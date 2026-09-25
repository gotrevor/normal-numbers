/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowGad

/-!
# The multi-gadget block law

Item 3 of the nested-layer route.  `AbelianWindowGad` gives two removal lemmas
(`blockGf_cons_of_high`, `blockGf_cons_of_low`) and the single-gadget closed form
(`blockGf_single`).  Here they are fed down a whole list of gadgets:

* `blockGf_eq_plain` — if the trace `I` fails to separate at least ONE pair of EVERY gadget in
  the list, the whole list drops out and `blockGf` is the plain binomial product;
* the interval geometry: an interval `Ico lo hi` separates the low pair `{p, p+1}` iff
  `lo = p + 1` or `hi = p + 1`, and the high pair iff `lo = p+a+1` or `hi = p+a+1`; a PREFIX
  (`lo = 0`) or a SUFFIX (`hi = q`) can therefore never separate both, so every gadget drops out
  and `BinomSeg` holds — the long-window half of the law, for ANY number of gadgets.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers.PowerBase

/-- Two gadgets occupy disjoint quadruples. -/
def GadDisj (g h : ℕ × ℕ) : Prop := ∀ u ∈ quadSet h.1 h.2, u ∉ quadSet g.1 g.2

theorem GadDisj.symm {g h : ℕ × ℕ} (hd : GadDisj g h) : GadDisj h g :=
  fun u hu hc => hd u hc hu

/-- A gadget list whose quadruples are pairwise disjoint.  Stated set-wise (not as
`List.Pairwise`) so that it is stable under permutation and under `erase`. -/
def GadSep (gs : List (ℕ × ℕ)) : Prop :=
  ∀ pa ∈ gs, ∀ qb ∈ gs, pa = qb ∨ GadDisj pa qb

/-- A gadget fits in a width-`q` block with a usable arm. -/
def GadOk (q : ℕ) (pa : ℕ × ℕ) : Prop := 2 ≤ pa.2 ∧ pa.1 + pa.2 + 1 < q

theorem blockGf_nil (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) :
    blockGf q (multiG q []) I = ∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2) := by
  rw [blockGf, ← gad_sum_plain q I]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  exact pow_card_filter q I hI (fun u => multiG q [] u d) (fun u => multiG_lt_two q [] u d)

theorem blockGf_congr_table (q : ℕ) (T T' : ℕ → ℕ → ℕ) (h : ∀ r d, T r d = T' r d)
    (I : Finset ℕ) : blockGf q T I = blockGf q T' I := by
  unfold blockGf
  simp only [h]

/-- Disjointness gives the head-versus-tail hypothesis the removal lemmas want. -/
theorem gadDisj_head {p a : ℕ} {gs : List (ℕ × ℕ)} (hsep : GadSep ((p, a) :: gs))
    (hnd : ((p, a) :: gs).Nodup) :
    ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a := by
  intro pa hpa
  have hne : (p, a) ≠ pa := fun hc => (List.nodup_cons.mp hnd).1 (hc ▸ hpa)
  rcases hsep (p, a) (by simp) pa (by simp [hpa]) with hc | hd
  · exact absurd hc hne
  · exact hd

/-- **The multi-gadget removal.**  If `I` leaves at least one pair of every gadget unseparated,
every gadget drops out. -/
theorem blockGf_eq_plain (q : ℕ) (gs : List (ℕ × ℕ)) (I : Finset ℕ) (hI : I ⊆ range q)
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup)
    (hsep : ∀ pa ∈ gs, (pa.1 ∈ I ↔ pa.1 + 1 ∈ I) ∨ (pa.1 + pa.2 ∈ I ↔ pa.1 + pa.2 + 1 ∈ I)) :
    blockGf q (multiG q gs) I = ∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2) := by
  induction gs with
  | nil => exact blockGf_nil q I hI
  | cons pa gs ih =>
      obtain ⟨p, a⟩ := pa
      obtain ⟨ha, hq⟩ := hok (p, a) (by simp)
      have hdisj := gadDisj_head hgs hnd
      have htail : blockGf q (multiG q gs) I
          = ∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2) :=
        ih (fun qa hqa => hok qa (by simp [hqa]))
          (fun x hx y hy => hgs x (by simp [hx]) y (by simp [hy]))
          (List.nodup_cons.mp hnd).2 (fun qa hqa => hsep qa (by simp [hqa]))
      rcases hsep (p, a) (by simp) with h | h
      · rw [blockGf_cons_of_low q p a gs ha hq hdisj I h, htail]
      · rw [blockGf_cons_of_high q p a gs ha hdisj I h, htail]

/-! ## The table does not see the order of the list -/

/-- On a position covered by a gadget of the list, the table is that gadget's bit. -/
theorem multiG_mem_eq (q : ℕ) (gs : List (ℕ × ℕ)) (hgs : GadSep gs) (hnd : gs.Nodup) (r d : ℕ)
    (pa : ℕ × ℕ) (hpa : pa ∈ gs) (hr : r ∈ quadSet pa.1 pa.2) :
    multiG q gs r d = gadBit q pa.1 pa.2 r d := by
  induction gs with
  | nil => exact absurd hpa (by simp)
  | cons g0 gs ih =>
      obtain ⟨p, a⟩ := g0
      rw [multiG_cons]
      by_cases hq : r ∈ quadSet p a
      · rw [if_pos hq]
        rcases List.mem_cons.mp hpa with rfl | hpa'
        · rfl
        · exact absurd hq (gadDisj_head hgs hnd pa hpa' r hr)
      · rw [if_neg hq]
        have hpa' : pa ∈ gs := by
          rcases List.mem_cons.mp hpa with rfl | h
          · exact absurd hr hq
          · exact h
        exact ih (fun x hx y hy => hgs x (by simp [hx]) y (by simp [hy]))
          (List.nodup_cons.mp hnd).2 hpa'

/-- Hence the table is invariant under permuting the list. -/
theorem multiG_perm (q : ℕ) {gs hs : List (ℕ × ℕ)} (hperm : gs.Perm hs) (hgs : GadSep gs)
    (hnd : gs.Nodup) (r d : ℕ) : multiG q gs r d = multiG q hs r d := by
  classical
  have hgs' : GadSep hs := fun x hx y hy =>
    hgs x (hperm.mem_iff.mpr hx) y (hperm.mem_iff.mpr hy)
  have hnd' : hs.Nodup := hperm.nodup_iff.mp hnd
  by_cases h : ∃ pa ∈ gs, r ∈ quadSet pa.1 pa.2
  · obtain ⟨pa, hpa, hr⟩ := h
    rw [multiG_mem_eq q gs hgs hnd r d pa hpa hr,
      multiG_mem_eq q hs hgs' hnd' r d pa (hperm.mem_iff.mp hpa) hr]
  · push_neg at h
    rw [multiG_of_notMem q gs r d h,
      multiG_of_notMem q hs r d (fun pa hpa => h pa (hperm.mem_iff.mpr hpa))]

/-! ## Reduction to the one surviving gadget -/

/-- Shorthand: the trace `I` leaves one of the gadget's pairs unseparated. -/
def Unsep (I : Finset ℕ) (pa : ℕ × ℕ) : Prop :=
  (pa.1 ∈ I ↔ pa.1 + 1 ∈ I) ∨ (pa.1 + pa.2 ∈ I ↔ pa.1 + pa.2 + 1 ∈ I)

/-- **All but one gadget removed.**  If `I` leaves a pair of every gadget EXCEPT `pa`
unseparated, the whole list collapses to the single gadget `pa`. -/
theorem blockGf_reduce (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) :
    ∀ (n : ℕ) (gs : List (ℕ × ℕ)), gs.length = n → ∀ pa : ℕ × ℕ, pa ∈ gs →
      (∀ qb ∈ gs, GadOk q qb) → GadSep gs → gs.Nodup →
      (∀ qb ∈ gs, qb ≠ pa → Unsep I qb) →
      blockGf q (multiG q gs) I = blockGf q (multiG q [pa]) I := by
  classical
  intro n
  induction n with
  | zero =>
      intro gs hlen pa hpa _ _ _ _
      rw [List.length_eq_zero_iff] at hlen
      exact absurd hpa (by rw [hlen]; simp)
  | succ n ih =>
      intro gs hlen pa hpa hok hgs hnd hsep
      have hpaer : pa ∉ gs.erase pa := fun hc => (List.Nodup.not_mem_erase (a := pa) hnd) hc
      by_cases hone : gs.erase pa = []
      · -- `gs` is exactly `[pa]`
        have hperm : gs.Perm (pa :: gs.erase pa) := List.perm_cons_erase hpa
        rw [hone] at hperm
        exact blockGf_congr_table q _ _ (fun r d => multiG_perm q hperm hgs hnd r d) I
      · obtain ⟨qb, hqbmem⟩ := List.exists_mem_of_ne_nil _ hone
        have hqbne : qb ≠ pa := fun hc => hpaer (hc ▸ hqbmem)
        have hqbgs : qb ∈ gs := List.mem_of_mem_erase hqbmem
        set gs' := gs.erase qb with hgs'def
        have hperm : gs.Perm (qb :: gs') := List.perm_cons_erase hqbgs
        have hpagsf : pa ∈ gs' := by
          have hne2 : pa ≠ qb := fun hc => hqbne hc.symm
          rw [hgs'def]
          exact (List.mem_erase_of_ne hne2).mpr hpa
        have hnd' : (qb :: gs').Nodup := hperm.nodup_iff.mp hnd
        have hgsc : GadSep (qb :: gs') := fun x hx y hy =>
          hgs x (hperm.mem_iff.mpr hx) y (hperm.mem_iff.mpr hy)
        have hokc : ∀ x ∈ (qb :: gs'), GadOk q x := fun x hx => hok x (hperm.mem_iff.mpr hx)
        have hstep : blockGf q (multiG q gs) I = blockGf q (multiG q (qb :: gs')) I :=
          blockGf_congr_table q _ _ (fun r d => multiG_perm q hperm hgs hnd r d) I
        obtain ⟨p0, a0⟩ := qb
        obtain ⟨ha0, hq0⟩ := hokc (p0, a0) (by simp)
        have hdisj := gadDisj_head hgsc hnd'
        have hrem : blockGf q (multiG q ((p0, a0) :: gs')) I = blockGf q (multiG q gs') I := by
          rcases hsep (p0, a0) hqbgs hqbne with h | h
          · exact blockGf_cons_of_low q p0 a0 gs' ha0 hq0 hdisj I h
          · exact blockGf_cons_of_high q p0 a0 gs' ha0 hdisj I h
        have hlen' : gs'.length = n := by
          have := List.length_erase_of_mem hqbgs
          rw [hgs'def, this, hlen]
          omega

        rw [hstep, hrem]
        exact ih gs' hlen' pa hpagsf (fun x hx => hokc x (by simp [hx]))
          (fun x hx y hy => hgsc x (by simp [hx]) y (by simp [hy]))
          (List.nodup_cons.mp hnd').2 (fun x hx hne => hsep x (hperm.mem_iff.mpr (by simp [hx])) hne)

/-! ## Interval geometry -/

/-- A **prefix** of the block never separates both pairs of a gadget. -/
theorem sep_of_prefix {hi p a : ℕ} (ha : 2 ≤ a) :
    (p ∈ Finset.Ico 0 hi ↔ p + 1 ∈ Finset.Ico 0 hi) ∨
      (p + a ∈ Finset.Ico 0 hi ↔ p + a + 1 ∈ Finset.Ico 0 hi) := by
  simp only [Finset.mem_Ico, Nat.zero_le, true_and]
  by_cases hp : p + 1 < hi
  · exact Or.inl ⟨fun _ => hp, fun _ => by omega⟩
  · exact Or.inr ⟨fun hc => by omega, fun hc => by omega⟩

/-- A **suffix** of the block never separates both pairs of a gadget. -/
theorem sep_of_suffix {lo q p a : ℕ} (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    (p ∈ Finset.Ico lo q ↔ p + 1 ∈ Finset.Ico lo q) ∨
      (p + a ∈ Finset.Ico lo q ↔ p + a + 1 ∈ Finset.Ico lo q) := by
  simp only [Finset.mem_Ico]
  by_cases hp : lo ≤ p
  · exact Or.inl ⟨fun _ => ⟨by omega, by omega⟩, fun _ => ⟨hp, by omega⟩⟩
  · by_cases hp2 : lo ≤ p + 1
    · exact Or.inr ⟨fun _ => ⟨by omega, by omega⟩, fun _ => ⟨by omega, by omega⟩⟩
    · exact Or.inl ⟨fun hc => by omega, fun hc => by omega⟩

/-! ## `BinomSeg` for any number of gadgets -/

/-- The plain product is the exact Binomial generating function, at any width. -/
theorem prod_base_eq (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) :
    (∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2))
      = C ((2 : ℝ) ^ q / 2 ^ I.card) * (1 + X) ^ I.card := by
  classical
  rw [← Finset.prod_sdiff hI]
  have h1 : ∏ i ∈ I, (if i ∈ I then (1 + X : ℝ[X]) else 2) = (1 + X) ^ I.card := by
    rw [Finset.prod_congr rfl (fun i hi => if_pos hi), Finset.prod_const]
  have h2 : ∏ i ∈ (range q) \ I, (if i ∈ I then (1 + X : ℝ[X]) else 2)
      = 2 ^ ((range q) \ I).card := by
    rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2), Finset.prod_const]
  have hcard : ((range q) \ I).card = q - I.card := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hI]
  have hle : I.card ≤ q := by simpa using Finset.card_le_card hI
  rw [h1, h2, hcard]
  have hsplit : ((2 : ℝ) ^ q / 2 ^ I.card) = 2 ^ (q - I.card) := by
    rw [div_eq_iff (by positivity), ← pow_add]
    congr 1
    omega
  rw [hsplit, Polynomial.C_pow, Polynomial.C_ofNat]

/-- **Every prefix and every suffix of a multi-gadget block law is Binomial** — so the
block-driven sequence is abelian at every window length `L ≥ q`, no matter how many gadgets the
block carries. -/
theorem multi_binomSeg (q : ℕ) (gs : List (ℕ × ℕ)) (hok : ∀ pa ∈ gs, GadOk q pa)
    (hgs : GadSep gs) (hnd : gs.Nodup) : BinomSeg (multiG q gs) q (2 ^ q) := by
  classical
  intro lo hi hhi hps
  have hI : Finset.Ico lo hi ⊆ range q := by
    intro i hi'
    rw [Finset.mem_Ico] at hi'
    exact Finset.mem_range.mpr (by omega)
  have hsep : ∀ pa ∈ gs, (pa.1 ∈ Finset.Ico lo hi ↔ pa.1 + 1 ∈ Finset.Ico lo hi) ∨
      (pa.1 + pa.2 ∈ Finset.Ico lo hi ↔ pa.1 + pa.2 + 1 ∈ Finset.Ico lo hi) := by
    intro pa hpa
    obtain ⟨ha, hq⟩ := hok pa hpa
    rcases hps with rfl | rfl
    · exact sep_of_prefix ha
    · exact sep_of_suffix ha hq
  have hcard : (Finset.Ico lo hi).card = hi - lo := by simp
  have := blockGf_eq_plain q gs (Finset.Ico lo hi) hI hok hgs hnd hsep
  rw [blockGf] at this
  rw [this, prod_base_eq q _ hI, hcard]
  norm_num

/-- An interval separates BOTH pairs of the gadget `(p, a)` only in the single position
`lo = p + 1`, `hi = p + a + 1`. -/
theorem sep_of_ne {lo hi p a : ℕ} (ha : 2 ≤ a) (hne : ¬ (lo = p + 1 ∧ hi = p + a + 1)) :
    Unsep (Finset.Ico lo hi) (p, a) := by
  have key : ((lo ≤ p ∧ p < hi) ↔ (lo ≤ p + 1 ∧ p + 1 < hi)) ∨
      ((lo ≤ p + a ∧ p + a < hi) ↔ (lo ≤ p + a + 1 ∧ p + a + 1 < hi)) := by omega
  simp only [Unsep, Finset.mem_Ico]
  exact key

/-- The trace of a length-`L ≠ a` window never separates both pairs of an `a`-armed gadget. -/
theorem segSet_unsep (q L r b p a : ℕ) (ha : 2 ≤ a) (hq : p + a + 1 < q) (hr : r < q)
    (hL : L ≠ a) : Unsep (segSet q L r b) (p, a) := by
  rw [segSet_eq_Ico_gen]
  refine sep_of_ne ha ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · simp only [Nat.zero_mul, Nat.sub_zero]
    omega
  · have hbq : q ≤ b * q := Nat.le_mul_of_pos_left q hb1
    omega

/-- **The multi-gadget sequence is abelian at every length that is not one of the arms.** -/
theorem multi_isAbelianAt_of_notMem (q : ℕ) (gs : List (ℕ × ℕ)) (hq0 : 0 < q)
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) (c : ℕ → ℕ)
    (hcB : ∀ m, c m < 2 ^ q) (hc : IsNormalSequence (2 ^ q) c) (L : ℕ)
    (hL : ∀ pa ∈ gs, L ≠ pa.2) : IsAbelianAt (blockSeq (multiG q gs) c q) L := by
  classical
  set S := q + L with hSdef
  have hB0 : 0 < 2 ^ q := by positivity
  have hSle : q + L ≤ q * S + 1 := by
    have : S ≤ q * S := Nat.le_mul_of_pos_left S hq0
    omega
  have hfib : ∀ r < q, ∀ t < L, (r + t) / q < S := by
    intro r hr t ht
    have := Nat.div_le_self (r + t) q
    omega
  refine (isAbelianAt_blockSeq_iff (multiG q gs) c hB0 hq0 hcB hc L S hSle).mpr (fun j _ => ?_)
  refine blockFreq_eq_binomial_of_seg (multiG q gs) hB0 hq0 S L hfib (fun r hr b hb => ?_) j
  have hsub : segSet q L r b ⊆ range q := fun u hu => (Finset.mem_filter.mp hu).1
  have hsep : ∀ pa ∈ gs, Unsep (segSet q L r b) pa := by
    intro pa hpa
    obtain ⟨p, a⟩ := pa
    obtain ⟨ha, hqa⟩ := hok (p, a) hpa
    exact segSet_unsep q L r b p a ha hqa hr (hL (p, a) hpa)
  have hcard : segLen q L r b = (segSet q L r b).card := segLen_eq_card q L r b hq0
  have hgf : ∀ d, segOnes (multiG q gs) q L r b d
      = ((segSet q L r b).filter (fun u => multiG q gs u d = 1)).card :=
    fun d => segOnes_eq_card (multiG q gs) hq0 L r b d
  have hplain := blockGf_eq_plain q gs (segSet q L r b) hsub hok hgs hnd hsep
  rw [blockGf] at hplain
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ range (2 ^ q)) => by rw [hgf d]), hplain,
    prod_base_eq q _ hsub, hcard]
  norm_num

/-! ## A single defective residue refutes abelianness -/

/-- If every residue but one gives the exact Binomial window law, and the exceptional residue's
window polynomial has the wrong constant term, the sequence is NOT abelian at `L`. -/
theorem not_isAbelianAt_of_one_defect (g : ℕ → ℕ → ℕ) (c : ℕ → ℕ) {B q : ℕ} (hB : 0 < B)
    (hq : 0 < q) (hcB : ∀ m, c m < B) (hc : IsNormalSequence B c) (L S r0 : ℕ)
    (hSle : q + L ≤ q * S + 1) (hr0 : r0 < q)
    (hother : ∀ r < q, r ≠ r0 → winGf g q B S L r = C ((B : ℝ) ^ S / 2 ^ L) * (1 + X) ^ L)
    (hdef : (winGf g q B S L r0).coeff 0 ≠ (B : ℝ) ^ S / 2 ^ L) :
    ¬ IsAbelianAt (blockSeq g c q) L := by
  classical
  intro h
  have hbf := (isAbelianAt_blockSeq_iff g c hB hq hcB hc L S hSle).mp h 0 (by omega)
  have hcoef : ∀ r ∈ (range q).erase r0,
      (winGf g q B S L r).coeff 0 = (B : ℝ) ^ S / 2 ^ L := by
    intro r hr
    rw [hother r (Finset.mem_range.mp (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr),
      Polynomial.coeff_C_mul, add_comm (1 : ℝ[X]) X, Polynomial.coeff_X_add_one_pow]
    simp
  rw [blockFreq_eq_coeff, ← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hr0),
    Finset.sum_congr rfl hcoef, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_range.mpr hr0), Finset.card_range, nsmul_eq_mul,
    Nat.choose_zero_right, Nat.cast_one] at hbf
  set v : ℝ := (B : ℝ) ^ S / 2 ^ L with hv
  set c0 : ℝ := (winGf g q B S L r0).coeff 0 with hc0
  have hBS : (0 : ℝ) < (B : ℝ) ^ S := by positivity
  have h2L : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    have : (1 : ℕ) ≤ q := hq
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast, div_eq_div_iff (by positivity) (by positivity)] at hbf
  have hBSv : (B : ℝ) ^ S = v * 2 ^ L := by rw [hv]; field_simp
  have hcancel : ((q : ℝ) - 1) * v + c0 = (q : ℝ) * v := by
    have h2 : (((q : ℝ) - 1) * v + c0) * 2 ^ L = ((q : ℝ) * v) * 2 ^ L := by
      rw [hbf, one_mul, hBSv]; ring
    exact mul_right_cancel₀ (ne_of_gt h2L) h2
  exact hdef (by linear_combination hcancel)

/-! ## The defect at an arm -/

theorem blockGf_empty (q : ℕ) (T : ℕ → ℕ → ℕ) : blockGf q T ∅ = C ((2 : ℝ) ^ q) := by
  rw [blockGf]
  simp only [Finset.filter_empty, Finset.card_empty, pow_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  rw [Polynomial.C_pow, Polynomial.C_ofNat]

theorem segSet_defect (q p a : ℕ) (hq : p + a + 1 < q) :
    segSet q a (p + 1) 0 = Finset.Ico (p + 1) (p + a + 1) := by
  rw [segSet_eq_Ico_gen]
  simp only [Nat.zero_mul, Nat.sub_zero]
  congr 1
  omega

theorem segSet_defect_pos (q p a b : ℕ) (hq : p + a + 1 < q) (hb : 1 ≤ b) :
    segSet q a (p + 1) b = ∅ := by
  rw [segSet_eq_Ico_gen]
  have hbq : q ≤ b * q := Nat.le_mul_of_pos_left q (by omega)
  have h1 : p + 1 - b * q = 0 := by omega
  have h2 : min q (p + 1 + a - b * q) = 0 := by omega
  rw [h1, h2]
  rfl

/-- The constant term of the plain product is a positive integer. -/
theorem prod_const_coeff_pos (s : Finset ℕ) (I : Finset ℕ) :
    0 < (∏ i ∈ s, (if i ∈ I then (1 + X : ℝ[X]) else 2)).coeff 0 := by
  classical
  have h : (∏ i ∈ s, (if i ∈ I then (1 + X : ℝ[X]) else 2)).coeff 0
      = ∏ i ∈ s, (if i ∈ I then (1 : ℝ) else 2) := by
    rw [← Polynomial.constantCoeff_apply, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hI : i ∈ I <;> simp [hI]
  rw [h]
  exact Finset.prod_pos (fun i _ => by by_cases hI : i ∈ I <;> simp [hI])

/-- **The defective segment.**  At the residue `p + 1` the first block's trace is exactly the
window that separates both pairs of the gadget `(p, a)`, and the gadget's correction pulls the
constant term strictly BELOW the Binomial value. -/
theorem blockGf_defect_coeff (q : ℕ) (gs : List (ℕ × ℕ)) (p a : ℕ) (hmem : (p, a) ∈ gs)
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup)
    (hinj : ∀ pa ∈ gs, ∀ qb ∈ gs, pa.2 = qb.2 → pa = qb) :
    (blockGf q (multiG q gs) (Finset.Ico (p + 1) (p + a + 1))).coeff 0
      < (2 : ℝ) ^ q / 2 ^ a := by
  classical
  obtain ⟨ha, hq⟩ := hok (p, a) hmem
  set I := Finset.Ico (p + 1) (p + a + 1) with hIdef
  have hI : I ⊆ range q := by
    intro i hi
    rw [hIdef, Finset.mem_Ico] at hi
    exact Finset.mem_range.mpr (by omega)
  have hsepoth : ∀ qb ∈ gs, qb ≠ (p, a) → Unsep I qb := by
    intro qb hqb hne
    obtain ⟨p', a'⟩ := qb
    obtain ⟨ha', hq'⟩ := hok (p', a') hqb
    refine sep_of_ne ha' ?_
    intro ⟨h1, h2⟩
    have : a' = a := by omega
    exact hne (hinj (p', a') hqb (p, a) hmem (by simpa using this))
  have hred := blockGf_reduce q I hI gs.length gs rfl (p, a) hmem hok hgs hnd hsepoth
  have hb : ∀ k : ℕ, ((1 + X : ℝ[X]) ^ k).coeff 0 = 1 := by
    intro k
    rw [add_comm, Polynomial.coeff_X_add_one_pow]
    simp
  rw [hred, blockGf_single q p a ha hq I hI, Polynomial.coeff_add, prod_base_eq q I hI,
    Polynomial.coeff_C_mul, hb]
  have hcard : I.card = a := by rw [hIdef, Nat.card_Ico]; omega
  have hp : p ∉ I := by rw [hIdef, Finset.mem_Ico]; omega
  have hp1 : p + 1 ∈ I := by rw [hIdef, Finset.mem_Ico]; omega
  have hpa : p + a ∈ I := by rw [hIdef, Finset.mem_Ico]; omega
  have hpa1 : p + a + 1 ∉ I := by rw [hIdef, Finset.mem_Ico]; omega
  rw [if_neg hp, if_pos hp1, if_pos hpa, if_neg hpa1, hcard]
  have hcorr : ((X : ℝ[X]) ^ (1 : ℕ) - X ^ (0 : ℕ)) * (X ^ (0 : ℕ) - X ^ (1 : ℕ))
      = -(X - 1) ^ 2 := by ring
  rw [hcorr, Polynomial.mul_coeff_zero]
  have hF := prod_const_coeff_pos ((range q) \ quadSet p a) I
  have hsq : ((-(X - 1) ^ 2 : ℝ[X])).coeff 0 = -1 := by
    simp only [neg_pow, Polynomial.coeff_neg]
    rw [show ((X - 1 : ℝ[X])) ^ 2 = X ^ 2 - 2 * X + 1 by ring]
    simp
  rw [hsq, mul_one]
  nlinarith [hF]

/-! ## Assembling the exact window set -/

theorem segGf_eq_blockGf (q : ℕ) (hq0 : 0 < q) (T : ℕ → ℕ → ℕ) (L r b : ℕ) :
    (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes T q L r b d)
      = blockGf q T (segSet q L r b) := by
  rw [blockGf]
  exact Finset.sum_congr rfl (fun d _ => by rw [segOnes_eq_card T hq0 L r b d])

/-- The segment law is exactly Binomial whenever every gadget is unseparated. -/
theorem multi_segGf_plain (q : ℕ) (gs : List (ℕ × ℕ)) (hq0 : 0 < q)
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) (L r b : ℕ)
    (hsep : ∀ pa ∈ gs, Unsep (segSet q L r b) pa) :
    (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q L r b d)
      = C (((2 ^ q : ℕ) : ℝ) / 2 ^ segLen q L r b) * (1 + X) ^ segLen q L r b := by
  have hsub : segSet q L r b ⊆ range q := fun u hu => (Finset.mem_filter.mp hu).1
  rw [segGf_eq_blockGf q hq0 _ L r b,
    blockGf_eq_plain q gs (segSet q L r b) hsub hok hgs hnd hsep,
    prod_base_eq q _ hsub, segLen_eq_card q L r b hq0]
  norm_num

/-- At a residue other than `p + 1`, a length-`a` window never separates any gadget, provided the
arms of the gadgets are distinct. -/
theorem segSet_unsep_other (q : ℕ) (gs : List (ℕ × ℕ)) (p a : ℕ) (hmem : (p, a) ∈ gs)
    (hok : ∀ pa ∈ gs, GadOk q pa)
    (hinj : ∀ pa ∈ gs, ∀ qb ∈ gs, pa.2 = qb.2 → pa = qb) (r b : ℕ) (hr : r < q)
    (hrne : r ≠ p + 1) : ∀ pa ∈ gs, Unsep (segSet q a r b) pa := by
  intro pa hpa
  obtain ⟨p', a'⟩ := pa
  obtain ⟨ha', hq'⟩ := hok (p', a') hpa
  rw [segSet_eq_Ico_gen]
  refine sep_of_ne ha' ?_
  intro ⟨h1, h2⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · simp only [Nat.zero_mul, Nat.sub_zero] at h1 h2
    have hA : a' = a := by omega
    have := hinj (p', a') hpa (p, a) hmem (by simpa using hA)
    have hp' : p' = p := by
      have := congrArg Prod.fst this; simpa using this
    omega
  · have hbq : q ≤ b * q := Nat.le_mul_of_pos_left q hb1
    omega

/-- **The multi-gadget sequence is NOT abelian at any of the gadget arms.** -/
theorem multi_not_isAbelianAt (q : ℕ) (gs : List (ℕ × ℕ)) (hq0 : 0 < q) (p a : ℕ)
    (hmem : (p, a) ∈ gs) (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup)
    (hinj : ∀ pa ∈ gs, ∀ qb ∈ gs, pa.2 = qb.2 → pa = qb) (c : ℕ → ℕ)
    (hcB : ∀ m, c m < 2 ^ q) (hc : IsNormalSequence (2 ^ q) c) :
    ¬ IsAbelianAt (blockSeq (multiG q gs) c q) a := by
  classical
  obtain ⟨ha, hq⟩ := hok (p, a) hmem
  simp only at ha hq
  have hB0 : 0 < 2 ^ q := by positivity
  set S := q + a with hSdef
  have hS1 : 1 ≤ S := by omega
  have hSle : q + a ≤ q * S + 1 := by
    have : S ≤ q * S := Nat.le_mul_of_pos_left S hq0
    omega
  have hfib : ∀ r < q, ∀ t < a, (r + t) / q < S := by
    intro r hr t ht
    have := Nat.div_le_self (r + t) q
    omega
  have hcast : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ) ^ q := by push_cast; ring
  refine not_isAbelianAt_of_one_defect (multiG q gs) c hB0 hq0 hcB hc a S (p + 1) hSle
    (by omega) ?_ ?_
  · intro r hr hrne
    exact winGf_eq_binomial (multiG q gs) hB0 S a r (hfib r hr) (fun b _ =>
      multi_segGf_plain q gs hq0 hok hgs hnd a r b
        (segSet_unsep_other q gs p a hmem hok hinj r b hr hrne))
  · have hprod : winGf (multiG q gs) q (2 ^ q) S a (p + 1)
        = blockGf q (multiG q gs) (Finset.Ico (p + 1) (p + a + 1)) * (C ((2 : ℝ) ^ q)) ^ (S - 1) := by
      rw [winGf_eq_prod (multiG q gs) hB0 q S a (p + 1) (hfib (p + 1) (by omega)),
        Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega : (0 : ℕ) < S)]
      congr 1
      · rw [segGf_eq_blockGf q hq0 _ a (p + 1) 0, segSet_defect q p a hq]
      · have hall : ∀ b ∈ Finset.Ico (0 + 1) S,
            (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q a (p + 1) b d)
              = C ((2 : ℝ) ^ q) := by
          intro b hb
          rw [Finset.mem_Ico] at hb
          rw [segGf_eq_blockGf q hq0 _ a (p + 1) b, segSet_defect_pos q p a b hq (by omega),
            blockGf_empty]
        rw [Finset.prod_congr rfl hall, Finset.prod_const, Nat.card_Ico]
    have hc0 := blockGf_defect_coeff q gs p a hmem hok hgs hnd hinj
    have hpow : ((C ((2 : ℝ) ^ q) : ℝ[X]) ^ (S - 1)).coeff 0 = ((2 : ℝ) ^ q) ^ (S - 1) := by
      rw [← map_pow, Polynomial.coeff_C_zero]
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ q) ^ (S - 1) := by positivity
    have hsplit : ((2 ^ q : ℕ) : ℝ) ^ S / 2 ^ a
        = ((2 : ℝ) ^ q / 2 ^ a) * ((2 : ℝ) ^ q) ^ (S - 1) := by
      have hp2 : ((2 : ℝ) ^ q) ^ S = (2 : ℝ) ^ q * ((2 : ℝ) ^ q) ^ (S - 1) := by
        rw [← pow_succ' ((2 : ℝ) ^ q) (S - 1), show S - 1 + 1 = S from by omega]
      rw [hcast, hp2]
      ring
    rw [hprod, Polynomial.mul_coeff_zero, hpow, hsplit]
    exact ne_of_lt (by nlinarith [hc0, hpos])

/-! ## The layout: one gadget per excluded length -/

/-- The total width consumed by a list of arms, each gadget getting `a + 2` positions. -/
def gadWidth : List ℕ → ℕ
  | [] => 0
  | a :: as => (a + 2) + gadWidth as

/-- Lay the gadgets out left to right starting at position `p`, arm `a` taking `a + 2`
positions. -/
def gadPlace : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | p, a :: as => (p, a) :: gadPlace (p + a + 2) as

@[simp] theorem gadPlace_nil (p : ℕ) : gadPlace p [] = [] := rfl

@[simp] theorem gadPlace_cons (p a : ℕ) (as : List ℕ) :
    gadPlace p (a :: as) = (p, a) :: gadPlace (p + a + 2) as := rfl

theorem gadPlace_mem_bound : ∀ (as : List ℕ) (p : ℕ) (x : ℕ × ℕ), x ∈ gadPlace p as →
    p ≤ x.1 ∧ x.1 + x.2 + 2 ≤ p + gadWidth as ∧ x.2 ∈ as := by
  intro as
  induction as with
  | nil => intro p x hx; exact absurd hx (by simp)
  | cons a as ih =>
      intro p x hx
      rw [gadPlace_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨le_refl _, ?_, by simp⟩
        show p + a + 2 ≤ p + ((a + 2) + gadWidth as)
        omega
      · obtain ⟨h1, h2, h3⟩ := ih (p + a + 2) x hx
        refine ⟨by omega, ?_, by simp [h3]⟩
        show x.1 + x.2 + 2 ≤ p + ((a + 2) + gadWidth as)
        omega

theorem gadPlace_arms : ∀ (as : List ℕ) (p : ℕ), (gadPlace p as).map Prod.snd = as := by
  intro as
  induction as with
  | nil => intro p; rfl
  | cons a as ih => intro p; rw [gadPlace_cons, List.map_cons, ih]

theorem gadPlace_nodup (as : List ℕ) (hnd : as.Nodup) (p : ℕ) : (gadPlace p as).Nodup := by
  have h := gadPlace_arms as p
  exact List.Nodup.of_map Prod.snd (by rw [h]; exact hnd)

theorem gadPlace_inj : ∀ (as : List ℕ), as.Nodup → ∀ (p : ℕ) (x : ℕ × ℕ), x ∈ gadPlace p as →
    ∀ y ∈ gadPlace p as, x.2 = y.2 → x = y := by
  intro as
  induction as with
  | nil => intro _ p x hx; exact absurd hx (by simp)
  | cons a as ih =>
      intro hnd p x hx y hy hxy
      rw [List.nodup_cons] at hnd
      rw [gadPlace_cons, List.mem_cons] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · exact absurd ((gadPlace_mem_bound as (p + a + 2) y hy).2.2) (by rw [← hxy]; exact hnd.1)
      · rcases hy with rfl | hy
        · exact absurd ((gadPlace_mem_bound as (p + a + 2) x hx).2.2) (by rw [hxy]; exact hnd.1)
        · exact ih hnd.2 (p + a + 2) x hx y hy hxy

theorem gadPlace_sep : ∀ (as : List ℕ) (p : ℕ), as.Nodup → GadSep (gadPlace p as) := by
  intro as
  induction as with
  | nil => intro p _ x hx; exact absurd hx (by simp)
  | cons a as ih =>
      intro p hnd
      rw [List.nodup_cons] at hnd
      have hdisj : ∀ y ∈ gadPlace (p + a + 2) as, GadDisj (p, a) y := by
        intro y hy u hu hc
        obtain ⟨h1, -, -⟩ := gadPlace_mem_bound as (p + a + 2) y hy
        rw [mem_quadSet] at hu hc
        rcases hu with rfl | rfl | rfl | rfl <;> rcases hc with h | h | h | h <;> omega
      intro x hx y hy
      rw [gadPlace_cons, List.mem_cons] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (hdisj y hy)
      · rcases hy with rfl | hy
        · exact Or.inr (hdisj x hx).symm
        · exact ih (p + a + 2) hnd.2 x hx y hy

theorem gadPlace_ok (as : List ℕ) (has : ∀ a ∈ as, 2 ≤ a) (p : ℕ) :
    ∀ x ∈ gadPlace p as, GadOk (p + gadWidth as + 1) x := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := gadPlace_mem_bound as p x hx
  exact ⟨has x.2 h3, by omega⟩

theorem blockSeq_multiG_lt_two (q : ℕ) (gs : List (ℕ × ℕ)) (c : ℕ → ℕ) (n : ℕ) :
    blockSeq (multiG q gs) c q n < 2 := multiG_lt_two q gs _ _

/-- **C4 for every finite complement.**  For every finite set `A` of lengths `≥ 2` there is a
binary sequence abelian at exactly the lengths outside `A`. -/
theorem c4_realizable_of_finite_compl (A : Finset ℕ) (hA : ∀ a ∈ A, 2 ≤ a) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∉ A) := by
  classical
  set as := A.sort (· ≤ ·) with hasdef
  have hmem : ∀ a, a ∈ as ↔ a ∈ A := fun a => by rw [hasdef, Finset.mem_sort]
  have hnd : as.Nodup := A.sort_nodup _
  have has : ∀ a ∈ as, 2 ≤ a := fun a ha => hA a ((hmem a).mp ha)
  set q := 0 + gadWidth as + 1 with hqdef
  set gs := gadPlace 0 as with hgsdef
  have hq0 : 0 < q := by omega
  have hok : ∀ pa ∈ gs, GadOk q pa := gadPlace_ok as has 0
  have hgs : GadSep gs := gadPlace_sep as 0 hnd
  have hndgs : gs.Nodup := gadPlace_nodup as hnd 0
  have hinj : ∀ pa ∈ gs, ∀ qb ∈ gs, pa.2 = qb.2 → pa = qb := gadPlace_inj as hnd 0
  set c := digitOf (2 ^ q) (Int.fract NormalNumbers.G4.Sched.fullRealW) with hcdef
  have hb2 : 2 ≤ 2 ^ q := by
    have : 2 ^ 1 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hcB : ∀ m, c m < 2 ^ q := fun m => digitOf_lt (2 ^ q) hb2 _ m
  have hc : IsNormalSequence (2 ^ q) c := by
    have h := NormalNumbers.G4.Sched.isNormal_two_pow_fullRealW q hq0
    rw [IsNormal] at h
    exact h
  refine ⟨blockSeq (multiG q gs) c q, blockSeq_multiG_lt_two q gs c, fun L hL => ?_⟩
  constructor
  · intro h hLA
    -- `L ∈ A` means `L` is one of the arms, so there is a gadget with arm `L`
    have hLas : L ∈ as := (hmem L).mpr hLA
    have : ∃ p, (p, L) ∈ gs := by
      have hmap : gs.map Prod.snd = as := gadPlace_arms as 0
      rw [← hmap, List.mem_map] at hLas
      obtain ⟨x, hx, hx2⟩ := hLas
      exact ⟨x.1, by rw [← hx2]; exact hx⟩
    obtain ⟨p, hp⟩ := this
    exact multi_not_isAbelianAt q gs hq0 p L hp hok hgs hndgs hinj c hcB hc h
  · intro hLA
    refine multi_isAbelianAt_of_notMem q gs hq0 hok hgs hndgs c hcB hc L (fun pa hpa => ?_)
    intro hc2
    exact hLA ((hmem pa.2).mp (gadPlace_mem_bound as 0 pa hpa).2.2 |> fun h => hc2 ▸ h)

end NormalNumbers.Abelian
