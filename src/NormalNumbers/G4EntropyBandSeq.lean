/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandFreq
import NormalNumbers.G4EntropyBlockWord

/-!
# Entropy expedition — the band sequence, and its strictly increasing position map

The band-`i` window family at the good atom is certified (`abs_posAvg_bandLaw_le`), pairwise
disjoint with a full window's margin (`window_gap_same_atom`), and confined to band `i`
(`pos_lt_bandTop`, `bandLo_le_of_mem_bandS`).  Reading the bands in order therefore produces a
**genuinely increasing** sequence of digit positions, block by block, with no repetition: this
module builds that map and proves it strictly monotone.

* `bnth i a` — the `a`-th band-`i` sample time, in increasing order.
* `bpos i a` — the digit position at which that window opens; `bpos_gap` separates consecutive
  windows by a full window length.
* `bL i = |bandS i|·m_i`, `bT i = Σ_{j<i} bL j` — the block lengths and the cutoffs.
* `bandPos j` — the position of the `j`-th digit read; `bandPos_strictMono`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### Enumerating one band -/

lemma card_bandS_pos (i : ℕ) : 0 < (bandS i).card := Finset.card_pos.2 (bandS_nonempty i)

/-- The `a`-th band-`i` sample time, in increasing order (cyclically extended). -/
noncomputable def bnth (i a : ℕ) : ℕ :=
  (bandS i).orderEmbOfFin rfl ⟨a % (bandS i).card, Nat.mod_lt _ (card_bandS_pos i)⟩

lemma bnth_mem (i a : ℕ) : bnth i a ∈ bandS i := by
  rw [bnth]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma bnth_mem_PK (i a : ℕ) : bnth i a ∈ PK i := bandS_subset i (bnth_mem i a)

lemma bnth_lt_bnth {i a b : ℕ} (hab : a < b) (hb : b < (bandS i).card) :
    bnth i a < bnth i b := by
  have ha : a < (bandS i).card := lt_trans hab hb
  rw [bnth, bnth]
  refine (Finset.orderEmbOfFin (bandS i) rfl).strictMono ?_
  refine Fin.mk_lt_mk.2 ?_
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

/-- The digit position at which the `a`-th band-`i` window opens. -/
noncomputable def bpos (i a : ℕ) : ℕ := 2 * kIdx (gridAt i) (bnth i a) (goodAtom i)

/-- **Consecutive windows are a full window apart.** -/
lemma bpos_gap {i a b : ℕ} (hab : a < b) (hb : b < (bandS i).card) :
    bpos i a + kk i ≤ bpos i b :=
  window_gap_same_atom i (goodAtom i) (bnth_mem_PK i a) (bnth_mem_PK i b)
    (bnth_lt_bnth hab hb)

lemma bpos_add_lt_bandTop (i a : ℕ) {p : ℕ} (hp : p < kk i) : bpos i a + p < bandTop i :=
  pos_lt_bandTop i (bnth_mem_PK i a) (goodAtom i) hp

lemma bandLo_le_bpos (i a : ℕ) : bandLo i ≤ bpos i a :=
  bandLo_le_of_mem_bandS i (bnth_mem i a)

/-! ### The block lengths and the cutoffs -/

/-- The number of digits band `i` contributes. -/
noncomputable def bL (i : ℕ) : ℕ := (bandS i).card * kk i

lemma kk_pos' (i : ℕ) : 0 < kk i := by unfold kk; omega

lemma bL_pos (i : ℕ) : 0 < bL i := Nat.mul_pos (card_bandS_pos i) (kk_pos' i)

/-- The cutoff after the first `i` bands. -/
noncomputable def bT : ℕ → ℕ
  | 0 => 0
  | (i + 1) => bT i + bL i

lemma bT_lt_succ (i : ℕ) : bT i < bT (i + 1) := by
  have := bL_pos i
  show bT i < bT i + bL i
  omega

lemma bT_mono : Monotone bT := monotone_nat_of_le_succ fun i => (bT_lt_succ i).le

lemma self_le_bT (i : ℕ) : i ≤ bT i := by
  induction i with
  | zero => simp [bT]
  | succ i ih => have := bT_lt_succ i; omega

/-- The band a read index belongs to. -/
noncomputable def bgrp (j : ℕ) : ℕ := Nat.findGreatest (fun m => bT m ≤ j) j

lemma bgrp_eq {i j : ℕ} (h1 : bT i ≤ j) (h2 : j < bT (i + 1)) : bgrp j = i := by
  classical
  have hij : i ≤ j := le_trans (self_le_bT i) h1
  have hle : i ≤ bgrp j := Nat.le_findGreatest hij h1
  by_contra hne
  have hlt : i < bgrp j := lt_of_le_of_ne hle (Ne.symm hne)
  have hspec : bT (bgrp j) ≤ j :=
    Nat.findGreatest_spec (P := fun m => bT m ≤ j) hij h1
  have : bT (i + 1) ≤ bT (bgrp j) := bT_mono (by omega)
  omega

lemma bT_bgrp_le (j : ℕ) : bT (bgrp j) ≤ j := by
  classical
  exact Nat.findGreatest_spec (P := fun m => bT m ≤ j) (Nat.zero_le j) (by simp [bT])

lemma lt_bT_bgrp_succ (j : ℕ) : j < bT (bgrp j + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have h1 : bgrp j + 1 ≤ j := le_trans (self_le_bT (bgrp j + 1)) hcon
  have h2 : bgrp j + 1 ≤ bgrp j := Nat.le_findGreatest h1 hcon
  omega

/-! ### The position map -/

/-- **The position of the `j`-th digit read.**  Bands in order; inside a band, windows in order;
inside a window, the `m_i` consecutive digit positions. -/
noncomputable def bandPos (j : ℕ) : ℕ :=
  bpos (bgrp j) ((j - bT (bgrp j)) / kk (bgrp j)) + (j - bT (bgrp j)) % kk (bgrp j)

lemma bandPos_eq {i j : ℕ} (h1 : bT i ≤ j) (h2 : j < bT (i + 1)) :
    bandPos j = bpos i ((j - bT i) / kk i) + (j - bT i) % kk i := by
  rw [bandPos, bgrp_eq h1 h2]

/-- **The position map is strictly increasing**: a genuine subsequence of `G₄`'s digits. -/
theorem bandPos_strictMono : StrictMono bandPos := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  set i := bgrp j with hi
  have h1 : bT i ≤ j := bT_bgrp_le j
  have h2 : j < bT (i + 1) := lt_bT_bgrp_succ j
  have hbT : bT (i + 1) = bT i + bL i := rfl
  set r : ℕ := j - bT i with hr
  have hrlt : r < bL i := by omega
  have hkk : 0 < kk i := kk_pos' i
  set a : ℕ := r / kk i with ha
  set p : ℕ := r % kk i with hp
  have hpk : p < kk i := Nat.mod_lt _ hkk
  have hra : r = a * kk i + p := (Nat.div_add_mod' r (kk i)).symm
  have hacard : a < (bandS i).card := by
    by_contra hcon
    push_neg at hcon
    have : (bandS i).card * kk i ≤ a * kk i := Nat.mul_le_mul_right _ hcon
    rw [bL] at hrlt
    omega
  have hj : bandPos j = bpos i a + p := bandPos_eq h1 h2
  rcases Nat.lt_or_ge (p + 1) (kk i) with hcase | hcase
  · -- inside the same window
    have hr1 : j + 1 - bT i = r + 1 := by omega
    have hlt1 : j + 1 < bT (i + 1) := by
      rw [hbT, bL]
      have : (a + 1) * kk i ≤ (bandS i).card * kk i := Nat.mul_le_mul_right _ hacard
      have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
      omega
    have hdiv : (r + 1) / kk i = a := by
      rw [hra]
      have : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [this, Nat.mul_add_div hkk, Nat.div_eq_of_lt hcase]
      omega
    have hmod : (r + 1) % kk i = p + 1 := by
      rw [hra]
      have : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hcase]
    have := bandPos_eq (i := i) (j := j + 1) (by omega) hlt1
    rw [this, hr1, hdiv, hmod, hj]
    omega
  · have hpk1 : p + 1 = kk i := by omega
    rcases Nat.lt_or_ge (a + 1) (bandS i).card with hcase2 | hcase2
    · -- next window, same band
      have hr1 : j + 1 - bT i = r + 1 := by omega
      have hreq : r + 1 = (a + 1) * kk i := by
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hlt1 : j + 1 < bT (i + 1) := by
        rw [hbT, bL]
        have : (a + 1) * kk i < (bandS i).card * kk i :=
          Nat.mul_lt_mul_of_lt_of_le hcase2 (le_refl _) hkk
        omega
      have hdiv : (r + 1) / kk i = a + 1 := by
        rw [hreq, Nat.mul_div_cancel _ hkk]
      have hmod : (r + 1) % kk i = 0 := by
        rw [hreq, Nat.mul_mod_left]
      have heq := bandPos_eq (i := i) (j := j + 1) (by omega) hlt1
      rw [heq, hr1, hdiv, hmod, hj]
      have hgap := bpos_gap (i := i) (a := a) (b := a + 1) (by omega) hcase2
      omega
    · -- next band
      have hacard' : a + 1 = (bandS i).card := by omega
      have hreq : r + 1 = bL i := by
        rw [bL, ← hacard']
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hj1 : j + 1 = bT (i + 1) := by rw [hbT]; omega
      have hlt2 : bT (i + 1) ≤ j + 1 := by omega
      have hlt3 : j + 1 < bT (i + 1 + 1) := by
        have := bT_lt_succ (i + 1)
        omega
      have heq := bandPos_eq (i := i + 1) (j := j + 1) hlt2 hlt3
      have hzero : j + 1 - bT (i + 1) = 0 := by omega
      rw [heq, hzero, Nat.zero_div, Nat.zero_mod, hj]
      have hup : bandLo (i + 1) ≤ bpos (i + 1) 0 := bandLo_le_bpos (i + 1) 0
      have hlo : bandLo (i + 1) = bandTop i := rfl
      have hdown : bpos i a + p < bandTop i := bpos_add_lt_bandTop i a hpk
      omega

/-! ### The digits read, and the window dictionary -/

/-- The digit sequence read along `bandPos`. -/
noncomputable def bandDig (x : ℝ) (j : ℕ) : ℕ := digitOf 2 (Int.fract x) (bandPos j)

lemma bandDig_lt (x : ℝ) (j : ℕ) : bandDig x j < 2 := Nat.mod_lt _ (by omega)

/-- Inside band `i`, the `a`-th window occupies the read indices
`bT i + a·m_i + q`, `q < m_i`, at digit positions `bpos i a + q`. -/
lemma bandPos_window (i a q : ℕ) (ha : a < (bandS i).card) (hq : q < kk i) :
    bandPos (bT i + a * kk i + q) = bpos i a + q := by
  have hkk : 0 < kk i := kk_pos' i
  have hlt : a * kk i + q < bL i := by
    rw [bL]
    have : (a + 1) * kk i ≤ (bandS i).card * kk i := Nat.mul_le_mul_right _ ha
    have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
    omega
  have h1 : bT i ≤ bT i + a * kk i + q := by omega
  have h2 : bT i + a * kk i + q < bT (i + 1) := by
    show bT i + a * kk i + q < bT i + bL i
    omega
  have hsub : bT i + a * kk i + q - bT i = a * kk i + q := by omega
  have hdiv : (a * kk i + q) / kk i = a := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_div hkk, Nat.div_eq_of_lt hq]
    omega
  have hmod : (a * kk i + q) % kk i = q := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  rw [bandPos_eq h1 h2, hsub, hdiv, hmod]

/-- **The dictionary**: a window of `v` fitting inside one band window is exactly an occurrence
of `v` in `x` at the corresponding digit position. -/
lemma matchesAt_bandDig_iff (x : ℝ) (i a q : ℕ) (v : List ℕ) (ha : a < (bandS i).card)
    (hq : q + v.length ≤ kk i) :
    MatchesAt (bandDig x) v (bT i + a * kk i + q) ↔ OccursAt 2 x v (bpos i a + q) := by
  have hkey : ∀ t < v.length,
      bandDig x (bT i + a * kk i + q + t) = digitOf 2 (Int.fract x) (bpos i a + q + t) := by
    intro t ht
    have hqt : q + t < kk i := by omega
    have hrw : bT i + a * kk i + q + t = bT i + a * kk i + (q + t) := by ring
    rw [bandDig, hrw, bandPos_window i a (q + t) ha hqt]
    ring_nf
  constructor
  · intro h t ht
    have h' := h t ht
    rw [hkey t ht] at h'
    rw [h']
    exact (List.getD_eq_getElem v 0 ht)
  · intro h t ht
    show bandDig x (bT i + a * kk i + q + t) = _
    rw [hkey t ht, h t ht]
    exact (List.getD_eq_getElem v 0 ht).symm

/-- Summing over the band's enumeration is summing over the band. -/
lemma sum_range_bnth {β : Type*} [AddCommMonoid β] (i : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (bandS i).card, g (bnth i a) = ∑ n ∈ bandS i, g n := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun a => g (bnth i a))]
  have hstep : ∀ a : Fin (bandS i).card,
      g (bnth i (a : ℕ)) = g ((bandS i).orderEmbOfFin rfl a) := by
    intro a
    have hfin : (⟨(a : ℕ) % (bandS i).card, Nat.mod_lt _ (card_bandS_pos i)⟩ :
        Fin (bandS i).card) = a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    rw [bnth, hfin]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  rw [← Finset.sum_attach (bandS i) g]
  refine Fintype.sum_bijective (fun a : Fin (bandS i).card =>
    (⟨(bandS i).orderEmbOfFin rfl a, Finset.orderEmbOfFin_mem _ _ _⟩ : (bandS i : Finset ℕ)))
    ?_ _ _ (fun a => rfl)
  constructor
  · intro a b hab
    have : ((bandS i).orderEmbOfFin rfl a : ℕ) = (bandS i).orderEmbOfFin rfl b := by
      exact congrArg Subtype.val hab
    exact (bandS i).orderEmbOfFin rfl |>.injective (by exact_mod_cast this)
  · rintro ⟨n, hn⟩
    have hrange : n ∈ Set.range ((bandS i).orderEmbOfFin (rfl : (bandS i).card = _)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hn
    obtain ⟨a, ha⟩ := hrange
    exact ⟨a, Subtype.ext ha⟩

/-! ### The per-band count -/

open Classical in
/-- The number of fitting in-window occurrences of `v` in band `i`. -/
noncomputable def bandGood (i : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ a ∈ Finset.range (bandS i).card,
    ((Finset.range (kk i - v.length + 1)).filter
      (fun q => OccursAt 2 x v (bpos i a + q))).card

open Classical in
/-- Translating a block of read indices to `[0, bL i)`. -/
lemma card_Ico_shift (Q : ℕ → Prop) [DecidablePred Q] (b len : ℕ) :
    ((Finset.Ico b (b + len)).filter Q).card
      = ((Finset.range len).filter (fun r => Q (b + r))).card := by
  classical
  refine Finset.card_nbij (fun p => p - b) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : b + (p - b) = p := by omega
    rw [this]
    exact hp.2
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hp hq
    simp only at hpq
    omega
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hr
    refine ⟨b + r, ?_, by simp⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico]
    exact ⟨by omega, hr.2⟩

open Classical in
/-- **The band's contribution to the read count**, up to one word length per window. -/
theorem band_winCount_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) :
    bandGood i x v
        ≤ ((Finset.Ico (bT i) (bT (i + 1))).filter (MatchesAt (bandDig x) v)).card ∧
      ((Finset.Ico (bT i) (bT (i + 1))).filter (MatchesAt (bandDig x) v)).card
        ≤ bandGood i x v + (bandS i).card * v.length := by
  classical
  have hbT : bT (i + 1) = bT i + bL i := rfl
  have hsplit : ((Finset.Ico (bT i) (bT (i + 1))).filter (MatchesAt (bandDig x) v)).card
      = ∑ a ∈ Finset.range (bandS i).card,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (bandDig x) v (bT i + (a * kk i + q)))).card := by
    rw [hbT, card_Ico_shift _ (bT i) (bL i), bL, card_filter_range_mul]
  rw [hsplit]
  have hper : ∀ a ∈ Finset.range (bandS i).card,
      ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (bpos i a + q))).card
        ≤ ((Finset.range (kk i)).filter
          (fun q => MatchesAt (bandDig x) v (bT i + (a * kk i + q)))).card ∧
      ((Finset.range (kk i)).filter
          (fun q => MatchesAt (bandDig x) v (bT i + (a * kk i + q)))).card
        ≤ ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (bpos i a + q))).card + v.length := by
    intro a ha
    have ha' : a < (bandS i).card := Finset.mem_range.1 ha
    have hcongr : ((Finset.range (kk i - v.length + 1)).filter
        (fun q => MatchesAt (bandDig x) v (bT i + (a * kk i + q)))).card
        = ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (bpos i a + q))).card := by
      congr 1
      refine Finset.filter_congr fun q hq => ?_
      have hqfit : q + v.length ≤ kk i := by
        have := Finset.mem_range.1 hq
        omega
      have hassoc : bT i + (a * kk i + q) = bT i + a * kk i + q := by ring
      rw [hassoc]
      simpa using matchesAt_bandDig_iff x i a q v ha' hqfit
    have h := card_filter_fit
      (fun q => MatchesAt (bandDig x) v (bT i + (a * kk i + q))) (m := kk i)
      (ℓ := v.length) hv hvm
    rw [hcongr] at h
    exact h
  constructor
  · exact Finset.sum_le_sum fun a ha => (hper a ha).1
  · calc ∑ a ∈ Finset.range (bandS i).card,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (bandDig x) v (bT i + (a * kk i + q)))).card
        ≤ ∑ a ∈ Finset.range (bandS i).card,
            (((Finset.range (kk i - v.length + 1)).filter
              (fun q => OccursAt 2 x v (bpos i a + q))).card + v.length) :=
          Finset.sum_le_sum fun a ha => (hper a ha).2
      _ = bandGood i x v + (bandS i).card * v.length := by
          rw [Finset.sum_add_distrib, bandGood]
          simp [mul_comm]

/-! ### Telescoping, and the domination of the last band -/

open Classical in
lemma winCount_bT (x : ℝ) (v : List ℕ) (n : ℕ) :
    winCount (bandDig x) v (bT n)
      = ∑ j ∈ Finset.range n,
          ((Finset.Ico (bT j) (bT (j + 1))).filter (MatchesAt (bandDig x) v)).card := by
  classical
  induction n with
  | zero => simp [bT, winCount_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih,
        winCount_split (bandDig x) v (bT_mono (Nat.le_succ n))]

set_option maxHeartbeats 1000000 in
/-- **Each band dwarfs the previous one.**  `granule_exceeds_previous_scale` applied to the
band, which keeps at least half the sample. -/
theorem bL_step (j : ℕ) : 20000 * (bL j : ℝ) ≤ (bL (j + 1) : ℝ) := by
  have hA : (1 : ℝ) ≤ (Fintype.card (gridAt j).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt j).Atom := Fintype.card_pos
    exact_mod_cast this
  have hPj : (0 : ℝ) ≤ ((PK j).card : ℝ) := Nat.cast_nonneg _
  have hkkj : (0 : ℝ) ≤ (kk j : ℝ) := Nat.cast_nonneg _
  have hband : ((bandS j).card : ℝ) ≤ ((PK j).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (bandS_subset j)
  -- `bL j ≤ |Atom_j|·|P_j|·m_j`
  have hb : ((bandS j).card : ℝ)
      ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PK j).card : ℝ) := by
    nlinarith [hband, hA, hPj]
  have h1 : (bL j : ℝ) ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PK j).card : ℝ) * (kk j : ℝ) := by
    have hbl : (bL j : ℝ) = ((bandS j).card : ℝ) * (kk j : ℝ) := by
      show ((((bandS j).card * kk j : ℕ)) : ℝ) = _
      push_cast; ring
    rw [hbl]
    exact mul_le_mul_of_nonneg_right hb hkkj
  have h2 := granule_exceeds_previous_scale j
  have h3 : ((PK (j + 1)).card : ℝ) ≤ 2 * ((bandS (j + 1)).card : ℝ) := card_bandS_ge' (j + 1)
  have hkk1 : (40000 : ℝ) ≤ (kk (j + 1) : ℝ) := by
    have : (40000 : ℕ) ≤ kk (j + 1) := by unfold kk; omega
    exact_mod_cast this
  have hS1 : (0 : ℝ) ≤ ((bandS (j + 1)).card : ℝ) := Nat.cast_nonneg _
  have h4 : (bL (j + 1) : ℝ) = ((bandS (j + 1)).card : ℝ) * (kk (j + 1) : ℝ) := by
    show ((((bandS (j + 1)).card * kk (j + 1) : ℕ)) : ℝ) = _
    push_cast; ring
  rw [h4]
  nlinarith [h1, h2, h3, hkk1, hS1]

/-- Everything before band `i` is at most a `10⁻⁴` fraction of band `i`. -/
theorem bT_le_bL (i : ℕ) : 10000 * (bT i : ℝ) ≤ (bL i : ℝ) := by
  induction i with
  | zero =>
      have h0 : ((bT 0 : ℕ) : ℝ) = 0 := by norm_num [bT]
      rw [h0]
      have : (0 : ℝ) ≤ (bL 0 : ℝ) := Nat.cast_nonneg _
      linarith
  | succ i ih =>
      have hstep := bL_step i
      have hbT : (bT (i + 1) : ℝ) = (bT i : ℝ) + (bL i : ℝ) := by
        show ((bT i + bL i : ℕ) : ℝ) = _
        push_cast; ring
      rw [hbT]
      nlinarith [ih, hstep]

lemma bL_pos_real (i : ℕ) : (0 : ℝ) < (bL i : ℝ) := by
  have := bL_pos i
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
/-- The sharper step: the growth factor is the next window length, not a constant. -/
theorem bL_step' (j : ℕ) : (kk (j + 1) : ℝ) * (bL j : ℝ) ≤ 2 * (bL (j + 1) : ℝ) := by
  have hA : (1 : ℝ) ≤ (Fintype.card (gridAt j).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt j).Atom := Fintype.card_pos
    exact_mod_cast this
  have hPj : (0 : ℝ) ≤ ((PK j).card : ℝ) := Nat.cast_nonneg _
  have hkkj : (0 : ℝ) ≤ (kk j : ℝ) := Nat.cast_nonneg _
  have hband : ((bandS j).card : ℝ) ≤ ((PK j).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (bandS_subset j)
  have hb : ((bandS j).card : ℝ)
      ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PK j).card : ℝ) := by
    nlinarith [hband, hA, hPj]
  have hbl : (bL j : ℝ) = ((bandS j).card : ℝ) * (kk j : ℝ) := by
    show ((((bandS j).card * kk j : ℕ)) : ℝ) = _
    push_cast; ring
  have h1 : (bL j : ℝ) ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PK j).card : ℝ) * (kk j : ℝ) := by
    rw [hbl]
    exact mul_le_mul_of_nonneg_right hb hkkj
  have h2 := granule_exceeds_previous_scale j
  have h3 : ((PK (j + 1)).card : ℝ) ≤ 2 * ((bandS (j + 1)).card : ℝ) := card_bandS_ge' (j + 1)
  have hkk1 : (0 : ℝ) ≤ (kk (j + 1) : ℝ) := Nat.cast_nonneg _
  have h4 : (bL (j + 1) : ℝ) = ((bandS (j + 1)).card : ℝ) * (kk (j + 1) : ℝ) := by
    show ((((bandS (j + 1)).card * kk (j + 1) : ℕ)) : ℝ) = _
    push_cast; ring
  rw [h4]
  nlinarith [h1, h2, h3, hkk1]

lemma kk_ge_real (i : ℕ) : (40000 : ℝ) ≤ (kk i : ℝ) := by
  have : (40000 : ℕ) ≤ kk i := by unfold kk; omega
  exact_mod_cast this

/-- **The history is a `4/m_i` fraction of band `i`.**  The bound improves with the scale, which
is what makes the seam corrections vanish. -/
theorem bT_kk_le (i : ℕ) : (bT i : ℝ) * (kk i : ℝ) ≤ 4 * (bL i : ℝ) := by
  induction i with
  | zero =>
      have h0 : ((bT 0 : ℕ) : ℝ) = 0 := by norm_num [bT]
      rw [h0]
      have : (0 : ℝ) ≤ (bL 0 : ℝ) := Nat.cast_nonneg _
      linarith
  | succ i ih =>
      have hstep := bL_step' i
      have hbT : (bT (i + 1) : ℝ) = (bT i : ℝ) + (bL i : ℝ) := by
        show ((bT i + bL i : ℕ) : ℝ) = _
        push_cast; ring
      have hkki := kk_ge_real i
      have hkki1 := kk_ge_real (i + 1)
      have hTnn : (0 : ℝ) ≤ (bT i : ℝ) := Nat.cast_nonneg _
      have hLnn : (0 : ℝ) ≤ (bL i : ℝ) := Nat.cast_nonneg _
      -- `bT i · m_{i+1} ≤ (4 bL i/m_i)·m_{i+1} ≤ 8 bL_{i+1}/m_i`
      have hTm : (bT i : ℝ) * (kk (i + 1) : ℝ) * (kk i : ℝ)
          ≤ 8 * (bL (i + 1) : ℝ) := by
        have h1 : (bT i : ℝ) * (kk (i + 1) : ℝ) * (kk i : ℝ)
            = ((bT i : ℝ) * (kk i : ℝ)) * (kk (i + 1) : ℝ) := by ring
        rw [h1]
        calc ((bT i : ℝ) * (kk i : ℝ)) * (kk (i + 1) : ℝ)
            ≤ (4 * (bL i : ℝ)) * (kk (i + 1) : ℝ) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = 4 * ((kk (i + 1) : ℝ) * (bL i : ℝ)) := by ring
          _ ≤ 4 * (2 * (bL (i + 1) : ℝ)) := by linarith
          _ = 8 * (bL (i + 1) : ℝ) := by ring
      rw [hbT]
      have hLnn1 : (0 : ℝ) ≤ (bL (i + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith [hTm, hstep, hkki, hkki1, hLnn1]

open Classical in
/-- `bandGood` re-summed over the band's sample times: the numerator of
`tendsto_band_occursCount`. -/
theorem bandGood_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    bandGood i x v
      = ∑ q ∈ Finset.range (kk i - v.length + 1),
          ((bandS i).filter fun n =>
            OccursAt 2 x v (2 * kIdx (gridAt i) n (goodAtom i) + q)).card := by
  classical
  unfold bandGood
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact sum_range_bnth i
    (fun n => if OccursAt 2 x v (2 * kIdx (gridAt i) n (goodAtom i) + q) then 1 else 0)

/-! ### The read count at the band cutoffs -/

open Classical in
/-- The read count at cutoff `bT (i+1)` is band `i`'s in-window count, up to the history and one
word length per window. -/
theorem winCount_bT_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) :
    bandGood i x v ≤ winCount (bandDig x) v (bT (i + 1)) ∧
      winCount (bandDig x) v (bT (i + 1))
        ≤ bandGood i x v + bT i + (bandS i).card * v.length := by
  classical
  have hsplit := winCount_split (bandDig x) v (bT_mono (Nat.le_succ i))
  simp only [Nat.succ_eq_add_one] at hsplit
  obtain ⟨h1, h2⟩ := band_winCount_bounds x i v hv hvm
  have hhist : winCount (bandDig x) v (bT i) ≤ bT i := winCount_le _ _ _
  generalize hc : (bandS i).card * v.length = c at h2 ⊢
  rw [hsplit]
  omega

/-! ### The frequency limit along the band cutoffs -/

lemma tendsto_const_div_kk (c : ℝ) :
    Tendsto (fun i => c / (kk i : ℝ)) atTop (nhds 0) :=
  tendsto_kk_atTop.const_div_atTop c

open Classical in
/-- **The headline of the band line.**  For every finite binary word `v`, the frequency of `v`
in the first `bT (i+1)` digits read along the strictly increasing position map `bandPos` tends
to `2^{−|v|}`.

The digits are `G₄`'s, read at a strictly increasing sequence of positions defined from the
schedule and the good atoms; the cutoffs `bT (i+1)` are the ends of the scale bands.  By
`certified_granule_exceeds_previous_scale` the limit over *all* prefix lengths — normality — is
not available on this mechanism; this is the strongest form that is. -/
theorem tendsto_bandRead_freq (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    Tendsto (fun i =>
        (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ) / (bT (i + 1) : ℝ))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  have hScard : ∀ i, (0 : ℝ) < ((bandS i).card : ℝ) := fun i => by
    have := card_bandS_pos i
    exact_mod_cast this
  have hkkpos : ∀ i, (0 : ℝ) < (kk i : ℝ) := fun i => by
    have := kk_pos' i
    exact_mod_cast this
  have hBpos : ∀ i, (0 : ℝ) < ((bT (i + 1) : ℕ) : ℝ) := fun i => by
    have : 0 < bT (i + 1) := lt_of_le_of_lt (Nat.zero_le _) (bT_lt_succ i)
    exact_mod_cast this
  have hBeq : ∀ i, ((bT (i + 1) : ℕ) : ℝ)
      = (bT i : ℝ) + ((bandS i).card : ℝ) * (kk i : ℝ) := by
    intro i
    show ((bT i + bL i : ℕ) : ℝ) = _
    rw [bL]
    push_cast
    ring
  have hT4 : ∀ i, (bT i : ℝ) ≤ 4 * ((bandS i).card : ℝ) := by
    intro i
    have h := bT_kk_le i
    have hbl : (bL i : ℝ) = ((bandS i).card : ℝ) * (kk i : ℝ) := by
      show ((((bandS i).card * kk i : ℕ)) : ℝ) = _
      push_cast; ring
    rw [hbl] at h
    nlinarith [hkkpos i, hScard i]
  -- the band's own ratio
  have hrlim : Tendsto (fun i => (bandGood i (primeLambertAtBase 4) v : ℝ)
      / (((bandS i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    refine (tendsto_band_occursCount v hlen hv).congr fun i => ?_
    rw [bandGood_eq i (primeLambertAtBase 4) v]
    congr 1
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun q =>
      (((bandS i).filter fun n =>
        OccursAt 2 (primeLambertAtBase 4) v
          (2 * kIdx (gridAt i) n (goodAtom i) + q)).card : ℝ))]
  -- the denominator correction
  have hcast : ∀ i, v.length ≤ kk i →
      ((kk i - v.length + 1 : ℕ) : ℝ) = (kk i : ℝ) - (v.length : ℝ) + 1 := by
    intro i hi
    have h1 : (kk i - v.length + 1 : ℕ) = kk i + 1 - v.length := by omega
    rw [h1, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hulim : Tendsto (fun i => (((bandS i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))
      / ((bT (i + 1) : ℕ) : ℝ)) atTop (nhds 1) := by
    have hsq : Tendsto (fun i => (((bandS i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))
        / ((bT (i + 1) : ℕ) : ℝ) - 1) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_div_kk ((v.length : ℝ) + 4))
      filter_upwards [eventually_ge_atTop v.length] with i hi
      have hli : v.length ≤ kk i := by unfold kk; omega
      have hSc := hScard i
      have hk := hkkpos i
      have hB := hBpos i
      have hTnn : (0 : ℝ) ≤ (bT i : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, hcast i hli, hBeq i, abs_le]
      set S : ℝ := ((bandS i).card : ℝ) with hS
      set K : ℝ := (kk i : ℝ) with hK
      set T : ℝ := (bT i : ℝ) with hT
      set L : ℝ := (v.length : ℝ) with hL
      have hSpos : 0 < S := hSc
      have hKpos : 0 < K := hk
      have hTnn' : 0 ≤ T := hTnn
      have hT4' : T ≤ 4 * S := hT4 i
      have hLnn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      have hden : (0 : ℝ) < T + S * K := by nlinarith
      have hSK : S ≤ (T + S * K) / K := by
        rw [le_div_iff₀ hKpos]
        nlinarith
      set D : ℝ := (L + 4) / K with hD
      have hmul : (L + 4) * S ≤ D * (T + S * K) := by
        have h2 : (L + 4) * S ≤ (L + 4) * ((T + S * K) / K) :=
          mul_le_mul_of_nonneg_left hSK (by linarith)
        have h3 : (L + 4) * ((T + S * K) / K) = D * (T + S * K) := by
          rw [hD]; field_simp
        linarith [h3 ▸ h2]
      have hkeyL : 1 - D ≤ S * (K - L + 1) / (T + S * K) := by
        rw [le_div_iff₀ hden]
        nlinarith [hmul, hT4']
      have hkeyR : S * (K - L + 1) / (T + S * K) ≤ 1 + D := by
        rw [div_le_iff₀ hden]
        nlinarith [hmul, hSpos, hLnn, hTnn']
      constructor
      · linarith [hkeyL]
      · linarith [hkeyR]
    have := hsq.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    rw [zero_add] at this
    exact this.congr fun i => by ring
  have hABlim : Tendsto (fun i => (bandGood i (primeLambertAtBase 4) v : ℝ)
      / ((bT (i + 1) : ℕ) : ℝ)) atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have h := hrlim.mul hulim
    rw [mul_one] at h
    refine h.congr fun i => ?_
    have hSc := (hScard i).ne'
    have hk := (hkkpos i).ne'
    have hB := (hBpos i).ne'
    have hfit : ((kk i - v.length + 1 : ℕ) : ℝ) ≠ 0 := by
      have : 0 < kk i - v.length + 1 := by omega
      have : (0 : ℝ) < ((kk i - v.length + 1 : ℕ) : ℝ) := by exact_mod_cast this
      exact this.ne'
    field_simp
  -- the seam error
  have hdlim : Tendsto (fun i =>
      (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ) / ((bT (i + 1) : ℕ) : ℝ)
        - (bandGood i (primeLambertAtBase 4) v : ℝ) / ((bT (i + 1) : ℕ) : ℝ))
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_kk ((v.length : ℝ) + 4))
    filter_upwards [eventually_ge_atTop v.length] with i hi
    have hli : v.length ≤ kk i := by unfold kk; omega
    have hSc := hScard i
    have hk := hkkpos i
    have hB := hBpos i
    have hTnn : (0 : ℝ) ≤ (bT i : ℝ) := Nat.cast_nonneg _
    obtain ⟨hlo, hhi⟩ := winCount_bT_bounds (primeLambertAtBase 4) i v hlen hli
    have hlowR : (bandGood i (primeLambertAtBase 4) v : ℝ)
        ≤ (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ) := by
      exact_mod_cast hlo
    have hhighR : (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ)
        ≤ (bandGood i (primeLambertAtBase 4) v : ℝ) + (bT i : ℝ)
          + ((bandS i).card : ℝ) * (v.length : ℝ) := by
      have : ((bandGood i (primeLambertAtBase 4) v + bT i
          + (bandS i).card * v.length : ℕ) : ℝ)
          = (bandGood i (primeLambertAtBase 4) v : ℝ) + (bT i : ℝ)
            + ((bandS i).card : ℝ) * (v.length : ℝ) := by push_cast; ring
      rw [← this]
      exact_mod_cast hhi
    have hBge : ((bandS i).card : ℝ) * (kk i : ℝ) ≤ ((bT (i + 1) : ℕ) : ℝ) := by
      rw [hBeq i]
      linarith
    rw [Real.norm_eq_abs, div_sub_div_same, abs_le]
    constructor
    · rw [neg_le, ← neg_div, neg_sub]
      have hnn : (0 : ℝ) ≤ ((v.length : ℝ) + 4) / (kk i : ℝ) := by positivity
      have hle : (bandGood i (primeLambertAtBase 4) v : ℝ)
          - (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ) ≤ 0 := by linarith
      have : ((bandGood i (primeLambertAtBase 4) v : ℝ)
          - (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ))
          / ((bT (i + 1) : ℕ) : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle hB.le
      linarith
    · rw [div_le_div_iff₀ hB hk]
      have hWA : (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ)
          - (bandGood i (primeLambertAtBase 4) v : ℝ)
          ≤ 4 * ((bandS i).card : ℝ) + ((bandS i).card : ℝ) * (v.length : ℝ) := by
        linarith [hT4 i]
      nlinarith [hWA, hBge, hSc, hk]
  have hfin := hdlim.add hABlim
  rw [zero_add] at hfin
  exact hfin.congr fun i => by ring

/-! ### The real read along the band sequence -/

open Classical in
/-- Every finite binary word occurs somewhere in the band read: its frequency is positive. -/
theorem exists_matchesAt_bandDig (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    ∃ t, MatchesAt (bandDig (primeLambertAtBase 4)) v t := by
  classical
  have hlim := tendsto_bandRead_freq v hlen hv
  have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ v.length := by positivity
  obtain ⟨i, hi⟩ := (hlim.eventually (eventually_gt_nhds hpos)).exists
  have hBpos : (0 : ℝ) < ((bT (i + 1) : ℕ) : ℝ) := by
    have : 0 < bT (i + 1) := lt_of_le_of_lt (Nat.zero_le _) (bT_lt_succ i)
    exact_mod_cast this
  have hWpos : (0 : ℝ) < (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have : (winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) : ℝ)
        / ((bT (i + 1) : ℕ) : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon hBpos.le
    linarith
  have hW : 0 < winCount (bandDig (primeLambertAtBase 4)) v (bT (i + 1)) := by
    exact_mod_cast hWpos
  obtain ⟨t, ht⟩ := Finset.card_pos.1 hW
  exact ⟨t, (Finset.mem_filter.1 ht).2⟩

/-- The band read never sticks at `1`. -/
theorem properDigits_bandDig : ProperDigits 2 (bandDig (primeLambertAtBase 4)) := by
  intro N
  have hlenv : (List.replicate (N + 1) 0).length = N + 1 := by simp
  have hbin : ∀ j, ∀ h : j < (List.replicate (N + 1) 0).length,
      (List.replicate (N + 1) 0)[j] < 2 := by
    intro j hj
    rw [List.getElem_replicate]
    omega
  obtain ⟨t, ht⟩ := exists_matchesAt_bandDig (List.replicate (N + 1) 0) (by omega) hbin
  refine ⟨t + N, by omega, ?_⟩
  have hN : N < (List.replicate (N + 1) 0).length := by omega
  have h := ht N hN
  rw [List.getD_eq_getElem _ 0 hN, List.getElem_replicate] at h
  have h0 : bandDig (primeLambertAtBase 4) (t + N) = 0 := h
  rw [h0]
  omega

/-- **The real read along the band sequence**: `G₄`'s digits at the strictly increasing
positions `bandPos`, summed in base two. -/
noncomputable def bandReal : ℝ := realOfDigits 2 (bandDig (primeLambertAtBase 4))

/-- Every finite binary word occurs in `bandReal`. -/
theorem isDisjunctive_bandReal : IsDisjunctive 2 bandReal := by
  have hmem := realOfDigits_mem_Ico 2 (le_refl 2) (bandDig (primeLambertAtBase 4))
    (bandDig_lt _) properDigits_bandDig
  rw [Set.mem_Ico] at hmem
  have hfract : Int.fract bandReal = bandReal := Int.fract_eq_self.mpr hmem
  have hdig : digitOf 2 bandReal = bandDig (primeLambertAtBase 4) :=
    digitOf_realOfDigits 2 (le_refl 2) _ (bandDig_lt _) properDigits_bandDig
  rw [isDisjunctive_iff_forall_occursAt 2 (le_refl 2)]
  intro w hw
  by_cases hw0 : w = []
  · subst hw0
    exact ⟨0, fun j hj => absurd hj (by simp)⟩
  · have hlen : 0 < w.length := List.length_pos_iff.2 hw0
    have hbin : ∀ j, ∀ h : j < w.length, w[j] < 2 :=
      fun j hj => hw _ (List.getElem_mem hj)
    obtain ⟨t, ht⟩ := exists_matchesAt_bandDig w hlen hbin
    refine ⟨t, fun j hj => ?_⟩
    rw [hfract, hdig]
    have h : bandDig (primeLambertAtBase 4) (t + j) = w.getD j 0 := ht j hj
    rw [h]
    exact List.getD_eq_getElem _ 0 hj

theorem irrational_bandReal : Irrational bandReal :=
  isDisjunctive_bandReal.irrational

/-! ### Non-vacuity: the band read sees only sampled positions -/

/-- **Every position the band read visits is a sampled position.**  Hence, by
`tendsto_density_isSampled`, `bandPos` skips almost every digit of `G₄`: `bandReal` is built
from a density-zero set of `G₄`'s digits and is in no sense `G₄` itself. -/
theorem isSampled_bandPos (j : ℕ) : IsSampled (bandPos j) := by
  classical
  set i := bgrp j with hi
  have h1 : bT i ≤ j := bT_bgrp_le j
  have h2 : j < bT (i + 1) := lt_bT_bgrp_succ j
  have hbT : bT (i + 1) = bT i + bL i := rfl
  have hkk : 0 < kk i := kk_pos' i
  set r : ℕ := j - bT i with hr
  have hrlt : r < bL i := by omega
  have hacard : r / kk i < (bandS i).card := by
    by_contra hcon
    push_neg at hcon
    have h := Nat.div_mul_le_self r (kk i)
    have hmul : (bandS i).card * kk i ≤ r / kk i * kk i := Nat.mul_le_mul_right _ hcon
    rw [bL] at hrlt
    have hdm := Nat.div_add_mod' r (kk i)
    omega
  have hmod : r % kk i < kk i := Nat.mod_lt _ hkk
  have heq : bandPos j = 2 * kIdx (gridAt i) (bnth i (r / kk i)) (goodAtom i) + r % kk i := by
    rw [bandPos_eq h1 h2, bpos]
  refine ⟨i, ?_⟩
  rw [heq]
  exact mem_sampledPos_of (gridAt i) (bnth_mem_PK i (r / kk i)) (goodAtom i) hmod

/-! ### Faithfulness: the statements are not vacuous -/

/-- The band read is a genuine injection of read indices into digit positions. -/
theorem bandPos_injective : Function.Injective bandPos := bandPos_strictMono.injective

/-- The cutoffs are cofinal, so `tendsto_bandRead_freq` is a statement about arbitrarily long
prefixes. -/
theorem tendsto_bT_atTop : Tendsto (fun i => (bT i : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
  have : i ≤ bT i := self_le_bT i
  exact_mod_cast this

/-- The read positions themselves are cofinal. -/
theorem tendsto_bandPos_atTop : Tendsto (fun j => (bandPos j : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
  have : j ≤ bandPos j := bandPos_strictMono.le_apply
  exact_mod_cast this

end NormalNumbers.G4.Sched
