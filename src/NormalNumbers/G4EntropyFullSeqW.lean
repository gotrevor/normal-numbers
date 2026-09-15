/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandWide
import NormalNumbers.G4EntropyFullSeq

/-!
# The **wide** schedule-only band read

`G4EntropyFullSeq`'s read `fullPos` runs over `bandT i`, the level-`i` sample between the
previous band's ceiling and `X (KK i)`.  This module re-runs the same construction over the
*wide* band `bandW i` of `G4EntropyBandWide`: the level-`i` sample between `wFloor i` and the
top of level `i`'s own certified tile, `wTop i = Xlo (KK (i+1))`.

Everything in `G4EntropyFullSeq`'s construction is band-generic and ports verbatim, with two
substitutions:

* `windows_eq_or_disjoint` ⇝ `windows_eq_or_disjoint_at` (the band no longer sits inside
  `PK i`, since `wTop i > X (KK i)`);
* the read's strict monotonicity used `bandLo (i+1) = bandTop i` **definitionally**; here the
  corresponding fact is the *inequality* `wPosTop_le_wLo_succ`.
-/


open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The band's window starts -/

open Classical in
/-- The distinct window starts of band `i`. -/
noncomputable def winStartsW (i : ℕ) : Finset ℕ :=
  ((bandW i) ×ˢ (Finset.univ : Finset (gridAt i).Atom)).image
    (fun z => 2 * kIdx (gridAt i) z.1 z.2)

open Classical in
lemma mem_winStartsW (i : ℕ) {q : ℕ} :
    q ∈ winStartsW i ↔ ∃ n ∈ bandW i, ∃ α : (gridAt i).Atom, q = 2 * kIdx (gridAt i) n α := by
  classical
  rw [winStartsW, Finset.mem_image]
  constructor
  · rintro ⟨⟨n, α⟩, hz, rfl⟩
    exact ⟨n, (Finset.mem_product.1 hz).1, α, rfl⟩
  · rintro ⟨n, hn, α, rfl⟩
    exact ⟨(n, α), Finset.mem_product.2 ⟨hn, Finset.mem_univ _⟩, rfl⟩

lemma winStartsW_nonempty (i : ℕ) : (winStartsW i).Nonempty := by
  classical
  obtain ⟨n, hn⟩ := bandW_nonempty i
  exact ⟨2 * kIdx (gridAt i) n (Classical.arbitrary _),
    (mem_winStartsW i).2 ⟨n, hn, Classical.arbitrary _, rfl⟩⟩

lemma card_winStartsW_pos (i : ℕ) : 0 < (winStartsW i).card :=
  Finset.card_pos.2 (winStartsW_nonempty i)

/-- **Distinct window starts are a full window apart.**  This is `windows_eq_or_disjoint` read on
the `Finset` of starts. -/
theorem winStartsW_gap (i : ℕ) {q q' : ℕ} (hq : q ∈ winStartsW i) (hq' : q' ∈ winStartsW i)
    (hlt : q < q') : q + kk i ≤ q' := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStartsW i).1 hq
  obtain ⟨n', hn', β, rfl⟩ := (mem_winStartsW i).1 hq'
  rcases windows_eq_or_disjoint_at i (wTop i) (bandW_subset i hn) (bandW_subset i hn') α β with h | h | h
  · omega
  · exact h
  · omega

/-- Every band-`i` window start is above the band floor. -/
lemma wLo_le_winStartsW (i : ℕ) {q : ℕ} (hq : q ∈ winStartsW i) : wLo i ≤ q := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStartsW i).1 hq
  exact wLo_le_pos_of_mem_bandWtr i (wTop i) hn α

/-- Every band-`i` window lies below the band ceiling. -/
lemma winStartsW_add_lt_wPosTop (i : ℕ) {q : ℕ} (hq : q ∈ winStartsW i) {p : ℕ} (hp : p < kk i) :
    q + p < wPosTop i := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStartsW i).1 hq
  exact pos_lt_wPosTop i (wTop i) (le_refl _) (bandW_subset i hn) α hp

/-! ### Enumerating them -/

/-- The `a`-th window start of band `i`, in increasing order (cyclically extended). -/
noncomputable def fnthW (i a : ℕ) : ℕ :=
  (winStartsW i).orderEmbOfFin rfl ⟨a % (winStartsW i).card, Nat.mod_lt _ (card_winStartsW_pos i)⟩

lemma fnthW_mem (i a : ℕ) : fnthW i a ∈ winStartsW i := by
  rw [fnthW]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma fnthW_lt_fnthW {i a b : ℕ} (hab : a < b) (hb : b < (winStartsW i).card) :
    fnthW i a < fnthW i b := by
  have ha : a < (winStartsW i).card := lt_trans hab hb
  rw [fnthW, fnthW]
  refine (Finset.orderEmbOfFin (winStartsW i) rfl).strictMono ?_
  refine Fin.mk_lt_mk.2 ?_
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

/-- **Consecutive window starts are a full window apart.** -/
lemma fnthW_gap {i a b : ℕ} (hab : a < b) (hb : b < (winStartsW i).card) :
    fnthW i a + kk i ≤ fnthW i b :=
  winStartsW_gap i (fnthW_mem i a) (fnthW_mem i b) (fnthW_lt_fnthW hab hb)

lemma wLo_le_fnthW (i a : ℕ) : wLo i ≤ fnthW i a :=
  wLo_le_winStartsW i (fnthW_mem i a)

lemma fnthW_add_lt_wPosTop (i a : ℕ) {p : ℕ} (hp : p < kk i) : fnthW i a + p < wPosTop i :=
  winStartsW_add_lt_wPosTop i (fnthW_mem i a) hp

/-! ### The schedule-only position map -/

/-- The number of digits band `i` contributes to the schedule-only read. -/
noncomputable def fLW (i : ℕ) : ℕ := (winStartsW i).card * kk i

lemma fLW_pos (i : ℕ) : 0 < fLW i :=
  Nat.mul_pos (card_winStartsW_pos i) (by unfold kk; omega)

/-- The cutoff after the first `i` bands. -/
noncomputable def fTW : ℕ → ℕ
  | 0 => 0
  | (i + 1) => fTW i + fLW i

lemma fTW_lt_succ (i : ℕ) : fTW i < fTW (i + 1) := by
  have := fLW_pos i
  show fTW i < fTW i + fLW i
  omega

lemma fTW_mono : Monotone fTW := monotone_nat_of_le_succ fun i => (fTW_lt_succ i).le

lemma self_le_fTW (i : ℕ) : i ≤ fTW i := by
  induction i with
  | zero => simp [fTW]
  | succ i ih => have := fTW_lt_succ i; omega

/-- The band a read index belongs to. -/
noncomputable def fgrpW (j : ℕ) : ℕ := Nat.findGreatest (fun m => fTW m ≤ j) j

lemma fgrpW_eq {i j : ℕ} (h1 : fTW i ≤ j) (h2 : j < fTW (i + 1)) : fgrpW j = i := by
  classical
  have hij : i ≤ j := le_trans (self_le_fTW i) h1
  have hle : i ≤ fgrpW j := Nat.le_findGreatest hij h1
  by_contra hne
  have hlt : i < fgrpW j := lt_of_le_of_ne hle (Ne.symm hne)
  have hspec : fTW (fgrpW j) ≤ j := Nat.findGreatest_spec (P := fun m => fTW m ≤ j) hij h1
  have : fTW (i + 1) ≤ fTW (fgrpW j) := fTW_mono (by omega)
  omega

lemma fTW_fgrpW_le (j : ℕ) : fTW (fgrpW j) ≤ j := by
  classical
  exact Nat.findGreatest_spec (P := fun m => fTW m ≤ j) (Nat.zero_le j) (by simp [fTW])

lemma lt_fTW_fgrpW_succ (j : ℕ) : j < fTW (fgrpW j + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have h1 : fgrpW j + 1 ≤ j := le_trans (self_le_fTW (fgrpW j + 1)) hcon
  have h2 : fgrpW j + 1 ≤ fgrpW j := Nat.le_findGreatest h1 hcon
  omega

/-- **The schedule-only position map.**  Bands in order; inside a band, the distinct window
starts in order; inside a window, the `m_i` consecutive positions.  No reference to `G₄`. -/
noncomputable def fullPosW (j : ℕ) : ℕ :=
  fnthW (fgrpW j) ((j - fTW (fgrpW j)) / kk (fgrpW j)) + (j - fTW (fgrpW j)) % kk (fgrpW j)

lemma fullPosW_eq {i j : ℕ} (h1 : fTW i ≤ j) (h2 : j < fTW (i + 1)) :
    fullPosW j = fnthW i ((j - fTW i) / kk i) + (j - fTW i) % kk i := by
  rw [fullPosW, fgrpW_eq h1 h2]

/-- **The schedule-only read is a genuine subsequence.** -/
theorem fullPosW_strictMono : StrictMono fullPosW := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  set i := fgrpW j with hi
  have h1 : fTW i ≤ j := fTW_fgrpW_le j
  have h2 : j < fTW (i + 1) := lt_fTW_fgrpW_succ j
  have hfT : fTW (i + 1) = fTW i + fLW i := rfl
  set r : ℕ := j - fTW i with hr
  have hrlt : r < fLW i := by omega
  have hkk : 0 < kk i := by unfold kk; omega
  set a : ℕ := r / kk i with ha
  set p : ℕ := r % kk i with hp
  have hpk : p < kk i := Nat.mod_lt _ hkk
  have hra : r = a * kk i + p := (Nat.div_add_mod' r (kk i)).symm
  have hacard : a < (winStartsW i).card := by
    by_contra hcon
    push_neg at hcon
    have : (winStartsW i).card * kk i ≤ a * kk i := Nat.mul_le_mul_right _ hcon
    rw [fLW] at hrlt
    omega
  have hj : fullPosW j = fnthW i a + p := fullPosW_eq h1 h2
  rcases Nat.lt_or_ge (p + 1) (kk i) with hcase | hcase
  · have hr1 : j + 1 - fTW i = r + 1 := by omega
    have hlt1 : j + 1 < fTW (i + 1) := by
      rw [hfT, fLW]
      have : (a + 1) * kk i ≤ (winStartsW i).card * kk i := Nat.mul_le_mul_right _ hacard
      have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
      omega
    have hdiv : (r + 1) / kk i = a := by
      rw [hra]
      have hc : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [hc, Nat.mul_add_div hkk, Nat.div_eq_of_lt hcase]
      omega
    have hmod : (r + 1) % kk i = p + 1 := by
      rw [hra]
      have hc : a * kk i + p + 1 = kk i * a + (p + 1) := by ring
      rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hcase]
    have := fullPosW_eq (i := i) (j := j + 1) (by omega) hlt1
    rw [this, hr1, hdiv, hmod, hj]
    omega
  · have hpk1 : p + 1 = kk i := by omega
    rcases Nat.lt_or_ge (a + 1) (winStartsW i).card with hcase2 | hcase2
    · have hr1 : j + 1 - fTW i = r + 1 := by omega
      have hreq : r + 1 = (a + 1) * kk i := by
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hlt1 : j + 1 < fTW (i + 1) := by
        rw [hfT, fLW]
        have : (a + 1) * kk i < (winStartsW i).card * kk i :=
          Nat.mul_lt_mul_of_lt_of_le hcase2 (le_refl _) hkk
        omega
      have hdiv : (r + 1) / kk i = a + 1 := by rw [hreq, Nat.mul_div_cancel _ hkk]
      have hmod : (r + 1) % kk i = 0 := by rw [hreq, Nat.mul_mod_left]
      have heq := fullPosW_eq (i := i) (j := j + 1) (by omega) hlt1
      rw [heq, hr1, hdiv, hmod, hj]
      have hgap := fnthW_gap (i := i) (a := a) (b := a + 1) (by omega) hcase2
      omega
    · have hacard' : a + 1 = (winStartsW i).card := by omega
      have hreq : r + 1 = fLW i := by
        rw [fLW, ← hacard']
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hj1 : j + 1 = fTW (i + 1) := by rw [hfT]; omega
      have hlt2 : fTW (i + 1) ≤ j + 1 := by omega
      have hlt3 : j + 1 < fTW (i + 1 + 1) := by
        have := fTW_lt_succ (i + 1)
        omega
      have heq := fullPosW_eq (i := i + 1) (j := j + 1) hlt2 hlt3
      have hzero : j + 1 - fTW (i + 1) = 0 := by omega
      rw [heq, hzero, Nat.zero_div, Nat.zero_mod, hj]
      have hup : wLo (i + 1) ≤ fnthW (i + 1) 0 := wLo_le_fnthW (i + 1) 0
      have hlo : wPosTop i ≤ wLo (i + 1) := wPosTop_le_wLo_succ i
      have hdown : fnthW i a + p < wPosTop i := fnthW_add_lt_wPosTop i a hpk
      omega

/-! ### The digits read, and the window dictionary -/

/-- The digit sequence read along `fullPosW`. -/
noncomputable def fullDigW (x : ℝ) (j : ℕ) : ℕ := digitOf 2 (Int.fract x) (fullPosW j)

lemma fullDigW_lt (x : ℝ) (j : ℕ) : fullDigW x j < 2 := Nat.mod_lt _ (by omega)

/-- Inside band `i`, the `a`-th window occupies the read indices `fTW i + a·m_i + q`. -/
lemma fullPosW_window (i a q : ℕ) (ha : a < (winStartsW i).card) (hq : q < kk i) :
    fullPosW (fTW i + a * kk i + q) = fnthW i a + q := by
  have hkk : 0 < kk i := by unfold kk; omega
  have hlt : a * kk i + q < fLW i := by
    rw [fLW]
    have : (a + 1) * kk i ≤ (winStartsW i).card * kk i := Nat.mul_le_mul_right _ ha
    have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
    omega
  have h1 : fTW i ≤ fTW i + a * kk i + q := by omega
  have h2 : fTW i + a * kk i + q < fTW (i + 1) := by
    show fTW i + a * kk i + q < fTW i + fLW i
    omega
  have hsub : fTW i + a * kk i + q - fTW i = a * kk i + q := by omega
  have hdiv : (a * kk i + q) / kk i = a := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_div hkk, Nat.div_eq_of_lt hq]
    omega
  have hmod : (a * kk i + q) % kk i = q := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  rw [fullPosW_eq h1 h2, hsub, hdiv, hmod]

/-- **The dictionary**: a window of `v` fitting inside one band window is an occurrence of `v`
in `x` at the corresponding digit position. -/
lemma matchesAt_fullDigW_iff (x : ℝ) (i a q : ℕ) (v : List ℕ) (ha : a < (winStartsW i).card)
    (hq : q + v.length ≤ kk i) :
    MatchesAt (fullDigW x) v (fTW i + a * kk i + q) ↔ OccursAt 2 x v (fnthW i a + q) := by
  have hkey : ∀ t < v.length,
      fullDigW x (fTW i + a * kk i + q + t) = digitOf 2 (Int.fract x) (fnthW i a + q + t) := by
    intro t ht
    have hqt : q + t < kk i := by omega
    have hrw : fTW i + a * kk i + q + t = fTW i + a * kk i + (q + t) := by ring
    rw [fullDigW, hrw, fullPosW_window i a (q + t) ha hqt]
    ring_nf
  constructor
  · intro h t ht
    have h' := h t ht
    rw [hkey t ht] at h'
    rw [h']
    exact (List.getD_eq_getElem v 0 ht)
  · intro h t ht
    show fullDigW x (fTW i + a * kk i + q + t) = _
    rw [hkey t ht, h t ht]
    exact (List.getD_eq_getElem v 0 ht).symm

set_option maxHeartbeats 1000000 in
/-- Summing over the band's window-start enumeration is summing over the starts. -/
lemma sum_range_fnthW {β : Type*} [AddCommMonoid β] (i : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (winStartsW i).card, g (fnthW i a) = ∑ q ∈ winStartsW i, g q := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun a => g (fnthW i a))]
  have hstep : ∀ a : Fin (winStartsW i).card,
      g (fnthW i (a : ℕ)) = g ((winStartsW i).orderEmbOfFin rfl a) := by
    intro a
    have hfin : (⟨(a : ℕ) % (winStartsW i).card, Nat.mod_lt _ (card_winStartsW_pos i)⟩ :
        Fin (winStartsW i).card) = a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    rw [fnthW, hfin]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  rw [← Finset.sum_attach (winStartsW i) g]
  refine Fintype.sum_bijective (fun a : Fin (winStartsW i).card =>
    (⟨(winStartsW i).orderEmbOfFin rfl a, Finset.orderEmbOfFin_mem _ _ _⟩ :
      (winStartsW i : Finset ℕ))) ?_ _ _ (fun a => rfl)
  constructor
  · intro a b hab
    have : ((winStartsW i).orderEmbOfFin rfl a : ℕ) = (winStartsW i).orderEmbOfFin rfl b :=
      congrArg Subtype.val hab
    exact (winStartsW i).orderEmbOfFin rfl |>.injective (by exact_mod_cast this)
  · rintro ⟨q, hq⟩
    have hrange : q ∈ Set.range ((winStartsW i).orderEmbOfFin (rfl : (winStartsW i).card = _)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hq
    obtain ⟨a, ha⟩ := hrange
    exact ⟨a, Subtype.ext ha⟩

/-! ### The read count over a band -/

open Classical in
/-- The number of fitting in-window occurrences of `v` in band `i`'s distinct windows. -/
noncomputable def fullGoodW (i : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ a ∈ Finset.range (winStartsW i).card,
    ((Finset.range (kk i - v.length + 1)).filter
      (fun q => OccursAt 2 x v (fnthW i a + q))).card

open Classical in
/-- `fullGoodW` re-summed over the band's window starts. -/
theorem fullGoodW_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    fullGoodW i x v
      = ∑ q ∈ winStartsW i,
          ((Finset.range (kk i - v.length + 1)).filter
            (fun p => OccursAt 2 x v (q + p))).card :=
  sum_range_fnthW i (fun q =>
    ((Finset.range (kk i - v.length + 1)).filter (fun p => OccursAt 2 x v (q + p))).card)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The band's contribution to the schedule-only read count**, up to one word length per
window. -/
theorem fullW_band_winCount_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) :
    fullGoodW i x v
        ≤ ((Finset.Ico (fTW i) (fTW (i + 1))).filter (MatchesAt (fullDigW x) v)).card ∧
      ((Finset.Ico (fTW i) (fTW (i + 1))).filter (MatchesAt (fullDigW x) v)).card
        ≤ fullGoodW i x v + (winStartsW i).card * v.length := by
  classical
  have hbT : fTW (i + 1) = fTW i + fLW i := rfl
  have hsplit : ((Finset.Ico (fTW i) (fTW (i + 1))).filter (MatchesAt (fullDigW x) v)).card
      = ∑ a ∈ Finset.range (winStartsW i).card,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (fullDigW x) v (fTW i + (a * kk i + q)))).card := by
    rw [hbT, card_Ico_shift _ (fTW i) (fLW i), fLW, card_filter_range_mul]
  rw [hsplit]
  have hper : ∀ a ∈ Finset.range (winStartsW i).card,
      ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnthW i a + q))).card
        ≤ ((Finset.range (kk i)).filter
          (fun q => MatchesAt (fullDigW x) v (fTW i + (a * kk i + q)))).card ∧
      ((Finset.range (kk i)).filter
          (fun q => MatchesAt (fullDigW x) v (fTW i + (a * kk i + q)))).card
        ≤ ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnthW i a + q))).card + v.length := by
    intro a ha
    have ha' : a < (winStartsW i).card := Finset.mem_range.1 ha
    have hcongr : ((Finset.range (kk i - v.length + 1)).filter
        (fun q => MatchesAt (fullDigW x) v (fTW i + (a * kk i + q)))).card
        = ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnthW i a + q))).card := by
      congr 1
      refine Finset.filter_congr fun q hq => ?_
      have hqfit : q + v.length ≤ kk i := by
        have := Finset.mem_range.1 hq
        omega
      have hassoc : fTW i + (a * kk i + q) = fTW i + a * kk i + q := by ring
      rw [hassoc]
      simpa using matchesAt_fullDigW_iff x i a q v ha' hqfit
    have h := card_filter_fit
      (fun q => MatchesAt (fullDigW x) v (fTW i + (a * kk i + q))) (m := kk i)
      (ℓ := v.length) hv hvm
    rw [hcongr] at h
    exact h
  constructor
  · exact Finset.sum_le_sum fun a ha => (hper a ha).1
  · calc ∑ a ∈ Finset.range (winStartsW i).card,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (fullDigW x) v (fTW i + (a * kk i + q)))).card
        ≤ ∑ a ∈ Finset.range (winStartsW i).card,
            (((Finset.range (kk i - v.length + 1)).filter
              (fun q => OccursAt 2 x v (fnthW i a + q))).card + v.length) :=
          Finset.sum_le_sum fun a ha => (hper a ha).2
      _ = fullGoodW i x v + (winStartsW i).card * v.length := by
          rw [Finset.sum_add_distrib, fullGoodW]
          simp [mul_comm]

set_option maxHeartbeats 1000000 in
open Classical in
/-- The full read count at the band cutoffs. -/
theorem fullW_winCount_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) :
    fullGoodW i x v ≤ winCount (fullDigW x) v (fTW (i + 1)) ∧
      winCount (fullDigW x) v (fTW (i + 1))
        ≤ fullGoodW i x v + fTW i + (winStartsW i).card * v.length := by
  classical
  have hsplit := winCount_split (fullDigW x) v (fTW_mono (Nat.le_succ i))
  simp only [Nat.succ_eq_add_one] at hsplit
  obtain ⟨h1, h2⟩ := fullW_band_winCount_bounds x i v hv hvm
  have hhist : winCount (fullDigW x) v (fTW i) ≤ fTW i := winCount_le _ _ _
  generalize hc : (winStartsW i).card * v.length = c at h2 ⊢
  rw [hsplit]
  omega

/-! ### Bridging the wide band to the old sample -/

lemma X_le_wTop (i : ℕ) : X (KK i) ≤ wTop i := by
  have := eighteen_X_le_wTop i
  have hX : 0 < X (KK i) := by
    have : X (KK i) = 2 ^ (100 * 2 ^ m (KK i)) := rfl
    rw [this]; positivity
  omega

/-- The old sample sits inside the wide band's truncation: `wTop i ≥ X (KK i)`. -/
lemma PK_subset_PKtr_wTop (i : ℕ) : PK i ⊆ PKtr i (wTop i) := by
  intro n hn
  rw [PK, apSample, Finset.mem_filter, Finset.mem_range] at hn
  rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_lt_of_le hn.1 (X_le_wTop i), hn.2⟩

lemma card_bandW_ge (i : ℕ) : ((PKtr i (wTop i)).card : ℝ) ≤ 2 * ((bandW i).card : ℝ) :=
  card_bandWtr_ge i (wTop i) (wgate_wTop i)

/-- `|Atom|² ≤ |P_K|` at the tile top, by monotonicity from `card_Atom_sq_le_PK`. -/
theorem card_Atom_sq_le_PKW (i : ℕ) :
    (Fintype.card (gridAt i).Atom : ℝ) ^ 2 ≤ ((PKtr i (wTop i)).card : ℝ) := by
  refine le_trans (card_Atom_sq_le_PK i) ?_
  exact Nat.cast_le.2 (Finset.card_le_card (PK_subset_PKtr_wTop i))


/-! ### From distinct windows to `(n, α)` pairs: the multiplicity bridge -/

open Classical in
/-- The window-occurrence count of one window start. -/
noncomputable def winOccW (i : ℕ) (x : ℝ) (v : List ℕ) (q : ℕ) : ℕ :=
  ((Finset.range (kk i - v.length + 1)).filter (fun p => OccursAt 2 x v (q + p))).card

lemma winOccW_le (i : ℕ) (x : ℝ) (v : List ℕ) (q : ℕ) :
    winOccW i x v q ≤ kk i - v.length + 1 := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [winOccW]

open Classical in
/-- The band's `(n, α)` pairs. -/
noncomputable def bandWPairs (i : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  (bandW i) ×ˢ (Finset.univ : Finset (gridAt i).Atom)

open Classical in
lemma winStartsW_eq_image (i : ℕ) :
    winStartsW i = (bandWPairs i).image (fun z => 2 * kIdx (gridAt i) z.1 z.2) := rfl

open Classical in
/-- **The pair sum is the multiplicity-weighted start sum.** -/
theorem sum_pairsW_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    ∑ z ∈ bandWPairs i, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      = ∑ q ∈ winStartsW i,
          ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card
            * winOccW i x v q := by
  classical
  rw [winStartsW_eq_image]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := bandWPairs i) (t := (bandWPairs i).image (fun z => 2 * kIdx (gridAt i) z.1 z.2))
    (g := fun z => 2 * kIdx (gridAt i) z.1 z.2)
    (fun z hz => Finset.mem_image_of_mem _ hz)
    (fun z => winOccW i x v (2 * kIdx (gridAt i) z.1 z.2))
  rw [← hfib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hcongr : ∀ z ∈ (bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q),
      winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) = winOccW i x v q := by
    intro z hz
    rw [(Finset.mem_filter.1 hz).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]

open Classical in
/-- Each fiber is nonempty, so the excess `|pairs| − |starts|` is the total multiplicity
overhangW. -/
theorem card_bandWPairs_sub (i : ℕ) :
    (winStartsW i).card ≤ (bandWPairs i).card := by
  classical
  rw [winStartsW_eq_image]
  exact Finset.card_image_le

open Classical in
/-- **The pair sum exceeds the start sum by at most the overhangW, times the window length.** -/
theorem sum_pairsW_sub_le (i : ℕ) (x : ℝ) (v : List ℕ) :
    ∑ q ∈ winStartsW i, winOccW i x v q ≤ ∑ z ∈ bandWPairs i,
        winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) ∧
      ∑ z ∈ bandWPairs i, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
        ≤ ∑ q ∈ winStartsW i, winOccW i x v q
          + ((bandWPairs i).card - (winStartsW i).card) * (kk i - v.length + 1) := by
  classical
  rw [sum_pairsW_eq i x v]
  have hfib : ∀ q ∈ winStartsW i,
      1 ≤ ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card := by
    intro q hq
    rw [winStartsW_eq_image, Finset.mem_image] at hq
    obtain ⟨z, hz, hzq⟩ := hq
    exact Finset.card_pos.2 ⟨z, Finset.mem_filter.2 ⟨hz, hzq⟩⟩
  have hsumfib : ∑ q ∈ winStartsW i,
      ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card
      = (bandWPairs i).card := by
    rw [winStartsW_eq_image]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun z hz => Finset.mem_image_of_mem _ hz)).symm
  constructor
  · refine Finset.sum_le_sum fun q hq => ?_
    have hc := hfib q hq
    exact Nat.le_mul_of_pos_left _ (by omega)
  · have hterm : ∀ q ∈ winStartsW i,
        ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card
            * winOccW i x v q
          ≤ winOccW i x v q
            + (((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
              * (kk i - v.length + 1) := by
      intro q hq
      have h1 := hfib q hq
      have h2 := winOccW_le i x v q
      set c := ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card with hc
      have hc1 : c - 1 + 1 = c := by omega
      calc c * winOccW i x v q = ((c - 1) + 1) * winOccW i x v q := by rw [hc1]
        _ = winOccW i x v q + (c - 1) * winOccW i x v q := by ring
        _ ≤ winOccW i x v q + (c - 1) * (kk i - v.length + 1) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    have hsub : ∑ q ∈ winStartsW i,
        (((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
        ≤ (bandWPairs i).card - (winStartsW i).card := by
      have hle : ∑ q ∈ winStartsW i, 1 ≤ ∑ q ∈ winStartsW i,
          ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card :=
        Finset.sum_le_sum hfib
      have hcards : ∑ q ∈ winStartsW i, (1 : ℕ) = (winStartsW i).card := by simp
      have hsplit : ∑ q ∈ winStartsW i,
          (((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
          = (∑ q ∈ winStartsW i,
              ((bandWPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card)
            - ∑ q ∈ winStartsW i, 1 := by
        rw [← Finset.sum_tsub_distrib]
        exact fun q hq => hfib q hq
      rw [hsplit, hsumfib, hcards]
    exact hsub

/-! ### The overhangW is a vanishing fraction -/

open Classical in
/-- The band pairs whose window is shared with another atom. -/
noncomputable def badWPairs (i : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  (bandWPairs i).filter (fun z => ∃ β, β ≠ z.2 ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) z.1 z.2))

open Classical in
/-- **The multiplicity overhangW is at most the number of shared pairs.**  Off `badWPairs` the
window-start map is injective. -/
theorem overhangW_le (i : ℕ) :
    (bandWPairs i).card - (winStartsW i).card ≤ (badWPairs i).card := by
  classical
  have hinj : ((bandWPairs i) \ (badWPairs i)).card ≤ (winStartsW i).card := by
    refine Finset.card_le_card_of_injOn (fun z => 2 * kIdx (gridAt i) z.1 z.2) ?_ ?_
    · intro z hz
      simp only [Finset.coe_sdiff, Set.mem_diff] at hz
      have hz1 : z ∈ bandWPairs i := hz.1
      exact (mem_winStartsW i).2 ⟨z.1, (Finset.mem_product.1 hz1).1, z.2, rfl⟩
    · intro z hz z' hz' heq
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hz hz'
      simp only at heq
      by_cases hat : z.2 = z'.2
      · -- same atom: `n ↦ kIdx` is injective
        have hz1 : z.1 ∈ bandW i := (Finset.mem_product.1 hz.1).1
        have hz1' : z'.1 ∈ bandW i := (Finset.mem_product.1 hz'.1).1
        have hkk : 0 < kk i := by unfold kk; omega
        have heq' : 2 * kIdx (gridAt i) z.1 z.2 = 2 * kIdx (gridAt i) z'.1 z.2 := by
          rw [heq, ← hat]
        have hn : z.1 = z'.1 := by
          by_contra hne
          rcases Nat.lt_or_ge z.1 z'.1 with hlt | hge
          · have hg := window_gap_same_atom_at i (wTop i) z.2 (bandW_subset i hz1) (bandW_subset i hz1') hlt
            omega
          · have hgt : z'.1 < z.1 := by omega
            have hg := window_gap_same_atom_at i (wTop i) z.2 (bandW_subset i hz1') (bandW_subset i hz1) hgt
            omega
        exact Prod.ext hn hat
      · -- different atoms: `z` would be bad
        exfalso
        refine hz.2 ?_
        refine Finset.mem_filter.2 ⟨hz.1, z'.2, fun h => hat h.symm, ?_⟩
        have hkeq : kIdx (gridAt i) z.1 z.2 = kIdx (gridAt i) z'.1 z'.2 := by omega
        rw [hkeq]
        exact activeIdx_kIdx (gridAt i) (bandW_subset i (Finset.mem_product.1 hz'.1).1) z'.2
  have hsub : (bandWPairs i).card ≤ ((bandWPairs i) \ (badWPairs i)).card + (badWPairs i).card := by
    have hb : badWPairs i ⊆ bandWPairs i := Finset.filter_subset _ _
    have := Finset.card_sdiff_add_card_eq_card hb
    omega
  omega

open Classical in
/-- **The overhangW, quantitatively**: at most `2|P_K| + 2|Atom|²`. -/
theorem overhangW_le_real (i : ℕ) :
    (((bandWPairs i).card - (winStartsW i).card : ℕ) : ℝ)
      ≤ 2 * ((PKtr i (wTop i)).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
  classical
  have hcard : ((badWPairs i).card : ℝ)
      ≤ 2 * ((PKtr i (wTop i)).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
    have hsplit : (badWPairs i).card
        ≤ ∑ α : (gridAt i).Atom,
            ((PKtr i (wTop i)).filter (fun n =>
              ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card := by
      classical
      have hsub : badWPairs i ⊆ (Finset.univ : Finset (gridAt i).Atom).biUnion
          (fun α => ((PKtr i (wTop i)).filter (fun n =>
            ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).image
              (fun n => (n, α))) := by
        intro z hz
        rw [badWPairs, Finset.mem_filter] at hz
        obtain ⟨hz1, hz2⟩ := hz
        refine Finset.mem_biUnion.2 ⟨z.2, Finset.mem_univ _, ?_⟩
        refine Finset.mem_image.2 ⟨z.1, ?_, rfl⟩
        exact Finset.mem_filter.2 ⟨bandW_subset i (Finset.mem_product.1 hz1).1, hz2⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_biUnion_le) ?_
      exact Finset.sum_le_sum fun α _ => Finset.card_image_le
    have hterm : ∀ α : (gridAt i).Atom,
        (((PKtr i (wTop i)).filter (fun n =>
          ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card : ℝ)
          ≤ 2 * ((PKtr i (wTop i)).card : ℝ) / (Fintype.card (gridAt i).Atom : ℝ)
            + 2 * (Fintype.card (gridAt i).Atom : ℝ) := fun α => card_multi_atom_le_real_at i (wTop i) (two_P₀_le_of_wgate (wgate_wTop i)) α
    have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
      have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
      exact_mod_cast this
    have hsum : ((badWPairs i).card : ℝ)
        ≤ ∑ _α : (gridAt i).Atom, (2 * ((PKtr i (wTop i)).card : ℝ)
            / (Fintype.card (gridAt i).Atom : ℝ)
            + 2 * (Fintype.card (gridAt i).Atom : ℝ)) := by
      have hsplitR : ((badWPairs i).card : ℝ)
          ≤ ∑ α : (gridAt i).Atom,
              ((((PKtr i (wTop i)).filter (fun n =>
                ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card : ℕ) : ℝ) := by
        exact_mod_cast hsplit
      exact le_trans hsplitR (Finset.sum_le_sum fun α _ => hterm α)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hexp : (Fintype.card (gridAt i).Atom : ℝ)
        * (2 * ((PKtr i (wTop i)).card : ℝ) / (Fintype.card (gridAt i).Atom : ℝ)
          + 2 * (Fintype.card (gridAt i).Atom : ℝ))
        = 2 * ((PKtr i (wTop i)).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
      field_simp
    rw [hexp] at hsum
    exact hsum
  refine le_trans ?_ hcard
  exact_mod_cast overhangW_le i

/-! ### Each band dwarfs everything before it -/

open Classical in
/-- Distinct sample times give distinct window starts at any fixed atom, so the band has at
least `|bandW i|` distinct starts. -/
theorem card_bandW_le_winStartsW (i : ℕ) : (bandW i).card ≤ (winStartsW i).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun n => 2 * kIdx (gridAt i) n (Classical.arbitrary _))
    ?_ ?_
  · intro n hn
    exact (mem_winStartsW i).2 ⟨n, hn, Classical.arbitrary _, rfl⟩
  · intro n hn n' hn' heq
    simp only at heq
    by_contra hne
    have hkk : 0 < kk i := by unfold kk; omega
    rcases Nat.lt_or_ge n n' with hlt | hge
    · have := window_gap_same_atom_at i (wTop i) (Classical.arbitrary _)
        (bandW_subset i hn) (bandW_subset i hn') hlt
      omega
    · have hgt : n' < n := by omega
      have := window_gap_same_atom_at i (wTop i) (Classical.arbitrary _)
        (bandW_subset i hn') (bandW_subset i hn) hgt
      omega

open Classical in
/-- The band has at most `|bandW i|·|Atom|` distinct starts. -/
theorem card_winStartsW_le (i : ℕ) :
    (winStartsW i).card ≤ (bandW i).card * Fintype.card (gridAt i).Atom := by
  classical
  rw [winStartsW_eq_image]
  refine le_trans Finset.card_image_le ?_
  rw [bandWPairs, Finset.card_product, Finset.card_univ]

set_option maxHeartbeats 1000000 in
/-- **Each band dwarfs the previous one**, with the next window length as the factor. -/
theorem fLW_step (j : ℕ) : (kk (j + 1) : ℝ) * (fLW j : ℝ) ≤ 2 * (fLW (j + 1) : ℝ) := by
  have hA : (1 : ℝ) ≤ (Fintype.card (gridAt j).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt j).Atom := Fintype.card_pos
    exact_mod_cast this
  have hPj : (0 : ℝ) ≤ ((PKtr j (wTop j)).card : ℝ) := Nat.cast_nonneg _
  have hkkj : (0 : ℝ) ≤ (kk j : ℝ) := Nat.cast_nonneg _
  have hband : ((bandW j).card : ℝ) ≤ ((PKtr j (wTop j)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (bandW_subset j)
  have hws : ((winStartsW j).card : ℝ)
      ≤ ((bandW j).card : ℝ) * (Fintype.card (gridAt j).Atom : ℝ) := by
    have h := card_winStartsW_le j
    exact_mod_cast h
  have hbl : (fLW j : ℝ) = ((winStartsW j).card : ℝ) * (kk j : ℝ) := by
    show ((((winStartsW j).card * kk j : ℕ)) : ℝ) = _
    push_cast; ring
  have h1 : (fLW j : ℝ)
      ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PKtr j (wTop j)).card : ℝ) * (kk j : ℝ) := by
    rw [hbl]
    have hstep : ((winStartsW j).card : ℝ)
        ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PKtr j (wTop j)).card : ℝ) := by
      nlinarith [hws, hband, hA, hPj]
    exact mul_le_mul_of_nonneg_right hstep hkkj
  have h2 := granuleW_exceeds_previous_scale j
  have h3 : ((PKtr (j + 1) (wTop (j + 1))).card : ℝ) ≤ 2 * ((bandW (j + 1)).card : ℝ) := card_bandW_ge (j + 1)
  have h3' : ((bandW (j + 1)).card : ℝ) ≤ ((winStartsW (j + 1)).card : ℝ) := by
    have := card_bandW_le_winStartsW (j + 1)
    exact_mod_cast this
  have hkk1 : (0 : ℝ) ≤ (kk (j + 1) : ℝ) := Nat.cast_nonneg _
  have h4 : (fLW (j + 1) : ℝ) = ((winStartsW (j + 1)).card : ℝ) * (kk (j + 1) : ℝ) := by
    show ((((winStartsW (j + 1)).card * kk (j + 1) : ℕ)) : ℝ) = _
    push_cast; ring
  rw [h4]
  nlinarith [h1, h2, h3, h3', hkk1]

/-- **The history is a `4/m_i` fraction of band `i`.** -/
theorem fTW_kk_le (i : ℕ) : (fTW i : ℝ) * (kk i : ℝ) ≤ 4 * (fLW i : ℝ) := by
  induction i with
  | zero =>
      have h0 : ((fTW 0 : ℕ) : ℝ) = 0 := by norm_num [fTW]
      rw [h0]
      have : (0 : ℝ) ≤ (fLW 0 : ℝ) := Nat.cast_nonneg _
      linarith
  | succ i ih =>
      have hstep := fLW_step i
      have hbT : (fTW (i + 1) : ℝ) = (fTW i : ℝ) + (fLW i : ℝ) := by
        show ((fTW i + fLW i : ℕ) : ℝ) = _
        push_cast; ring
      have hkki := kk_ge_real' i
      have hkki1 := kk_ge_real' (i + 1)
      have hTnn : (0 : ℝ) ≤ (fTW i : ℝ) := Nat.cast_nonneg _
      have hLnn : (0 : ℝ) ≤ (fLW i : ℝ) := Nat.cast_nonneg _
      have hTm : (fTW i : ℝ) * (kk (i + 1) : ℝ) * (kk i : ℝ) ≤ 8 * (fLW (i + 1) : ℝ) := by
        have h1 : (fTW i : ℝ) * (kk (i + 1) : ℝ) * (kk i : ℝ)
            = ((fTW i : ℝ) * (kk i : ℝ)) * (kk (i + 1) : ℝ) := by ring
        rw [h1]
        calc ((fTW i : ℝ) * (kk i : ℝ)) * (kk (i + 1) : ℝ)
            ≤ (4 * (fLW i : ℝ)) * (kk (i + 1) : ℝ) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = 4 * ((kk (i + 1) : ℝ) * (fLW i : ℝ)) := by ring
          _ ≤ 4 * (2 * (fLW (i + 1) : ℝ)) := by linarith
          _ = 8 * (fLW (i + 1) : ℝ) := by ring
      rw [hbT]
      have hLnn1 : (0 : ℝ) ≤ (fLW (i + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith [hTm, hstep, hkki, hkki1, hLnn1]

/-! ### The overhangW fraction vanishes -/
/-- **The overhangW fraction vanishes**: `ov_i / |bandWPairs i| ≤ 8/|Atom_i| → 0`. -/
theorem overhangW_frac_le (i : ℕ) :
    (((bandWPairs i).card - (winStartsW i).card : ℕ) : ℝ)
      ≤ 8 / (Fintype.card (gridAt i).Atom : ℝ) * ((bandWPairs i).card : ℝ) := by
  have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hov := overhangW_le_real i
  have hPsq := card_Atom_sq_le_PKW i
  have hB : ((bandWPairs i).card : ℝ)
      = ((bandW i).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
    have hnat : (bandWPairs i).card = (bandW i).card * Fintype.card (gridAt i).Atom := by
      rw [bandWPairs, Finset.card_product, Finset.card_univ]
    rw [hnat]
    push_cast
    ring
  have hT : ((PKtr i (wTop i)).card : ℝ) ≤ 2 * ((bandW i).card : ℝ) := card_bandW_ge i
  have hTnn : (0 : ℝ) ≤ ((bandW i).card : ℝ) := Nat.cast_nonneg _
  have hPnn : (0 : ℝ) ≤ ((PKtr i (wTop i)).card : ℝ) := Nat.cast_nonneg _
  rw [hB]
  -- `ov ≤ 2|PK| + 2|Atom|² ≤ 4|bandW| + 2|PK| ≤ 8|bandW|`
  have hstep : (((bandWPairs i).card - (winStartsW i).card : ℕ) : ℝ)
      ≤ 8 * ((bandW i).card : ℝ) := by
    have h1 : 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 ≤ 2 * ((PKtr i (wTop i)).card : ℝ) := by
      linarith [hPsq]
    linarith [hov, h1, hT]
  have hfrac : 8 * ((bandW i).card : ℝ)
      = 8 / (Fintype.card (gridAt i).Atom : ℝ)
        * (((bandW i).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)) := by
    field_simp
  linarith [hstep, hfrac]

/-! ### The pair count is the sum over pairs of the window count -/

open Classical in
/-- The `(n, α, p)` count of `tendsto_bandW_occursCount`, re-summed over the band pairs. -/
theorem pairCountW_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
        ((bandW i).filter fun n =>
          OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
      = ∑ z ∈ bandWPairs i, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2) := by
  classical
  have hL : ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
        ((bandW i).filter fun n =>
          OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
      = ∑ α : (gridAt i).Atom, ∑ p ∈ Finset.range (kk i - v.length + 1),
          ∑ n ∈ bandW i,
            (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun p =>
      ∑ n ∈ bandW i, (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hR : ∑ z ∈ bandWPairs i, winOccW i x v (2 * kIdx (gridAt i) z.1 z.2)
      = ∑ n ∈ bandW i, ∑ α : (gridAt i).Atom,
          ∑ p ∈ Finset.range (kk i - v.length + 1),
            (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0) := by
    rw [bandWPairs, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun α _ => ?_
    rw [winOccW, Finset.card_filter]
  rw [hL, hR]
  rw [Finset.sum_congr rfl (fun (α : (gridAt i).Atom) _ =>
    Finset.sum_comm (s := Finset.range (kk i - v.length + 1)) (t := bandW i)
      (f := fun p n => if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0))]
  exact Finset.sum_comm


/-- The cutoffs are cofinal, so `tendsto_fullRead_freq` speaks about arbitrarily long prefixes. -/
theorem tendsto_fTW_atTop : Tendsto (fun i => (fTW i : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
  have : i ≤ fTW i := self_le_fTW i
  exact_mod_cast this



end NormalNumbers.G4.Sched
