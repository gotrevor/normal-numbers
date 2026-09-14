/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandFull
import NormalNumbers.G4EntropyBandSeq

/-!
# Entropy expedition — the schedule-only band read

`G4EntropyBandSeq`'s read picks one *good atom* per scale, which depends on `G₄`'s entropy data.
With `windows_eq_or_disjoint` (`Q ∣ P₀`) the read can take the **whole** sample's windows in a
band, and everything becomes schedule-only.

* `winStarts i` — the band-`i` window starts, as a `Finset`: `{2·kIdx(n,α) : n ∈ bandT i, α}`.
  A *set*, so coinciding windows are counted once; `windows_eq_or_disjoint` makes distinct
  elements at least `m_i` apart.
* `fnth i a` — the `a`-th of them, in increasing order.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The band's window starts -/

open Classical in
/-- The distinct window starts of band `i`. -/
noncomputable def winStarts (i : ℕ) : Finset ℕ :=
  ((bandT i) ×ˢ (Finset.univ : Finset (gridAt i).Atom)).image
    (fun z => 2 * kIdx (gridAt i) z.1 z.2)

open Classical in
lemma mem_winStarts (i : ℕ) {q : ℕ} :
    q ∈ winStarts i ↔ ∃ n ∈ bandT i, ∃ α : (gridAt i).Atom, q = 2 * kIdx (gridAt i) n α := by
  classical
  rw [winStarts, Finset.mem_image]
  constructor
  · rintro ⟨⟨n, α⟩, hz, rfl⟩
    exact ⟨n, (Finset.mem_product.1 hz).1, α, rfl⟩
  · rintro ⟨n, hn, α, rfl⟩
    exact ⟨(n, α), Finset.mem_product.2 ⟨hn, Finset.mem_univ _⟩, rfl⟩

lemma winStarts_nonempty (i : ℕ) : (winStarts i).Nonempty := by
  classical
  obtain ⟨n, hn⟩ := bandT_nonempty i
  exact ⟨2 * kIdx (gridAt i) n (Classical.arbitrary _),
    (mem_winStarts i).2 ⟨n, hn, Classical.arbitrary _, rfl⟩⟩

lemma card_winStarts_pos (i : ℕ) : 0 < (winStarts i).card :=
  Finset.card_pos.2 (winStarts_nonempty i)

/-- **Distinct window starts are a full window apart.**  This is `windows_eq_or_disjoint` read on
the `Finset` of starts. -/
theorem winStarts_gap (i : ℕ) {q q' : ℕ} (hq : q ∈ winStarts i) (hq' : q' ∈ winStarts i)
    (hlt : q < q') : q + kk i ≤ q' := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStarts i).1 hq
  obtain ⟨n', hn', β, rfl⟩ := (mem_winStarts i).1 hq'
  rcases windows_eq_or_disjoint i (bandT_subset i hn) (bandT_subset i hn') α β with h | h | h
  · omega
  · exact h
  · omega

/-- Every band-`i` window start is above the band floor. -/
lemma bandLo_le_winStarts (i : ℕ) {q : ℕ} (hq : q ∈ winStarts i) : bandLo i ≤ q := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStarts i).1 hq
  exact bandLo_le_pos_of_mem_bandT i hn α

/-- Every band-`i` window lies below the band ceiling. -/
lemma winStarts_add_lt_bandTop (i : ℕ) {q : ℕ} (hq : q ∈ winStarts i) {p : ℕ} (hp : p < kk i) :
    q + p < bandTop i := by
  classical
  obtain ⟨n, hn, α, rfl⟩ := (mem_winStarts i).1 hq
  exact pos_lt_bandTop i (bandT_subset i hn) α hp

/-! ### Enumerating them -/

/-- The `a`-th window start of band `i`, in increasing order (cyclically extended). -/
noncomputable def fnth (i a : ℕ) : ℕ :=
  (winStarts i).orderEmbOfFin rfl ⟨a % (winStarts i).card, Nat.mod_lt _ (card_winStarts_pos i)⟩

lemma fnth_mem (i a : ℕ) : fnth i a ∈ winStarts i := by
  rw [fnth]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma fnth_lt_fnth {i a b : ℕ} (hab : a < b) (hb : b < (winStarts i).card) :
    fnth i a < fnth i b := by
  have ha : a < (winStarts i).card := lt_trans hab hb
  rw [fnth, fnth]
  refine (Finset.orderEmbOfFin (winStarts i) rfl).strictMono ?_
  refine Fin.mk_lt_mk.2 ?_
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact hab

/-- **Consecutive window starts are a full window apart.** -/
lemma fnth_gap {i a b : ℕ} (hab : a < b) (hb : b < (winStarts i).card) :
    fnth i a + kk i ≤ fnth i b :=
  winStarts_gap i (fnth_mem i a) (fnth_mem i b) (fnth_lt_fnth hab hb)

lemma bandLo_le_fnth (i a : ℕ) : bandLo i ≤ fnth i a :=
  bandLo_le_winStarts i (fnth_mem i a)

lemma fnth_add_lt_bandTop (i a : ℕ) {p : ℕ} (hp : p < kk i) : fnth i a + p < bandTop i :=
  winStarts_add_lt_bandTop i (fnth_mem i a) hp

/-! ### The schedule-only position map -/

/-- The number of digits band `i` contributes to the schedule-only read. -/
noncomputable def fL (i : ℕ) : ℕ := (winStarts i).card * kk i

lemma fL_pos (i : ℕ) : 0 < fL i :=
  Nat.mul_pos (card_winStarts_pos i) (by unfold kk; omega)

/-- The cutoff after the first `i` bands. -/
noncomputable def fT : ℕ → ℕ
  | 0 => 0
  | (i + 1) => fT i + fL i

lemma fT_lt_succ (i : ℕ) : fT i < fT (i + 1) := by
  have := fL_pos i
  show fT i < fT i + fL i
  omega

lemma fT_mono : Monotone fT := monotone_nat_of_le_succ fun i => (fT_lt_succ i).le

lemma self_le_fT (i : ℕ) : i ≤ fT i := by
  induction i with
  | zero => simp [fT]
  | succ i ih => have := fT_lt_succ i; omega

/-- The band a read index belongs to. -/
noncomputable def fgrp (j : ℕ) : ℕ := Nat.findGreatest (fun m => fT m ≤ j) j

lemma fgrp_eq {i j : ℕ} (h1 : fT i ≤ j) (h2 : j < fT (i + 1)) : fgrp j = i := by
  classical
  have hij : i ≤ j := le_trans (self_le_fT i) h1
  have hle : i ≤ fgrp j := Nat.le_findGreatest hij h1
  by_contra hne
  have hlt : i < fgrp j := lt_of_le_of_ne hle (Ne.symm hne)
  have hspec : fT (fgrp j) ≤ j := Nat.findGreatest_spec (P := fun m => fT m ≤ j) hij h1
  have : fT (i + 1) ≤ fT (fgrp j) := fT_mono (by omega)
  omega

lemma fT_fgrp_le (j : ℕ) : fT (fgrp j) ≤ j := by
  classical
  exact Nat.findGreatest_spec (P := fun m => fT m ≤ j) (Nat.zero_le j) (by simp [fT])

lemma lt_fT_fgrp_succ (j : ℕ) : j < fT (fgrp j + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have h1 : fgrp j + 1 ≤ j := le_trans (self_le_fT (fgrp j + 1)) hcon
  have h2 : fgrp j + 1 ≤ fgrp j := Nat.le_findGreatest h1 hcon
  omega

/-- **The schedule-only position map.**  Bands in order; inside a band, the distinct window
starts in order; inside a window, the `m_i` consecutive positions.  No reference to `G₄`. -/
noncomputable def fullPos (j : ℕ) : ℕ :=
  fnth (fgrp j) ((j - fT (fgrp j)) / kk (fgrp j)) + (j - fT (fgrp j)) % kk (fgrp j)

lemma fullPos_eq {i j : ℕ} (h1 : fT i ≤ j) (h2 : j < fT (i + 1)) :
    fullPos j = fnth i ((j - fT i) / kk i) + (j - fT i) % kk i := by
  rw [fullPos, fgrp_eq h1 h2]

/-- **The schedule-only read is a genuine subsequence.** -/
theorem fullPos_strictMono : StrictMono fullPos := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  set i := fgrp j with hi
  have h1 : fT i ≤ j := fT_fgrp_le j
  have h2 : j < fT (i + 1) := lt_fT_fgrp_succ j
  have hfT : fT (i + 1) = fT i + fL i := rfl
  set r : ℕ := j - fT i with hr
  have hrlt : r < fL i := by omega
  have hkk : 0 < kk i := by unfold kk; omega
  set a : ℕ := r / kk i with ha
  set p : ℕ := r % kk i with hp
  have hpk : p < kk i := Nat.mod_lt _ hkk
  have hra : r = a * kk i + p := (Nat.div_add_mod' r (kk i)).symm
  have hacard : a < (winStarts i).card := by
    by_contra hcon
    push_neg at hcon
    have : (winStarts i).card * kk i ≤ a * kk i := Nat.mul_le_mul_right _ hcon
    rw [fL] at hrlt
    omega
  have hj : fullPos j = fnth i a + p := fullPos_eq h1 h2
  rcases Nat.lt_or_ge (p + 1) (kk i) with hcase | hcase
  · have hr1 : j + 1 - fT i = r + 1 := by omega
    have hlt1 : j + 1 < fT (i + 1) := by
      rw [hfT, fL]
      have : (a + 1) * kk i ≤ (winStarts i).card * kk i := Nat.mul_le_mul_right _ hacard
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
    have := fullPos_eq (i := i) (j := j + 1) (by omega) hlt1
    rw [this, hr1, hdiv, hmod, hj]
    omega
  · have hpk1 : p + 1 = kk i := by omega
    rcases Nat.lt_or_ge (a + 1) (winStarts i).card with hcase2 | hcase2
    · have hr1 : j + 1 - fT i = r + 1 := by omega
      have hreq : r + 1 = (a + 1) * kk i := by
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hlt1 : j + 1 < fT (i + 1) := by
        rw [hfT, fL]
        have : (a + 1) * kk i < (winStarts i).card * kk i :=
          Nat.mul_lt_mul_of_lt_of_le hcase2 (le_refl _) hkk
        omega
      have hdiv : (r + 1) / kk i = a + 1 := by rw [hreq, Nat.mul_div_cancel _ hkk]
      have hmod : (r + 1) % kk i = 0 := by rw [hreq, Nat.mul_mod_left]
      have heq := fullPos_eq (i := i) (j := j + 1) (by omega) hlt1
      rw [heq, hr1, hdiv, hmod, hj]
      have hgap := fnth_gap (i := i) (a := a) (b := a + 1) (by omega) hcase2
      omega
    · have hacard' : a + 1 = (winStarts i).card := by omega
      have hreq : r + 1 = fL i := by
        rw [fL, ← hacard']
        have : (a + 1) * kk i = a * kk i + kk i := by ring
        omega
      have hj1 : j + 1 = fT (i + 1) := by rw [hfT]; omega
      have hlt2 : fT (i + 1) ≤ j + 1 := by omega
      have hlt3 : j + 1 < fT (i + 1 + 1) := by
        have := fT_lt_succ (i + 1)
        omega
      have heq := fullPos_eq (i := i + 1) (j := j + 1) hlt2 hlt3
      have hzero : j + 1 - fT (i + 1) = 0 := by omega
      rw [heq, hzero, Nat.zero_div, Nat.zero_mod, hj]
      have hup : bandLo (i + 1) ≤ fnth (i + 1) 0 := bandLo_le_fnth (i + 1) 0
      have hlo : bandLo (i + 1) = bandTop i := rfl
      have hdown : fnth i a + p < bandTop i := fnth_add_lt_bandTop i a hpk
      omega

/-! ### The digits read, and the window dictionary -/

/-- The digit sequence read along `fullPos`. -/
noncomputable def fullDig (x : ℝ) (j : ℕ) : ℕ := digitOf 2 (Int.fract x) (fullPos j)

lemma fullDig_lt (x : ℝ) (j : ℕ) : fullDig x j < 2 := Nat.mod_lt _ (by omega)

/-- Inside band `i`, the `a`-th window occupies the read indices `fT i + a·m_i + q`. -/
lemma fullPos_window (i a q : ℕ) (ha : a < (winStarts i).card) (hq : q < kk i) :
    fullPos (fT i + a * kk i + q) = fnth i a + q := by
  have hkk : 0 < kk i := by unfold kk; omega
  have hlt : a * kk i + q < fL i := by
    rw [fL]
    have : (a + 1) * kk i ≤ (winStarts i).card * kk i := Nat.mul_le_mul_right _ ha
    have hexp : (a + 1) * kk i = a * kk i + kk i := by ring
    omega
  have h1 : fT i ≤ fT i + a * kk i + q := by omega
  have h2 : fT i + a * kk i + q < fT (i + 1) := by
    show fT i + a * kk i + q < fT i + fL i
    omega
  have hsub : fT i + a * kk i + q - fT i = a * kk i + q := by omega
  have hdiv : (a * kk i + q) / kk i = a := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_div hkk, Nat.div_eq_of_lt hq]
    omega
  have hmod : (a * kk i + q) % kk i = q := by
    have hc : a * kk i + q = kk i * a + q := by ring
    rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  rw [fullPos_eq h1 h2, hsub, hdiv, hmod]

/-- **The dictionary**: a window of `v` fitting inside one band window is an occurrence of `v`
in `x` at the corresponding digit position. -/
lemma matchesAt_fullDig_iff (x : ℝ) (i a q : ℕ) (v : List ℕ) (ha : a < (winStarts i).card)
    (hq : q + v.length ≤ kk i) :
    MatchesAt (fullDig x) v (fT i + a * kk i + q) ↔ OccursAt 2 x v (fnth i a + q) := by
  have hkey : ∀ t < v.length,
      fullDig x (fT i + a * kk i + q + t) = digitOf 2 (Int.fract x) (fnth i a + q + t) := by
    intro t ht
    have hqt : q + t < kk i := by omega
    have hrw : fT i + a * kk i + q + t = fT i + a * kk i + (q + t) := by ring
    rw [fullDig, hrw, fullPos_window i a (q + t) ha hqt]
    ring_nf
  constructor
  · intro h t ht
    have h' := h t ht
    rw [hkey t ht] at h'
    rw [h']
    exact (List.getD_eq_getElem v 0 ht)
  · intro h t ht
    show fullDig x (fT i + a * kk i + q + t) = _
    rw [hkey t ht, h t ht]
    exact (List.getD_eq_getElem v 0 ht).symm

set_option maxHeartbeats 1000000 in
/-- Summing over the band's window-start enumeration is summing over the starts. -/
lemma sum_range_fnth {β : Type*} [AddCommMonoid β] (i : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (winStarts i).card, g (fnth i a) = ∑ q ∈ winStarts i, g q := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun a => g (fnth i a))]
  have hstep : ∀ a : Fin (winStarts i).card,
      g (fnth i (a : ℕ)) = g ((winStarts i).orderEmbOfFin rfl a) := by
    intro a
    have hfin : (⟨(a : ℕ) % (winStarts i).card, Nat.mod_lt _ (card_winStarts_pos i)⟩ :
        Fin (winStarts i).card) = a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    rw [fnth, hfin]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  rw [← Finset.sum_attach (winStarts i) g]
  refine Fintype.sum_bijective (fun a : Fin (winStarts i).card =>
    (⟨(winStarts i).orderEmbOfFin rfl a, Finset.orderEmbOfFin_mem _ _ _⟩ :
      (winStarts i : Finset ℕ))) ?_ _ _ (fun a => rfl)
  constructor
  · intro a b hab
    have : ((winStarts i).orderEmbOfFin rfl a : ℕ) = (winStarts i).orderEmbOfFin rfl b :=
      congrArg Subtype.val hab
    exact (winStarts i).orderEmbOfFin rfl |>.injective (by exact_mod_cast this)
  · rintro ⟨q, hq⟩
    have hrange : q ∈ Set.range ((winStarts i).orderEmbOfFin (rfl : (winStarts i).card = _)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hq
    obtain ⟨a, ha⟩ := hrange
    exact ⟨a, Subtype.ext ha⟩

/-! ### The read count over a band -/

open Classical in
/-- The number of fitting in-window occurrences of `v` in band `i`'s distinct windows. -/
noncomputable def fullGood (i : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ a ∈ Finset.range (winStarts i).card,
    ((Finset.range (kk i - v.length + 1)).filter
      (fun q => OccursAt 2 x v (fnth i a + q))).card

open Classical in
/-- `fullGood` re-summed over the band's window starts. -/
theorem fullGood_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    fullGood i x v
      = ∑ q ∈ winStarts i,
          ((Finset.range (kk i - v.length + 1)).filter
            (fun p => OccursAt 2 x v (q + p))).card :=
  sum_range_fnth i (fun q =>
    ((Finset.range (kk i - v.length + 1)).filter (fun p => OccursAt 2 x v (q + p))).card)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The band's contribution to the schedule-only read count**, up to one word length per
window. -/
theorem full_band_winCount_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) :
    fullGood i x v
        ≤ ((Finset.Ico (fT i) (fT (i + 1))).filter (MatchesAt (fullDig x) v)).card ∧
      ((Finset.Ico (fT i) (fT (i + 1))).filter (MatchesAt (fullDig x) v)).card
        ≤ fullGood i x v + (winStarts i).card * v.length := by
  classical
  have hbT : fT (i + 1) = fT i + fL i := rfl
  have hsplit : ((Finset.Ico (fT i) (fT (i + 1))).filter (MatchesAt (fullDig x) v)).card
      = ∑ a ∈ Finset.range (winStarts i).card,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (fullDig x) v (fT i + (a * kk i + q)))).card := by
    rw [hbT, card_Ico_shift _ (fT i) (fL i), fL, card_filter_range_mul]
  rw [hsplit]
  have hper : ∀ a ∈ Finset.range (winStarts i).card,
      ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnth i a + q))).card
        ≤ ((Finset.range (kk i)).filter
          (fun q => MatchesAt (fullDig x) v (fT i + (a * kk i + q)))).card ∧
      ((Finset.range (kk i)).filter
          (fun q => MatchesAt (fullDig x) v (fT i + (a * kk i + q)))).card
        ≤ ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnth i a + q))).card + v.length := by
    intro a ha
    have ha' : a < (winStarts i).card := Finset.mem_range.1 ha
    have hcongr : ((Finset.range (kk i - v.length + 1)).filter
        (fun q => MatchesAt (fullDig x) v (fT i + (a * kk i + q)))).card
        = ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnth i a + q))).card := by
      congr 1
      refine Finset.filter_congr fun q hq => ?_
      have hqfit : q + v.length ≤ kk i := by
        have := Finset.mem_range.1 hq
        omega
      have hassoc : fT i + (a * kk i + q) = fT i + a * kk i + q := by ring
      rw [hassoc]
      simpa using matchesAt_fullDig_iff x i a q v ha' hqfit
    have h := card_filter_fit
      (fun q => MatchesAt (fullDig x) v (fT i + (a * kk i + q))) (m := kk i)
      (ℓ := v.length) hv hvm
    rw [hcongr] at h
    exact h
  constructor
  · exact Finset.sum_le_sum fun a ha => (hper a ha).1
  · calc ∑ a ∈ Finset.range (winStarts i).card,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (fullDig x) v (fT i + (a * kk i + q)))).card
        ≤ ∑ a ∈ Finset.range (winStarts i).card,
            (((Finset.range (kk i - v.length + 1)).filter
              (fun q => OccursAt 2 x v (fnth i a + q))).card + v.length) :=
          Finset.sum_le_sum fun a ha => (hper a ha).2
      _ = fullGood i x v + (winStarts i).card * v.length := by
          rw [Finset.sum_add_distrib, fullGood]
          simp [mul_comm]

set_option maxHeartbeats 1000000 in
open Classical in
/-- The full read count at the band cutoffs. -/
theorem full_winCount_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) :
    fullGood i x v ≤ winCount (fullDig x) v (fT (i + 1)) ∧
      winCount (fullDig x) v (fT (i + 1))
        ≤ fullGood i x v + fT i + (winStarts i).card * v.length := by
  classical
  have hsplit := winCount_split (fullDig x) v (fT_mono (Nat.le_succ i))
  simp only [Nat.succ_eq_add_one] at hsplit
  obtain ⟨h1, h2⟩ := full_band_winCount_bounds x i v hv hvm
  have hhist : winCount (fullDig x) v (fT i) ≤ fT i := winCount_le _ _ _
  generalize hc : (winStarts i).card * v.length = c at h2 ⊢
  rw [hsplit]
  omega

/-! ### From distinct windows to `(n, α)` pairs: the multiplicity bridge -/

open Classical in
/-- The window-occurrence count of one window start. -/
noncomputable def winOcc (i : ℕ) (x : ℝ) (v : List ℕ) (q : ℕ) : ℕ :=
  ((Finset.range (kk i - v.length + 1)).filter (fun p => OccursAt 2 x v (q + p))).card

lemma winOcc_le (i : ℕ) (x : ℝ) (v : List ℕ) (q : ℕ) :
    winOcc i x v q ≤ kk i - v.length + 1 := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [winOcc]

open Classical in
/-- The band's `(n, α)` pairs. -/
noncomputable def bandPairs (i : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  (bandT i) ×ˢ (Finset.univ : Finset (gridAt i).Atom)

open Classical in
lemma winStarts_eq_image (i : ℕ) :
    winStarts i = (bandPairs i).image (fun z => 2 * kIdx (gridAt i) z.1 z.2) := rfl

open Classical in
/-- **The pair sum is the multiplicity-weighted start sum.** -/
theorem sum_pairs_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    ∑ z ∈ bandPairs i, winOcc i x v (2 * kIdx (gridAt i) z.1 z.2)
      = ∑ q ∈ winStarts i,
          ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card
            * winOcc i x v q := by
  classical
  rw [winStarts_eq_image]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := bandPairs i) (t := (bandPairs i).image (fun z => 2 * kIdx (gridAt i) z.1 z.2))
    (g := fun z => 2 * kIdx (gridAt i) z.1 z.2)
    (fun z hz => Finset.mem_image_of_mem _ hz)
    (fun z => winOcc i x v (2 * kIdx (gridAt i) z.1 z.2))
  rw [← hfib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hcongr : ∀ z ∈ (bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q),
      winOcc i x v (2 * kIdx (gridAt i) z.1 z.2) = winOcc i x v q := by
    intro z hz
    rw [(Finset.mem_filter.1 hz).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]

open Classical in
/-- Each fiber is nonempty, so the excess `|pairs| − |starts|` is the total multiplicity
overhang. -/
theorem card_bandPairs_sub (i : ℕ) :
    (winStarts i).card ≤ (bandPairs i).card := by
  classical
  rw [winStarts_eq_image]
  exact Finset.card_image_le

open Classical in
/-- **The pair sum exceeds the start sum by at most the overhang, times the window length.** -/
theorem sum_pairs_sub_le (i : ℕ) (x : ℝ) (v : List ℕ) :
    ∑ q ∈ winStarts i, winOcc i x v q ≤ ∑ z ∈ bandPairs i,
        winOcc i x v (2 * kIdx (gridAt i) z.1 z.2) ∧
      ∑ z ∈ bandPairs i, winOcc i x v (2 * kIdx (gridAt i) z.1 z.2)
        ≤ ∑ q ∈ winStarts i, winOcc i x v q
          + ((bandPairs i).card - (winStarts i).card) * (kk i - v.length + 1) := by
  classical
  rw [sum_pairs_eq i x v]
  have hfib : ∀ q ∈ winStarts i,
      1 ≤ ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card := by
    intro q hq
    rw [winStarts_eq_image, Finset.mem_image] at hq
    obtain ⟨z, hz, hzq⟩ := hq
    exact Finset.card_pos.2 ⟨z, Finset.mem_filter.2 ⟨hz, hzq⟩⟩
  have hsumfib : ∑ q ∈ winStarts i,
      ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card
      = (bandPairs i).card := by
    rw [winStarts_eq_image]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun z hz => Finset.mem_image_of_mem _ hz)).symm
  constructor
  · refine Finset.sum_le_sum fun q hq => ?_
    have hc := hfib q hq
    exact Nat.le_mul_of_pos_left _ (by omega)
  · have hterm : ∀ q ∈ winStarts i,
        ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card
            * winOcc i x v q
          ≤ winOcc i x v q
            + (((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
              * (kk i - v.length + 1) := by
      intro q hq
      have h1 := hfib q hq
      have h2 := winOcc_le i x v q
      set c := ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card with hc
      have hc1 : c - 1 + 1 = c := by omega
      calc c * winOcc i x v q = ((c - 1) + 1) * winOcc i x v q := by rw [hc1]
        _ = winOcc i x v q + (c - 1) * winOcc i x v q := by ring
        _ ≤ winOcc i x v q + (c - 1) * (kk i - v.length + 1) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    have hsub : ∑ q ∈ winStarts i,
        (((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
        ≤ (bandPairs i).card - (winStarts i).card := by
      have hle : ∑ q ∈ winStarts i, 1 ≤ ∑ q ∈ winStarts i,
          ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card :=
        Finset.sum_le_sum hfib
      have hcards : ∑ q ∈ winStarts i, (1 : ℕ) = (winStarts i).card := by simp
      have hsplit : ∑ q ∈ winStarts i,
          (((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card - 1)
          = (∑ q ∈ winStarts i,
              ((bandPairs i).filter (fun z => 2 * kIdx (gridAt i) z.1 z.2 = q)).card)
            - ∑ q ∈ winStarts i, 1 := by
        rw [← Finset.sum_tsub_distrib]
        exact fun q hq => hfib q hq
      rw [hsplit, hsumfib, hcards]
    exact hsub

/-! ### The overhang is a vanishing fraction -/

open Classical in
/-- The band pairs whose window is shared with another atom. -/
noncomputable def badPairs (i : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  (bandPairs i).filter (fun z => ∃ β, β ≠ z.2 ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) z.1 z.2))

open Classical in
/-- **The multiplicity overhang is at most the number of shared pairs.**  Off `badPairs` the
window-start map is injective. -/
theorem overhang_le (i : ℕ) :
    (bandPairs i).card - (winStarts i).card ≤ (badPairs i).card := by
  classical
  have hinj : ((bandPairs i) \ (badPairs i)).card ≤ (winStarts i).card := by
    refine Finset.card_le_card_of_injOn (fun z => 2 * kIdx (gridAt i) z.1 z.2) ?_ ?_
    · intro z hz
      simp only [Finset.coe_sdiff, Set.mem_diff] at hz
      have hz1 : z ∈ bandPairs i := hz.1
      exact (mem_winStarts i).2 ⟨z.1, (Finset.mem_product.1 hz1).1, z.2, rfl⟩
    · intro z hz z' hz' heq
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hz hz'
      simp only at heq
      by_cases hat : z.2 = z'.2
      · -- same atom: `n ↦ kIdx` is injective
        have hz1 : z.1 ∈ bandT i := (Finset.mem_product.1 hz.1).1
        have hz1' : z'.1 ∈ bandT i := (Finset.mem_product.1 hz'.1).1
        have hkk : 0 < kk i := by unfold kk; omega
        have heq' : 2 * kIdx (gridAt i) z.1 z.2 = 2 * kIdx (gridAt i) z'.1 z.2 := by
          rw [heq, ← hat]
        have hn : z.1 = z'.1 := by
          by_contra hne
          rcases Nat.lt_or_ge z.1 z'.1 with hlt | hge
          · have hg := window_gap_same_atom i z.2 (bandT_subset i hz1) (bandT_subset i hz1') hlt
            omega
          · have hgt : z'.1 < z.1 := by omega
            have hg := window_gap_same_atom i z.2 (bandT_subset i hz1') (bandT_subset i hz1) hgt
            omega
        exact Prod.ext hn hat
      · -- different atoms: `z` would be bad
        exfalso
        refine hz.2 ?_
        refine Finset.mem_filter.2 ⟨hz.1, z'.2, fun h => hat h.symm, ?_⟩
        have hkeq : kIdx (gridAt i) z.1 z.2 = kIdx (gridAt i) z'.1 z'.2 := by omega
        rw [hkeq]
        exact activeIdx_kIdx (gridAt i) (bandT_subset i (Finset.mem_product.1 hz'.1).1) z'.2
  have hsub : (bandPairs i).card ≤ ((bandPairs i) \ (badPairs i)).card + (badPairs i).card := by
    have hb : badPairs i ⊆ bandPairs i := Finset.filter_subset _ _
    have := Finset.card_sdiff_add_card_eq_card hb
    omega
  omega

open Classical in
/-- **The overhang, quantitatively**: at most `2|P_K| + 2|Atom|²`. -/
theorem overhang_le_real (i : ℕ) :
    (((bandPairs i).card - (winStarts i).card : ℕ) : ℝ)
      ≤ 2 * ((PK i).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
  classical
  have hcard : ((badPairs i).card : ℝ)
      ≤ 2 * ((PK i).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
    have hsplit : (badPairs i).card
        ≤ ∑ α : (gridAt i).Atom,
            ((PK i).filter (fun n =>
              ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card := by
      classical
      have hsub : badPairs i ⊆ (Finset.univ : Finset (gridAt i).Atom).biUnion
          (fun α => ((PK i).filter (fun n =>
            ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).image
              (fun n => (n, α))) := by
        intro z hz
        rw [badPairs, Finset.mem_filter] at hz
        obtain ⟨hz1, hz2⟩ := hz
        refine Finset.mem_biUnion.2 ⟨z.2, Finset.mem_univ _, ?_⟩
        refine Finset.mem_image.2 ⟨z.1, ?_, rfl⟩
        exact Finset.mem_filter.2 ⟨bandT_subset i (Finset.mem_product.1 hz1).1, hz2⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_biUnion_le) ?_
      exact Finset.sum_le_sum fun α _ => Finset.card_image_le
    have hterm : ∀ α : (gridAt i).Atom,
        (((PK i).filter (fun n =>
          ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card : ℝ)
          ≤ 2 * ((PK i).card : ℝ) / (Fintype.card (gridAt i).Atom : ℝ)
            + 2 * (Fintype.card (gridAt i).Atom : ℝ) := fun α => card_multi_atom_le_real i α
    have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
      have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
      exact_mod_cast this
    have hsum : ((badPairs i).card : ℝ)
        ≤ ∑ _α : (gridAt i).Atom, (2 * ((PK i).card : ℝ)
            / (Fintype.card (gridAt i).Atom : ℝ)
            + 2 * (Fintype.card (gridAt i).Atom : ℝ)) := by
      have hsplitR : ((badPairs i).card : ℝ)
          ≤ ∑ α : (gridAt i).Atom,
              ((((PK i).filter (fun n =>
                ∃ β, β ≠ α ∧ ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card : ℕ) : ℝ) := by
        exact_mod_cast hsplit
      exact le_trans hsplitR (Finset.sum_le_sum fun α _ => hterm α)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hexp : (Fintype.card (gridAt i).Atom : ℝ)
        * (2 * ((PK i).card : ℝ) / (Fintype.card (gridAt i).Atom : ℝ)
          + 2 * (Fintype.card (gridAt i).Atom : ℝ))
        = 2 * ((PK i).card : ℝ) + 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 := by
      field_simp
    rw [hexp] at hsum
    exact hsum
  refine le_trans ?_ hcard
  exact_mod_cast overhang_le i

/-! ### Each band dwarfs everything before it -/

open Classical in
/-- Distinct sample times give distinct window starts at any fixed atom, so the band has at
least `|bandT i|` distinct starts. -/
theorem card_bandT_le_winStarts (i : ℕ) : (bandT i).card ≤ (winStarts i).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun n => 2 * kIdx (gridAt i) n (Classical.arbitrary _))
    ?_ ?_
  · intro n hn
    exact (mem_winStarts i).2 ⟨n, hn, Classical.arbitrary _, rfl⟩
  · intro n hn n' hn' heq
    simp only at heq
    by_contra hne
    have hkk : 0 < kk i := by unfold kk; omega
    rcases Nat.lt_or_ge n n' with hlt | hge
    · have := window_gap_same_atom i (Classical.arbitrary _)
        (bandT_subset i hn) (bandT_subset i hn') hlt
      omega
    · have hgt : n' < n := by omega
      have := window_gap_same_atom i (Classical.arbitrary _)
        (bandT_subset i hn') (bandT_subset i hn) hgt
      omega

open Classical in
/-- The band has at most `|bandT i|·|Atom|` distinct starts. -/
theorem card_winStarts_le (i : ℕ) :
    (winStarts i).card ≤ (bandT i).card * Fintype.card (gridAt i).Atom := by
  classical
  rw [winStarts_eq_image]
  refine le_trans Finset.card_image_le ?_
  rw [bandPairs, Finset.card_product, Finset.card_univ]

set_option maxHeartbeats 1000000 in
/-- **Each band dwarfs the previous one**, with the next window length as the factor. -/
theorem fL_step (j : ℕ) : (kk (j + 1) : ℝ) * (fL j : ℝ) ≤ 2 * (fL (j + 1) : ℝ) := by
  have hA : (1 : ℝ) ≤ (Fintype.card (gridAt j).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt j).Atom := Fintype.card_pos
    exact_mod_cast this
  have hPj : (0 : ℝ) ≤ ((PK j).card : ℝ) := Nat.cast_nonneg _
  have hkkj : (0 : ℝ) ≤ (kk j : ℝ) := Nat.cast_nonneg _
  have hband : ((bandT j).card : ℝ) ≤ ((PK j).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (bandT_subset j)
  have hws : ((winStarts j).card : ℝ)
      ≤ ((bandT j).card : ℝ) * (Fintype.card (gridAt j).Atom : ℝ) := by
    have h := card_winStarts_le j
    exact_mod_cast h
  have hbl : (fL j : ℝ) = ((winStarts j).card : ℝ) * (kk j : ℝ) := by
    show ((((winStarts j).card * kk j : ℕ)) : ℝ) = _
    push_cast; ring
  have h1 : (fL j : ℝ)
      ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PK j).card : ℝ) * (kk j : ℝ) := by
    rw [hbl]
    have hstep : ((winStarts j).card : ℝ)
        ≤ (Fintype.card (gridAt j).Atom : ℝ) * ((PK j).card : ℝ) := by
      nlinarith [hws, hband, hA, hPj]
    exact mul_le_mul_of_nonneg_right hstep hkkj
  have h2 := granule_exceeds_previous_scale j
  have h3 : ((PK (j + 1)).card : ℝ) ≤ 2 * ((bandT (j + 1)).card : ℝ) := card_bandT_ge' (j + 1)
  have h3' : ((bandT (j + 1)).card : ℝ) ≤ ((winStarts (j + 1)).card : ℝ) := by
    have := card_bandT_le_winStarts (j + 1)
    exact_mod_cast this
  have hkk1 : (0 : ℝ) ≤ (kk (j + 1) : ℝ) := Nat.cast_nonneg _
  have h4 : (fL (j + 1) : ℝ) = ((winStarts (j + 1)).card : ℝ) * (kk (j + 1) : ℝ) := by
    show ((((winStarts (j + 1)).card * kk (j + 1) : ℕ)) : ℝ) = _
    push_cast; ring
  rw [h4]
  nlinarith [h1, h2, h3, h3', hkk1]

lemma kk_ge_real' (i : ℕ) : (40000 : ℝ) ≤ (kk i : ℝ) := by
  have : (40000 : ℕ) ≤ kk i := by unfold kk; omega
  exact_mod_cast this

/-- **The history is a `4/m_i` fraction of band `i`.** -/
theorem fT_kk_le (i : ℕ) : (fT i : ℝ) * (kk i : ℝ) ≤ 4 * (fL i : ℝ) := by
  induction i with
  | zero =>
      have h0 : ((fT 0 : ℕ) : ℝ) = 0 := by norm_num [fT]
      rw [h0]
      have : (0 : ℝ) ≤ (fL 0 : ℝ) := Nat.cast_nonneg _
      linarith
  | succ i ih =>
      have hstep := fL_step i
      have hbT : (fT (i + 1) : ℝ) = (fT i : ℝ) + (fL i : ℝ) := by
        show ((fT i + fL i : ℕ) : ℝ) = _
        push_cast; ring
      have hkki := kk_ge_real' i
      have hkki1 := kk_ge_real' (i + 1)
      have hTnn : (0 : ℝ) ≤ (fT i : ℝ) := Nat.cast_nonneg _
      have hLnn : (0 : ℝ) ≤ (fL i : ℝ) := Nat.cast_nonneg _
      have hTm : (fT i : ℝ) * (kk (i + 1) : ℝ) * (kk i : ℝ) ≤ 8 * (fL (i + 1) : ℝ) := by
        have h1 : (fT i : ℝ) * (kk (i + 1) : ℝ) * (kk i : ℝ)
            = ((fT i : ℝ) * (kk i : ℝ)) * (kk (i + 1) : ℝ) := by ring
        rw [h1]
        calc ((fT i : ℝ) * (kk i : ℝ)) * (kk (i + 1) : ℝ)
            ≤ (4 * (fL i : ℝ)) * (kk (i + 1) : ℝ) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = 4 * ((kk (i + 1) : ℝ) * (fL i : ℝ)) := by ring
          _ ≤ 4 * (2 * (fL (i + 1) : ℝ)) := by linarith
          _ = 8 * (fL (i + 1) : ℝ) := by ring
      rw [hbT]
      have hLnn1 : (0 : ℝ) ≤ (fL (i + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith [hTm, hstep, hkki, hkki1, hLnn1]

/-! ### The overhang fraction vanishes -/

set_option maxHeartbeats 1000000 in
/-- **`|Atom|² ≤ |P_K|`.**  `|Atom| ≤ 2^{K³+K}` while `|P_K| ≥ 2^{98·2^{m(K)}}/2` and
`m(K) ≥ K³`. -/
theorem card_Atom_sq_le_PK (i : ℕ) :
    (Fintype.card (gridAt i).Atom : ℝ) ^ 2 ≤ ((PK i).card : ℝ) := by
  have hA : (Fintype.card (gridAt i).Atom : ℝ) ≤ (2 : ℝ) ^ (KK i ^ 3 + KK i) := by
    have h := card_Atom_le_two_pow i
    have : ((Fintype.card (gridAt i).Atom : ℕ) : ℝ) ≤ ((2 ^ (KK i ^ 3 + KK i) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    exact this
  have hP := card_PK_ge i
  have hAnn : (0 : ℝ) ≤ (Fintype.card (gridAt i).Atom : ℝ) := Nat.cast_nonneg _
  have hsq : (Fintype.card (gridAt i).Atom : ℝ) ^ 2
      ≤ ((2 : ℝ) ^ (KK i ^ 3 + KK i)) ^ 2 := by
    exact pow_le_pow_left₀ hAnn hA 2
  have hexp : ((2 : ℝ) ^ (KK i ^ 3 + KK i)) ^ 2 = (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) := by
    rw [← pow_mul]
    ring_nf
  -- the exponent gap
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by have := KK_ge i; omega)
    unfold m
    omega
  have hlt : m (KK i) < 2 ^ m (KK i) := Nat.lt_two_pow_self
  have hKcube : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
  have hgap : 2 * (KK i ^ 3 + KK i) + 1 ≤ 98 * 2 ^ m (KK i) := by omega
  have hmono : (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) * 2 ≤ (2 : ℝ) ^ (98 * 2 ^ m (KK i)) := by
    have h2 : (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) * 2
        = (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i) + 1) := (pow_succ 2 _).symm
    rw [h2]
    exact pow_le_pow_right₀ (by norm_num) hgap
  have hhalf : (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) ≤ (2 : ℝ) ^ (98 * 2 ^ m (KK i)) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact hmono
  calc (Fintype.card (gridAt i).Atom : ℝ) ^ 2
      ≤ (2 : ℝ) ^ (2 * (KK i ^ 3 + KK i)) := by rw [← hexp]; exact hsq
    _ ≤ (2 : ℝ) ^ (98 * 2 ^ m (KK i)) / 2 := hhalf
    _ ≤ ((PK i).card : ℝ) := hP

/-- `|Atom_i| → ∞`. -/
theorem tendsto_card_Atom_atTop :
    Tendsto (fun i => (Fintype.card (gridAt i).Atom : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
  have h1 : i ≤ KK i := by unfold KK kk; omega
  have h2 : KK i ≤ Fintype.card (gridAt i).Atom := by
    rw [card_Atom_gridAt]
    have hb : KK i ≤ KK i ^ 2 + 1 := by nlinarith [KK_ge i]
    calc KK i ≤ KK i ^ 2 + 1 := hb
      _ = (KK i ^ 2 + 1) ^ 1 := (pow_one _).symm
      _ ≤ (KK i ^ 2 + 1) ^ KK i := Nat.pow_le_pow_right (by omega) (by have := KK_ge i; omega)
  have : i ≤ Fintype.card (gridAt i).Atom := le_trans h1 h2
  exact_mod_cast this

/-- **The overhang fraction vanishes**: `ov_i / |bandPairs i| ≤ 8/|Atom_i| → 0`. -/
theorem overhang_frac_le (i : ℕ) :
    (((bandPairs i).card - (winStarts i).card : ℕ) : ℝ)
      ≤ 8 / (Fintype.card (gridAt i).Atom : ℝ) * ((bandPairs i).card : ℝ) := by
  have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hov := overhang_le_real i
  have hPsq := card_Atom_sq_le_PK i
  have hB : ((bandPairs i).card : ℝ)
      = ((bandT i).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
    have hnat : (bandPairs i).card = (bandT i).card * Fintype.card (gridAt i).Atom := by
      rw [bandPairs, Finset.card_product, Finset.card_univ]
    rw [hnat]
    push_cast
    ring
  have hT : ((PK i).card : ℝ) ≤ 2 * ((bandT i).card : ℝ) := card_bandT_ge' i
  have hTnn : (0 : ℝ) ≤ ((bandT i).card : ℝ) := Nat.cast_nonneg _
  have hPnn : (0 : ℝ) ≤ ((PK i).card : ℝ) := Nat.cast_nonneg _
  rw [hB]
  -- `ov ≤ 2|PK| + 2|Atom|² ≤ 4|bandT| + 2|PK| ≤ 8|bandT|`
  have hstep : (((bandPairs i).card - (winStarts i).card : ℕ) : ℝ)
      ≤ 8 * ((bandT i).card : ℝ) := by
    have h1 : 2 * (Fintype.card (gridAt i).Atom : ℝ) ^ 2 ≤ 2 * ((PK i).card : ℝ) := by
      linarith [hPsq]
    linarith [hov, h1, hT]
  have hfrac : 8 * ((bandT i).card : ℝ)
      = 8 / (Fintype.card (gridAt i).Atom : ℝ)
        * (((bandT i).card : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)) := by
    field_simp
  linarith [hstep, hfrac]

/-! ### The pair count is the sum over pairs of the window count -/

open Classical in
/-- The `(n, α, p)` count of `tendsto_bandT_occursCount`, re-summed over the band pairs. -/
theorem pairCount_eq (i : ℕ) (x : ℝ) (v : List ℕ) :
    ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
        ((bandT i).filter fun n =>
          OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
      = ∑ z ∈ bandPairs i, winOcc i x v (2 * kIdx (gridAt i) z.1 z.2) := by
  classical
  have hL : ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
        ((bandT i).filter fun n =>
          OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
      = ∑ α : (gridAt i).Atom, ∑ p ∈ Finset.range (kk i - v.length + 1),
          ∑ n ∈ bandT i,
            (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun p =>
      ∑ n ∈ bandT i, (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hR : ∑ z ∈ bandPairs i, winOcc i x v (2 * kIdx (gridAt i) z.1 z.2)
      = ∑ n ∈ bandT i, ∑ α : (gridAt i).Atom,
          ∑ p ∈ Finset.range (kk i - v.length + 1),
            (if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0) := by
    rw [bandPairs, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun α _ => ?_
    rw [winOcc, Finset.card_filter]
  rw [hL, hR]
  rw [Finset.sum_congr rfl (fun (α : (gridAt i).Atom) _ =>
    Finset.sum_comm (s := Finset.range (kk i - v.length + 1)) (t := bandT i)
      (f := fun p n => if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0))]
  exact Finset.sum_comm




end NormalNumbers.G4.Sched

/-! ### The read-versus-certified error, as pure real arithmetic

Isolating the bookkeeping from the schedule keeps the elaborator away from the (astronomically
large) closed terms.  `W` is the read count, `N` the read length, `S` the distinct-window count,
`P` the pair count, `A`/`B` the numbers of distinct windows and of pairs, `F = m − ℓ + 1`,
`T` the history, `r` the certified frequency and `Q` the atom count.
-/

namespace NormalNumbers.G4Entropy

set_option maxHeartbeats 2000000 in
/-- **The read frequency tracks the certified one**, with error `16/Q + (ℓ+4)/m`. -/
theorem read_freq_error_bound {W N S P T A B F m ℓ r Q : ℝ}
    (hApos : 0 < A) (hFpos : 0 < F) (hmpos : 0 < m) (hQpos : 0 < Q) (hQ16 : 16 ≤ Q)
    (hTnn : 0 ≤ T) (hℓnn : 0 ≤ ℓ) (hWnn : 0 ≤ W)
    (hFm : F ≤ m) (hFeq : F = m - ℓ + 1)
    (hNeq : N = T + A * m) (hT4 : T ≤ 4 * A)
    (hWlo : S ≤ W) (hWhi : W ≤ S + T + A * ℓ)
    (hSP : S ≤ P) (hPS : P ≤ S + (B - A) * F)
    (hPr : P = r * (B * F)) (hrnn : 0 ≤ r) (hr1 : r ≤ 1)
    (hAB : A ≤ B) (hovA : B - A ≤ 16 / Q * A) :
    |W / N - r| ≤ 16 / Q + (ℓ + 4) / m := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hApos hAB
  have hNpos : 0 < N := by rw [hNeq]; nlinarith
  have hNge : A * m ≤ N := by rw [hNeq]; linarith
  have hNle : N ≤ A * (m + 4) := by rw [hNeq]; nlinarith
  have hQnn : (0 : ℝ) ≤ 16 / Q := by positivity
  have hmnn : (0 : ℝ) ≤ (ℓ + 4) / m := by positivity
  -- upper bound
  have hupper : W / N ≤ r + 16 / Q + (ℓ + 4) / m := by
    have hnum : W ≤ r * (B * F) + T + A * ℓ := by rw [← hPr]; linarith
    have hnumnn : (0 : ℝ) ≤ r * (B * F) + T + A * ℓ := by
      have h1 : (0 : ℝ) ≤ r * (B * F) := mul_nonneg hrnn (mul_nonneg hBpos.le hFpos.le)
      have h2 : (0 : ℝ) ≤ A * ℓ := mul_nonneg hApos.le hℓnn
      linarith
    have hstep : W / N ≤ (r * (B * F) + T + A * ℓ) / (A * m) := by
      have h1 : W / N ≤ (r * (B * F) + T + A * ℓ) / N := by gcongr
      refine h1.trans ?_
      exact div_le_div_of_nonneg_left hnumnn (by positivity) hNge
    refine hstep.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hBF : r * (B * F) ≤ r * (B * m) := by
      have hrB : (0 : ℝ) ≤ r * B := mul_nonneg hrnn hBpos.le
      calc r * (B * F) = (r * B) * F := by ring
        _ ≤ (r * B) * m := mul_le_mul_of_nonneg_left hFm hrB
        _ = r * (B * m) := by ring
    have hBA : r * (B * m) ≤ (r + 16 / Q) * (A * m) := by
      have h1 : r * B ≤ (r + 16 / Q) * A := by
        have h3 : r * (B - A) ≤ 16 / Q * A := by nlinarith [hovA, hr1, hrnn, hAB]
        nlinarith [h3]
      nlinarith [h1, hmpos]
    have hTA : T + A * ℓ ≤ (ℓ + 4) / m * (A * m) := by
      have hexp : (ℓ + 4) / m * (A * m) = (ℓ + 4) * A := by field_simp
      rw [hexp]
      nlinarith [hT4, hApos, hℓnn]
    nlinarith [hBF, hBA, hTA]
  -- lower bound
  have hlower : r - 16 / Q - (ℓ + 4) / m ≤ W / N := by
    rcases le_or_gt (r - 16 / Q) 0 with hneg | hpos
    · have hnn : (0 : ℝ) ≤ W / N := by positivity
      linarith
    · have hnum : r * (B * F) - (B - A) * F ≤ W := by rw [← hPr]; linarith
      have hnumnn : (0 : ℝ) ≤ r * (B * F) - (B - A) * F := by
        have h1 : (B - A) * F ≤ 16 / Q * (A * F) := by
          have hmul := mul_le_mul_of_nonneg_right hovA hFpos.le
          calc (B - A) * F ≤ (16 / Q * A) * F := hmul
            _ = 16 / Q * (A * F) := by ring
        have hBA0 : (0 : ℝ) ≤ (B - A) * F := mul_nonneg (by linarith) hFpos.le
        have hneg : -((B - A) * F) ≤ (B - A) * F * (r - 1) := by nlinarith [hBA0, hr1, hrnn]
        have hexp : r * (B * F) - (B - A) * F - (r - 16 / Q) * (A * F)
            = (B - A) * F * (r - 1) + 16 / Q * (A * F) := by ring
        have hpos2 : (0 : ℝ) ≤ (r - 16 / Q) * (A * F) :=
          mul_nonneg hpos.le (mul_nonneg hApos.le hFpos.le)
        linarith [hexp, hneg, h1, hpos2]
      have hstep : (r * (B * F) - (B - A) * F) / (A * (m + 4)) ≤ W / N := by
        have h1 : (r * (B * F) - (B - A) * F) / N ≤ W / N := by gcongr
        refine le_trans ?_ h1
        exact div_le_div_of_nonneg_left hnumnn hNpos hNle
      refine le_trans ?_ hstep
      rw [le_div_iff₀ (by positivity)]
      have hkey : (r - 16 / Q) * (A * F) ≤ r * (B * F) - (B - A) * F := by
        have h1 : (B - A) * F ≤ 16 / Q * (A * F) := by
          have hmul := mul_le_mul_of_nonneg_right hovA hFpos.le
          calc (B - A) * F ≤ (16 / Q * A) * F := hmul
            _ = 16 / Q * (A * F) := by ring
        have hBA0 : (0 : ℝ) ≤ (B - A) * F := mul_nonneg (by linarith) hFpos.le
        have hneg : -((B - A) * F) ≤ (B - A) * F * (r - 1) := by nlinarith [hBA0, hr1, hrnn]
        have hexp : r * (B * F) - (B - A) * F - (r - 16 / Q) * (A * F)
            = (B - A) * F * (r - 1) + 16 / Q * (A * F) := by ring
        linarith [hexp, hneg, h1]
      refine le_trans ?_ hkey
      have hfac : (r - 16 / Q - (ℓ + 4) / m) * (A * (m + 4))
          ≤ (r - 16 / Q) * (A * F) := by
        have hFdiff : (m + 4) - F = ℓ + 3 := by rw [hFeq]; ring
        have hrle : r - 16 / Q ≤ 1 := by linarith
        have hgap : (r - 16 / Q) * (m + 4) - (r - 16 / Q) * F = (r - 16 / Q) * (ℓ + 3) := by
          rw [← mul_sub, hFdiff]
        have hbound : (r - 16 / Q) * (ℓ + 3) ≤ (ℓ + 4) / m * (m + 4) := by
          have h1 : (r - 16 / Q) * (ℓ + 3) ≤ ℓ + 3 := by nlinarith [hpos, hrle, hℓnn]
          have h2 : (ℓ + 3) ≤ (ℓ + 4) / m * (m + 4) := by
            have hexp : (ℓ + 4) / m * (m + 4) = (ℓ + 4) * (m + 4) / m := by ring
            rw [hexp, le_div_iff₀ hmpos]
            nlinarith [hmpos, hℓnn]
          linarith
        have hexpand : (r - 16 / Q - (ℓ + 4) / m) * (A * (m + 4))
            = ((r - 16 / Q) * (m + 4) - (ℓ + 4) / m * (m + 4)) * A := by ring
        have hexpand2 : (r - 16 / Q) * (A * F) = ((r - 16 / Q) * F) * A := by ring
        rw [hexpand, hexpand2]
        refine mul_le_mul_of_nonneg_right ?_ hApos.le
        linarith [hgap, hbound]
      linarith [hfac]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The schedule-only frequency limit -/

open Classical in
/-- The band's certified frequency, as in `tendsto_bandT_occursCount`. -/
noncomputable def bandRatio (i : ℕ) (x : ℝ) (v : List ℕ) : ℝ :=
  (∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
      (((bandT i).filter fun n =>
        OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card : ℝ))
    / (((bandT i).card : ℝ)
        * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The read frequency tracks the certified one** at every scale. -/
theorem abs_fullRead_sub_bandRatio_le (v : List ℕ) (hlen : 0 < v.length) (i : ℕ)
    (hℓm : v.length ≤ kk i) (h16 : 16 ≤ Fintype.card (gridAt i).Atom) :
    |(winCount (fullDig (primeLambertAtBase 4)) v (fT (i + 1)) : ℝ) / ((fT (i + 1) : ℕ) : ℝ)
        - bandRatio i (primeLambertAtBase 4) v|
      ≤ 16 / (Fintype.card (gridAt i).Atom : ℝ) + ((v.length : ℝ) + 4) / (kk i : ℝ) := by
  classical
  have hApos : (0 : ℝ) < ((winStarts i).card : ℝ) := by
    exact_mod_cast card_winStarts_pos i
  have hQpos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hQ16 : (16 : ℝ) ≤ (Fintype.card (gridAt i).Atom : ℝ) := by exact_mod_cast h16
  have hmpos : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hFpos : (0 : ℝ) < ((kk i - v.length + 1 : ℕ) : ℝ) := by
    have : 0 < kk i - v.length + 1 := by omega
    exact_mod_cast this
  have hFm : ((kk i - v.length + 1 : ℕ) : ℝ) ≤ (kk i : ℝ) := by
    have : (kk i - v.length + 1 : ℕ) ≤ kk i := by omega
    exact_mod_cast this
  have hFeq : ((kk i - v.length + 1 : ℕ) : ℝ) = (kk i : ℝ) - (v.length : ℝ) + 1 := by
    have h1 : (kk i - v.length + 1 : ℕ) = kk i + 1 - v.length := by omega
    rw [h1, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hNeq : ((fT (i + 1) : ℕ) : ℝ)
      = ((fT i : ℕ) : ℝ) + ((winStarts i).card : ℝ) * (kk i : ℝ) := by
    show ((fT i + fL i : ℕ) : ℝ) = _
    rw [fL]
    push_cast
    ring
  have hT4 : ((fT i : ℕ) : ℝ) ≤ 4 * ((winStarts i).card : ℝ) := by
    have h := fT_kk_le i
    have hfl : (fL i : ℝ) = ((winStarts i).card : ℝ) * (kk i : ℝ) := by
      show ((((winStarts i).card * kk i : ℕ)) : ℝ) = _
      push_cast; ring
    rw [hfl] at h
    nlinarith [hmpos, hApos]
  obtain ⟨hlo, hhi⟩ := full_winCount_bounds (primeLambertAtBase 4) i v hlen hℓm
  have hWlo : (fullGood i (primeLambertAtBase 4) v : ℝ)
      ≤ (winCount (fullDig (primeLambertAtBase 4)) v (fT (i + 1)) : ℝ) := by
    exact_mod_cast hlo
  have hWhi : (winCount (fullDig (primeLambertAtBase 4)) v (fT (i + 1)) : ℝ)
      ≤ (fullGood i (primeLambertAtBase 4) v : ℝ) + ((fT i : ℕ) : ℝ)
        + ((winStarts i).card : ℝ) * (v.length : ℝ) := by
    have heq : ((fullGood i (primeLambertAtBase 4) v + fT i
        + (winStarts i).card * v.length : ℕ) : ℝ)
        = (fullGood i (primeLambertAtBase 4) v : ℝ) + ((fT i : ℕ) : ℝ)
          + ((winStarts i).card : ℝ) * (v.length : ℝ) := by push_cast; ring
    rw [← heq]
    exact_mod_cast hhi
  obtain ⟨hp1, hp2⟩ := sum_pairs_sub_le i (primeLambertAtBase 4) v
  have hAB : ((winStarts i).card : ℝ) ≤ ((bandPairs i).card : ℝ) := by
    exact_mod_cast card_bandPairs_sub i
  have hSP : (fullGood i (primeLambertAtBase 4) v : ℝ)
      ≤ ((∑ z ∈ bandPairs i,
          winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ) := by
    rw [fullGood_eq i (primeLambertAtBase 4) v]
    exact_mod_cast hp1
  have hPS : ((∑ z ∈ bandPairs i,
        winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ)
      ≤ (fullGood i (primeLambertAtBase 4) v : ℝ)
        + (((bandPairs i).card : ℝ) - ((winStarts i).card : ℝ))
          * ((kk i - v.length + 1 : ℕ) : ℝ) := by
    have hov : ((((bandPairs i).card - (winStarts i).card : ℕ)) : ℝ)
        = ((bandPairs i).card : ℝ) - ((winStarts i).card : ℝ) := by
      rw [Nat.cast_sub (card_bandPairs_sub i)]
    have h2 : ((∑ z ∈ bandPairs i,
        winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ) : ℝ)
        ≤ ((∑ q ∈ winStarts i, winOcc i (primeLambertAtBase 4) v q : ℕ) : ℝ)
          + ((((bandPairs i).card - (winStarts i).card : ℕ)) : ℝ)
            * ((kk i - v.length + 1 : ℕ) : ℝ) := by
      have := hp2
      push_cast
      exact_mod_cast this
    rw [hov] at h2
    rw [fullGood_eq i (primeLambertAtBase 4) v]
    exact h2
  have hnumcast : (∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
      ((((bandT i).filter fun n =>
        OccursAt 2 (primeLambertAtBase 4) v
          (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card : ℕ) : ℝ))
      = (((∑ z ∈ bandPairs i,
          winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ)) : ℝ) := by
    rw [← pairCount_eq i (primeLambertAtBase 4) v]
    push_cast
    rfl
  have hBFeq : ((bandPairs i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)
      = ((bandT i).card : ℝ)
        * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)) := by
    have hnat : (bandPairs i).card = (bandT i).card * Fintype.card (gridAt i).Atom := by
      rw [bandPairs, Finset.card_product, Finset.card_univ]
    rw [hnat]
    push_cast
    ring
  have hden : ((bandT i).card : ℝ)
      * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)) ≠ 0 := by
    have h1 : (0 : ℝ) < ((bandT i).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 (bandT_nonempty i)
    exact (mul_pos h1 (mul_pos hQpos hFpos)).ne'
  have hPr : (((∑ z ∈ bandPairs i,
        winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ)) : ℝ)
      = bandRatio i (primeLambertAtBase 4) v
        * (((bandPairs i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)) := by
    rw [bandRatio, hnumcast, hBFeq]
    exact (div_mul_cancel₀ _ hden).symm
  have hrnn : (0 : ℝ) ≤ bandRatio i (primeLambertAtBase 4) v := by
    rw [bandRatio]
    refine div_nonneg (Finset.sum_nonneg fun c _ => Nat.cast_nonneg _) ?_
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hr1 : bandRatio i (primeLambertAtBase 4) v ≤ 1 := by
    have hBpos : (0 : ℝ) < ((bandPairs i).card : ℝ) := lt_of_lt_of_le hApos hAB
    have hBF : (0 : ℝ) < ((bandPairs i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ) :=
      mul_pos hBpos hFpos
    have hbound : ∑ z ∈ bandPairs i,
        winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2)
        ≤ (bandPairs i).card * (kk i - v.length + 1) := by
      calc ∑ z ∈ bandPairs i,
            winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2)
          ≤ ∑ _z ∈ bandPairs i, (kk i - v.length + 1) :=
            Finset.sum_le_sum fun z _ => winOcc_le i (primeLambertAtBase 4) v _
        _ = (bandPairs i).card * (kk i - v.length + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hPle : (((∑ z ∈ bandPairs i,
          winOcc i (primeLambertAtBase 4) v (2 * kIdx (gridAt i) z.1 z.2) : ℕ)) : ℝ)
        ≤ ((bandPairs i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ) := by
      exact_mod_cast hbound
    rw [hPr] at hPle
    refine le_of_mul_le_mul_right ?_ hBF
    rw [one_mul]
    exact hPle
  have hovA : ((bandPairs i).card : ℝ) - ((winStarts i).card : ℝ)
      ≤ 16 / (Fintype.card (gridAt i).Atom : ℝ) * ((winStarts i).card : ℝ) := by
    have hfrac := overhang_frac_le i
    rw [Nat.cast_sub (card_bandPairs_sub i)] at hfrac
    have hBA2 : ((bandPairs i).card : ℝ) ≤ 2 * ((winStarts i).card : ℝ) := by
      have h8 : 8 / (Fintype.card (gridAt i).Atom : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hQpos (by norm_num)]
        linarith
      nlinarith [hfrac, h8, hApos]
    have h2 : (0 : ℝ) ≤ 8 / (Fintype.card (gridAt i).Atom : ℝ) := by positivity
    have h3 : 8 / (Fintype.card (gridAt i).Atom : ℝ) * ((bandPairs i).card : ℝ)
        ≤ 8 / (Fintype.card (gridAt i).Atom : ℝ) * (2 * ((winStarts i).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hBA2 h2
    have h4 : 8 / (Fintype.card (gridAt i).Atom : ℝ) * (2 * ((winStarts i).card : ℝ))
        = 16 / (Fintype.card (gridAt i).Atom : ℝ) * ((winStarts i).card : ℝ) := by ring
    linarith [hfrac, h3, h4]
  have hWnn : (0 : ℝ) ≤ (winCount (fullDig (primeLambertAtBase 4)) v (fT (i + 1)) : ℝ) :=
    Nat.cast_nonneg _
  have hTnn : (0 : ℝ) ≤ ((fT i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hℓnn : (0 : ℝ) ≤ (v.length : ℝ) := Nat.cast_nonneg _
  exact read_freq_error_bound hApos hFpos hmpos hQpos hQ16 hTnn hℓnn hWnn hFm hFeq hNeq hT4
    hWlo hWhi hSP hPS hPr hrnn hr1 hAB hovA



end NormalNumbers.G4.Sched
