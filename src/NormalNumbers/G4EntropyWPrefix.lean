/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWSandwich

/-!
# The wide read's **prefix** count

`G4EntropyFullSeqW` counts the read at the band cutoffs `fTW (i+1)`.  `IsNormalSequence 2` needs
every read index, so this module re-runs the count over the first `a` windows of band `i`.

Two facts:

* **The consumed starts are an initial segment.**  `fnthW i` enumerates `winStartsW i` in
  increasing order, so `startsLe i c = (winStartsW i).filter (· ≤ c)` is exactly the image of
  `Finset.range (aLe i c)` under `fnthW i` (`startsLe_eq_image`).  This is the bridge between the
  *read-index* view (the first `a` windows) and the *position-threshold* view (`G4EntropyWSandwich`'s
  `cutLo`/`cutHi`).
* **The prefix read count**, `fullW_band_prefix_winCount_bounds` and
  `fullW_prefix_winCount_bounds`: the verbatim analogues of `fullW_band_winCount_bounds` and
  `fullW_winCount_bounds` with `Finset.range a` in place of `Finset.range (winStartsW i).card`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### `fnthW` is an order isomorphism onto the starts -/

lemma fnthW_surj (i : ℕ) {q : ℕ} (hq : q ∈ winStartsW i) :
    ∃ b, b < (winStartsW i).card ∧ fnthW i b = q := by
  classical
  have hrange : q ∈ Set.range ((winStartsW i).orderEmbOfFin (rfl : (winStartsW i).card = _)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hq
  obtain ⟨b, hb⟩ := hrange
  refine ⟨(b : ℕ), b.isLt, ?_⟩
  rw [fnthW]
  have hfin : (⟨(b : ℕ) % (winStartsW i).card, Nat.mod_lt _ (card_winStartsW_pos i)⟩ :
      Fin (winStartsW i).card) = b := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt b.isLt
  rw [hfin]
  exact hb

lemma fnthW_mono' {i b b' : ℕ} (h : b ≤ b') (hb' : b' < (winStartsW i).card) :
    fnthW i b ≤ fnthW i b' := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact (fnthW_lt_fnthW hlt hb').le

lemma fnthW_le_iff {i b b' : ℕ} (hb : b < (winStartsW i).card)
    (hb' : b' < (winStartsW i).card) : fnthW i b ≤ fnthW i b' ↔ b ≤ b' := by
  constructor
  · intro h
    by_contra hcon
    have hlt : b' < b := by omega
    have := fnthW_lt_fnthW hlt hb
    omega
  · intro h
    exact fnthW_mono' h hb'

/-! ### The consumed starts are an initial segment -/

open Classical in
/-- The band-`i` window starts consumed by the position cutoff `c`. -/
noncomputable def startsLe (i c : ℕ) : Finset ℕ := (winStartsW i).filter (fun q => q ≤ c)

open Classical in
/-- How many windows of band `i` the position cutoff `c` consumes. -/
noncomputable def aLe (i c : ℕ) : ℕ := (startsLe i c).card

open Classical in
/-- The consumed **indices**. -/
noncomputable def idxLe (i c : ℕ) : Finset ℕ :=
  (Finset.range (winStartsW i).card).filter (fun b => fnthW i b ≤ c)

open Classical in
/-- **A down-set of `range N` is a `range`.** -/
lemma idxLe_eq_range (i c : ℕ) : idxLe i c = Finset.range (idxLe i c).card := by
  classical
  have hdown : ∀ {b b' : ℕ}, b ≤ b' → b' ∈ idxLe i c → b ∈ idxLe i c := by
    intro b b' hbb hb'
    rw [idxLe, Finset.mem_filter, Finset.mem_range] at hb' ⊢
    refine ⟨by omega, ?_⟩
    exact le_trans (fnthW_mono' hbb hb'.1) hb'.2
  ext b
  rw [Finset.mem_range]
  constructor
  · intro hb
    have hsub : Finset.range (b + 1) ⊆ idxLe i c := by
      intro t ht
      rw [Finset.mem_range] at ht
      exact hdown (by omega) hb
    have := Finset.card_le_card hsub
    simpa using Nat.lt_of_lt_of_le (by omega : b < b + 1) (by simpa using this)
  · intro hb
    by_contra hcon
    have hsub : idxLe i c ⊆ Finset.range b := by
      intro t ht
      rw [Finset.mem_range]
      by_contra hcon2
      exact hcon (hdown (by omega) ht)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    omega

open Classical in
lemma startsLe_eq_image_idxLe (i c : ℕ) :
    startsLe i c = Finset.image (fnthW i) (idxLe i c) := by
  classical
  ext q
  rw [startsLe, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hq, hqc⟩
    obtain ⟨b, hb, rfl⟩ := fnthW_surj i hq
    exact ⟨b, by rw [idxLe, Finset.mem_filter, Finset.mem_range]; exact ⟨hb, hqc⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rw [idxLe, Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨fnthW_mem i b, hb.2⟩

open Classical in
lemma card_idxLe (i c : ℕ) : (idxLe i c).card = aLe i c := by
  classical
  have hinj : Set.InjOn (fnthW i) (idxLe i c) := by
    intro b hb b' hb' hEq
    simp only [Finset.mem_coe, idxLe, Finset.mem_filter, Finset.mem_range] at hb hb'
    by_contra hcon
    rcases Nat.lt_or_ge b b' with h | h
    · have := fnthW_lt_fnthW h hb'.1; omega
    · have hlt : b' < b := by omega
      have := fnthW_lt_fnthW hlt hb.1; omega
  rw [aLe, startsLe_eq_image_idxLe]
  exact (Finset.card_image_of_injOn hinj).symm

open Classical in
/-- **The bridge**: the starts consumed by the position cutoff `c` are exactly the first
`aLe i c` starts of band `i`. -/
theorem startsLe_eq_image (i c : ℕ) :
    startsLe i c = Finset.image (fnthW i) (Finset.range (aLe i c)) := by
  rw [startsLe_eq_image_idxLe, ← card_idxLe, ← idxLe_eq_range]

lemma aLe_le_card (i c : ℕ) : aLe i c ≤ (winStartsW i).card := by
  classical
  rw [aLe, startsLe]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-! ### The prefix window sum -/

open Classical in
/-- The fitting in-window occurrences of `v` in the **first `a`** windows of band `i`. -/
noncomputable def fullGoodWPre (i a : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ b ∈ Finset.range a,
    ((Finset.range (kk i - v.length + 1)).filter
      (fun q => OccursAt 2 x v (fnthW i b + q))).card

open Classical in
/-- `fullGoodWPre` re-summed over the consumed starts. -/
theorem fullGoodWPre_eq (i c : ℕ) (x : ℝ) (v : List ℕ) :
    fullGoodWPre i (aLe i c) x v
      = ∑ q ∈ startsLe i c,
          ((Finset.range (kk i - v.length + 1)).filter
            (fun p => OccursAt 2 x v (q + p))).card := by
  classical
  have hinj : ∀ b ∈ Finset.range (aLe i c), ∀ b' ∈ Finset.range (aLe i c),
      fnthW i b = fnthW i b' → b = b' := by
    intro b hb b' hb' hEq
    rw [Finset.mem_range] at hb hb'
    have hbc : b < (winStartsW i).card := lt_of_lt_of_le hb (aLe_le_card i c)
    have hbc' : b' < (winStartsW i).card := lt_of_lt_of_le hb' (aLe_le_card i c)
    by_contra hcon
    rcases Nat.lt_or_ge b b' with h | h
    · have := fnthW_lt_fnthW h hbc'; omega
    · have hlt : b' < b := by omega
      have := fnthW_lt_fnthW hlt hbc; omega
  rw [startsLe_eq_image, fullGoodWPre, Finset.sum_image hinj]

/-! ### The prefix read count -/

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The prefix of band `i` contributes its own window occurrences**, up to one word length per
window.  This is `fullW_band_winCount_bounds` with `Finset.range a` for
`Finset.range (winStartsW i).card`. -/
theorem fullW_band_prefix_winCount_bounds (x : ℝ) (i a : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) (ha : a ≤ (winStartsW i).card) :
    fullGoodWPre i a x v
        ≤ ((Finset.Ico (fTW i) (fTW i + a * kk i)).filter
            (MatchesAt (fullDigW x) v)).card ∧
      ((Finset.Ico (fTW i) (fTW i + a * kk i)).filter (MatchesAt (fullDigW x) v)).card
        ≤ fullGoodWPre i a x v + a * v.length := by
  classical
  have hsplit : ((Finset.Ico (fTW i) (fTW i + a * kk i)).filter
        (MatchesAt (fullDigW x) v)).card
      = ∑ b ∈ Finset.range a,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card := by
    rw [card_Ico_shift _ (fTW i) (a * kk i), card_filter_range_mul]
  rw [hsplit]
  have hper : ∀ b ∈ Finset.range a,
      ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnthW i b + q))).card
        ≤ ((Finset.range (kk i)).filter
          (fun q => MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card ∧
      ((Finset.range (kk i)).filter
          (fun q => MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card
        ≤ ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnthW i b + q))).card + v.length := by
    intro b hb
    have hb' : b < (winStartsW i).card := lt_of_lt_of_le (Finset.mem_range.1 hb) ha
    have hcongr : ((Finset.range (kk i - v.length + 1)).filter
        (fun q => MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card
        = ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (fnthW i b + q))).card := by
      congr 1
      refine Finset.filter_congr fun q hq => ?_
      have hqfit : q + v.length ≤ kk i := by
        have := Finset.mem_range.1 hq
        omega
      have hassoc : fTW i + (b * kk i + q) = fTW i + b * kk i + q := by ring
      rw [hassoc]
      simpa using matchesAt_fullDigW_iff x i b q v hb' hqfit
    have h := card_filter_fit
      (fun q => MatchesAt (fullDigW x) v (fTW i + (b * kk i + q))) (m := kk i)
      (ℓ := v.length) hv hvm
    rw [hcongr] at h
    exact h
  constructor
  · exact Finset.sum_le_sum fun b hb => (hper b hb).1
  · calc ∑ b ∈ Finset.range a,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card
        ≤ ∑ b ∈ Finset.range a,
            (((Finset.range (kk i - v.length + 1)).filter
              (fun q => OccursAt 2 x v (fnthW i b + q))).card + v.length) :=
          Finset.sum_le_sum fun b hb => (hper b hb).2
      _ = fullGoodWPre i a x v + a * v.length := by
          rw [Finset.sum_add_distrib, fullGoodWPre]
          simp

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The full read count at a mid-band cutoff.** -/
theorem fullW_prefix_winCount_bounds (x : ℝ) (i a : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) (ha : a ≤ (winStartsW i).card) :
    fullGoodWPre i a x v ≤ winCount (fullDigW x) v (fTW i + a * kk i) ∧
      winCount (fullDigW x) v (fTW i + a * kk i)
        ≤ fullGoodWPre i a x v + fTW i + a * v.length := by
  classical
  have hle : fTW i ≤ fTW i + a * kk i := by omega
  have hsplit := winCount_split (fullDigW x) v hle
  obtain ⟨h1, h2⟩ := fullW_band_prefix_winCount_bounds x i a v hv hvm ha
  have hhist : winCount (fullDigW x) v (fTW i) ≤ fTW i := winCount_le _ _ _
  generalize hc : a * v.length = c at h2 ⊢
  rw [hsplit]
  omega

end NormalNumbers.G4.Sched
