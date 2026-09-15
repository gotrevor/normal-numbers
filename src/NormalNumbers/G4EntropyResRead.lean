/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWPrefix
import NormalNumbers.G4EntropySubLaw

/-!
# The read count restricted to a residue class of read positions

Base-`2^k` normality of `fullRealW` asks for the frequency of a binary word `v` of length
`ℓ = k·ℓ'` among the read positions `p ≡ c (mod k)`.  This module sets up the counting side of
that: `winCountR`, the residue-restricted window count, and the band-prefix bounds that mirror
`fullW_band_prefix_winCount_bounds` / `fullW_prefix_winCount_bounds` verbatim — the residue
condition rides along inside the filter and costs nothing in the combinatorics.

What it does *not* yet do is certify `fullGoodWPreR`; that is the job of the sub-family split
(`G4EntropySubLaw`), because the local class inside window `b` is `q ≡ c − fTW i − b·kk i`,
which moves with `b`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### §1  The residue-restricted window count -/

open Classical in
/-- **Residue-restricted window count**: the number of start positions `p < n` with
`p ≡ c (mod k)` at which `v` matches `s`. -/
noncomputable def winCountR (k c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => p % k = c ∧ MatchesAt s v p)).card

lemma winCountR_le (k c : ℕ) (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) : winCountR k c s v n ≤ n := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

lemma winCountR_zero (k c : ℕ) (s : ℕ → ℕ) (v : List ℕ) : winCountR k c s v 0 = 0 := by
  classical
  simp [winCountR]

open Classical in
lemma winCountR_split (k c : ℕ) (s : ℕ → ℕ) (v : List ℕ) {a n : ℕ} (han : a ≤ n) :
    winCountR k c s v n
      = winCountR k c s v a
        + ((Finset.Ico a n).filter (fun p => p % k = c ∧ MatchesAt s v p)).card := by
  classical
  unfold winCountR
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) han, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 a n))

lemma winCountR_mono (k c : ℕ) (s : ℕ → ℕ) (v : List ℕ) {m n : ℕ} (h : m ≤ n) :
    winCountR k c s v m ≤ winCountR k c s v n := by
  classical
  rw [winCountR_split k c s v h]; omega

lemma winCountR_sub_le (k c : ℕ) (s : ℕ → ℕ) (v : List ℕ) {m n : ℕ} (h : m ≤ n) :
    winCountR k c s v n - winCountR k c s v m ≤ n - m := by
  classical
  rw [winCountR_split k c s v h]
  have : ((Finset.Ico m n).filter (fun p => p % k = c ∧ MatchesAt s v p)).card ≤ n - m := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp
  omega

/-! ### §2  The residue-restricted prefix window sum -/

open Classical in
/-- The fitting in-window occurrences of `v` in the first `a` windows of band `i`, restricted to
the read positions `≡ c (mod k)`. -/
noncomputable def fullGoodWPreR (i a k c : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ b ∈ Finset.range a,
    ((Finset.range (kk i - v.length + 1)).filter
      (fun q => (fTW i + b * kk i + q) % k = c ∧ OccursAt 2 x v (fnthW i b + q))).card

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The prefix of band `i` contributes its own restricted window occurrences**, up to one word
length per window.  Mirrors `fullW_band_prefix_winCount_bounds`. -/
theorem fullW_band_prefix_winCountR_bounds (x : ℝ) (i a k c : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) (ha : a ≤ (winStartsW i).card) :
    fullGoodWPreR i a k c x v
        ≤ ((Finset.Ico (fTW i) (fTW i + a * kk i)).filter
            (fun p => p % k = c ∧ MatchesAt (fullDigW x) v p)).card ∧
      ((Finset.Ico (fTW i) (fTW i + a * kk i)).filter
            (fun p => p % k = c ∧ MatchesAt (fullDigW x) v p)).card
        ≤ fullGoodWPreR i a k c x v + a * v.length := by
  classical
  have hsplit : ((Finset.Ico (fTW i) (fTW i + a * kk i)).filter
        (fun p => p % k = c ∧ MatchesAt (fullDigW x) v p)).card
      = ∑ b ∈ Finset.range a,
          ((Finset.range (kk i)).filter
            (fun q => (fTW i + (b * kk i + q)) % k = c
              ∧ MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card := by
    rw [card_Ico_shift _ (fTW i) (a * kk i), card_filter_range_mul]
  rw [hsplit]
  have hper : ∀ b ∈ Finset.range a,
      ((Finset.range (kk i - v.length + 1)).filter
          (fun q => (fTW i + b * kk i + q) % k = c ∧ OccursAt 2 x v (fnthW i b + q))).card
        ≤ ((Finset.range (kk i)).filter
          (fun q => (fTW i + (b * kk i + q)) % k = c
            ∧ MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card ∧
      ((Finset.range (kk i)).filter
          (fun q => (fTW i + (b * kk i + q)) % k = c
            ∧ MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card
        ≤ ((Finset.range (kk i - v.length + 1)).filter
          (fun q => (fTW i + b * kk i + q) % k = c
            ∧ OccursAt 2 x v (fnthW i b + q))).card + v.length := by
    intro b hb
    have hb' : b < (winStartsW i).card := lt_of_lt_of_le (Finset.mem_range.1 hb) ha
    have hcongr : ((Finset.range (kk i - v.length + 1)).filter
        (fun q => (fTW i + (b * kk i + q)) % k = c
          ∧ MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card
        = ((Finset.range (kk i - v.length + 1)).filter
          (fun q => (fTW i + b * kk i + q) % k = c
            ∧ OccursAt 2 x v (fnthW i b + q))).card := by
      congr 1
      refine Finset.filter_congr fun q hq => ?_
      have hqfit : q + v.length ≤ kk i := by
        have := Finset.mem_range.1 hq
        omega
      have hassoc : fTW i + (b * kk i + q) = fTW i + b * kk i + q := by ring
      rw [hassoc]
      have hm := matchesAt_fullDigW_iff x i b q v hb' hqfit
      exact and_congr Iff.rfl hm
    have h := card_filter_fit
      (fun q => (fTW i + (b * kk i + q)) % k = c
        ∧ MatchesAt (fullDigW x) v (fTW i + (b * kk i + q))) (m := kk i)
      (ℓ := v.length) hv hvm
    rw [hcongr] at h
    exact h
  constructor
  · exact Finset.sum_le_sum fun b hb => (hper b hb).1
  · calc ∑ b ∈ Finset.range a,
          ((Finset.range (kk i)).filter
            (fun q => (fTW i + (b * kk i + q)) % k = c
              ∧ MatchesAt (fullDigW x) v (fTW i + (b * kk i + q)))).card
        ≤ ∑ b ∈ Finset.range a,
            (((Finset.range (kk i - v.length + 1)).filter
              (fun q => (fTW i + b * kk i + q) % k = c
                ∧ OccursAt 2 x v (fnthW i b + q))).card + v.length) :=
          Finset.sum_le_sum fun b hb => (hper b hb).2
      _ = fullGoodWPreR i a k c x v + a * v.length := by
          rw [Finset.sum_add_distrib, fullGoodWPreR]
          simp

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The full restricted read count at a mid-band cutoff.** -/
theorem fullW_prefix_winCountR_bounds (x : ℝ) (i a k c : ℕ) (v : List ℕ) (hv : 0 < v.length)
    (hvm : v.length ≤ kk i) (ha : a ≤ (winStartsW i).card) :
    fullGoodWPreR i a k c x v ≤ winCountR k c (fullDigW x) v (fTW i + a * kk i) ∧
      winCountR k c (fullDigW x) v (fTW i + a * kk i)
        ≤ fullGoodWPreR i a k c x v + fTW i + a * v.length := by
  classical
  have hle : fTW i ≤ fTW i + a * kk i := by omega
  have hsplit := winCountR_split k c (fullDigW x) v hle
  obtain ⟨h1, h2⟩ := fullW_band_prefix_winCountR_bounds x i a k c v hv hvm ha
  have hhist : winCountR k c (fullDigW x) v (fTW i) ≤ fTW i := winCountR_le _ _ _ _ _
  generalize hcc : a * v.length = e at h2 ⊢
  rw [hsplit]
  omega

/-! ### §3  The residue shift inside a window

Within window `b` of band `i`, the read position is `fTW i + b·kk i + q`, so the *read* class
`c` corresponds to the *local* class `locRes i k c b`. -/

/-- The local offset class inside window `b` that realises the read class `c`. -/
noncomputable def locRes (i k c b : ℕ) : ℕ := (c + k - (fTW i + b * kk i) % k) % k

/-- Shifting a residue by `t`, inside one period. -/
lemma mod_shift_iff {k c t r : ℕ} (hk : 0 < k) (hc : c < k) (ht : t < k) (hr : r < k) :
    (t + r) % k = c ↔ r = (c + k - t) % k := by
  have key : ∀ y, y < 2 * k → y % k = if y < k then y else y - k := by
    intro y hy
    rcases lt_or_ge y k with h | h
    · rw [if_pos h, Nat.mod_eq_of_lt h]
    · rw [if_neg (by omega), Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  rw [key (t + r) (by omega), key (c + k - t) (by omega)]
  split_ifs <;> omega

/-- **The residue shift.**  A read position in window `b` lies in class `c` iff its local
offset lies in class `locRes i k c b`. -/
lemma mem_res_iff_locRes (i k c b : ℕ) (hk : 0 < k) (hc : c < k) (q : ℕ) :
    (fTW i + b * kk i + q) % k = c ↔ q % k = locRes i k c b := by
  rw [locRes, Nat.add_mod (fTW i + b * kk i) q k]
  exact mod_shift_iff hk hc (Nat.mod_lt _ hk) (Nat.mod_lt _ hk)

/-- `locRes` depends on `b` only through `b % k`. -/
lemma locRes_mod (i k c b : ℕ) : locRes i k c b = locRes i k c (b % k) := by
  have h : (fTW i + b * kk i) % k = (fTW i + b % k * kk i) % k := by
    simp [Nat.add_mod, Nat.mul_mod]
  rw [locRes, locRes, h]

end NormalNumbers.G4.Sched
