/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.Counting

/-!
# The Walsh / parity criterion for binary normality

Normality says one measure looks like Haar measure in **two** duals: the circle's characters
(Weyl sums, `WeylCriterion.lean`) and the digit group's characters (Walsh–Hadamard, here).
This file develops the digit side for base two.

For a binary digit sequence `s` and a finite offset set `S`, the **parity correlation** is

  `parityMean s S N = (1/N) ∑_{n < N} ∏_{i ∈ S} (-1)^(s (n+i))`.

The central fact is finite and exact — no analysis, no Erdős–Turán truncation loss, because
both sides live on the same finite group:

* `prod_one_add_eq` : `∏_{i<L} (1 + ε_i δ_i) = 2^L` when the block matches and `0` otherwise;
* `matchesAt_indicator_eq` : the indicator of a length-`L` block is the Hadamard transform of
  the parity characters (`Verdict` §2 of `Maze.lean` calls the circle-side blindness this
  fact repairs).

Design note and the two finite inequalities it feeds:
`DESIGN-2026-09-20-walsh-weyl-bridge.md`.  The identity is verified to machine precision on
five sequences by `experiments/walsh_parity_identity.py`, with hand-computed Parry values in
the accompanying test.
-/

namespace NormalNumbers.Walsh

open Finset

variable {s : ℕ → ℕ}

/-- The parity character of `s` at offset set `S`, read at position `n`. -/
def parityChar (s : ℕ → ℕ) (S : Finset ℕ) (n : ℕ) : ℝ := ∏ i ∈ S, (-1 : ℝ) ^ s (n + i)

/-- The parity correlation (Walsh mean) of `s` over `S` across the first `N` positions. -/
noncomputable def parityMean (s : ℕ → ℕ) (S : Finset ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, parityChar s S n) / N

/-- The sign attached to a block `w` by the offset set `S`. -/
def blockSign (w : List ℕ) (S : Finset ℕ) : ℝ := ∏ i ∈ S, (-1 : ℝ) ^ w.getD i 0

@[simp] theorem parityChar_empty (s : ℕ → ℕ) (n : ℕ) : parityChar s ∅ n = 1 := by
  simp [parityChar]

@[simp] theorem blockSign_empty (w : List ℕ) : blockSign w ∅ = 1 := by simp [blockSign]

/-- A binary digit contributes `±1`, never anything else. -/
theorem neg_one_pow_eq_of_lt_two {a : ℕ} (ha : a < 2) :
    (-1 : ℝ) ^ a = if a = 0 then 1 else -1 := by
  interval_cases a <;> norm_num

/-- For binary digits, `(-1)^a * (-1)^b = 1` exactly when `a = b`. -/
theorem neg_one_pow_mul_self {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    (-1 : ℝ) ^ a * (-1) ^ b = if a = b then 1 else -1 := by
  interval_cases a <;> interval_cases b <;> norm_num

/-- A fitting `getD` lands in the list, so block-digit hypotheses apply to it. -/
theorem getD_mem_of_lt {w : List ℕ} {i : ℕ} (hi : i < w.length) : w.getD i 0 ∈ w := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **The pointwise product collapse.**  Each factor `1 + (-1)^{w_i}(-1)^{s(n+i)}` is `2`
on agreement and `0` on disagreement, so the product over a window is `2^L` exactly when the
block matches and `0` otherwise.  This is the whole content of the Hadamard identity. -/
theorem prod_one_add_eq (s : ℕ → ℕ) (w : List ℕ) (n : ℕ)
    (hs : ∀ m, s m < 2) (hw : ∀ d ∈ w, d < 2) :
    ∏ i ∈ range w.length, (1 + (-1 : ℝ) ^ w.getD i 0 * (-1) ^ s (n + i))
      = if MatchesAt s w n then 2 ^ w.length else 0 := by
  by_cases hm : MatchesAt s w n
  · rw [if_pos hm]
    rw [Finset.prod_congr rfl (fun i hi => ?_), Finset.prod_const, card_range]
    have hi' : i < w.length := mem_range.mp hi
    have hwi : w.getD i 0 < 2 := hw _ (getD_mem_of_lt hi')
    rw [hm i hi', neg_one_pow_mul_self hwi hwi, if_pos rfl]
    norm_num
  · rw [if_neg hm]
    simp only [MatchesAt, not_forall] at hm
    obtain ⟨j, hj, hne⟩ := hm
    have hj' : j < w.length := by simpa using hj
    refine Finset.prod_eq_zero (mem_range.mpr hj') ?_
    have hwj : w.getD j 0 < 2 := hw _ (getD_mem_of_lt hj')
    have hne' : s (n + j) ≠ w.getD j 0 := by simpa using hne
    rw [mul_comm, neg_one_pow_mul_self (hs _) hwj, if_neg hne']
    norm_num

/-- **The Hadamard expansion of a block indicator.**  The indicator of `w` occurring at `n`
is the average of the parity characters over all offset subsets of the window, signed by `w`.

This is the exact, finite bridge between the two duals: block frequencies on one side, parity
correlations on the other.  Unlike Erdős–Turán there is no truncation term. -/
theorem matchesAt_indicator_eq (s : ℕ → ℕ) (w : List ℕ) (n : ℕ)
    (hs : ∀ m, s m < 2) (hw : ∀ d ∈ w, d < 2) :
    (if MatchesAt s w n then (1 : ℝ) else 0)
      = (2 ^ w.length)⁻¹ * ∑ S ∈ (range w.length).powerset,
          blockSign w S * parityChar s S n := by
  have hexp : ∀ S ∈ (range w.length).powerset,
      blockSign w S * parityChar s S n
        = ∏ i ∈ S, ((-1 : ℝ) ^ w.getD i 0 * (-1) ^ s (n + i)) := by
    intro S _
    rw [blockSign, parityChar, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl hexp]
  have hprod : ∏ i ∈ range w.length, ((-1 : ℝ) ^ w.getD i 0 * (-1) ^ s (n + i) + 1)
      = ∑ S ∈ (range w.length).powerset,
          ∏ i ∈ S, ((-1 : ℝ) ^ w.getD i 0 * (-1) ^ s (n + i)) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl (fun S _ => by simp)
  rw [← hprod]
  have : ∀ i, ((-1 : ℝ) ^ w.getD i 0 * (-1) ^ s (n + i) + 1)
      = (1 + (-1 : ℝ) ^ w.getD i 0 * (-1) ^ s (n + i)) := fun i => by ring
  simp only [this]
  rw [prod_one_add_eq s w n hs hw]
  by_cases hm : MatchesAt s w n
  · rw [if_pos hm, if_pos hm]
    field_simp
  · rw [if_neg hm, if_neg hm, mul_zero]

/-! ## The summed transform and the two finite inequalities -/

/-- Occurrences of `w` among the first `N` positions, unclipped (windows may overrun `N`).
`Counting.card_filter_matchesAt_le` bounds the difference from `countOccurrences` by
`w.length`, an `O(1)` boundary term that dies after division by `N`. -/
def blockCount (s : ℕ → ℕ) (w : List ℕ) (N : ℕ) : ℕ :=
  ((range N).filter (MatchesAt s w)).card

/-- Frequency of `w` among the first `N` positions. -/
noncomputable def blockMean (s : ℕ → ℕ) (w : List ℕ) (N : ℕ) : ℝ := (blockCount s w N : ℝ) / N

@[simp] theorem parityMean_empty_of_pos (s : ℕ → ℕ) {N : ℕ} (hN : 0 < N) :
    parityMean s ∅ N = 1 := by
  simp [parityMean, Nat.cast_ne_zero.mpr hN.ne']

/-- **The transform, summed.**  Block frequency is the signed average of the parity
correlations over all offset subsets of the window.  Exact at every finite `N`. -/
theorem blockMean_eq (s : ℕ → ℕ) (w : List ℕ) (N : ℕ)
    (hs : ∀ m, s m < 2) (hw : ∀ d ∈ w, d < 2) :
    blockMean s w N
      = (2 ^ w.length)⁻¹ * ∑ S ∈ (range w.length).powerset,
          blockSign w S * parityMean s S N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [blockMean, parityMean, blockCount]
  have hcount : (blockCount s w N : ℝ)
      = ∑ n ∈ range N, (if MatchesAt s w n then (1 : ℝ) else 0) := by
    rw [blockCount, Finset.card_filter]
    push_cast
    simp
  rw [blockMean, hcount,
    Finset.sum_congr rfl (fun n _ => matchesAt_indicator_eq s w n hs hw),
    ← Finset.mul_sum, mul_div_assoc]
  congr 1
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Finset.mul_sum, parityMean, mul_div_assoc]

/-- Splitting the empty offset set out of the transform. -/
theorem blockMean_sub_eq (s : ℕ → ℕ) (w : List ℕ) {N : ℕ} (hN : 0 < N)
    (hs : ∀ m, s m < 2) (hw : ∀ d ∈ w, d < 2) :
    blockMean s w N - (2 ^ w.length)⁻¹
      = (2 ^ w.length)⁻¹ * ∑ S ∈ (range w.length).powerset.erase ∅,
          blockSign w S * parityMean s S N := by
  rw [blockMean_eq s w N hs hw]
  have hmem : (∅ : Finset ℕ) ∈ (range w.length).powerset := by simp
  rw [← Finset.add_sum_erase _ _ hmem, blockSign_empty, parityMean_empty_of_pos s hN]
  ring

/-- **Inequality (A).**  Every block frequency is controlled by the parity correlations: if
all nonempty parity correlations are small, no block can be over- or under-represented. -/
theorem abs_blockMean_sub_le (s : ℕ → ℕ) (w : List ℕ) {N : ℕ} (hN : 0 < N)
    (hs : ∀ m, s m < 2) (hw : ∀ d ∈ w, d < 2) :
    |blockMean s w N - (2 ^ w.length)⁻¹|
      ≤ (2 ^ w.length)⁻¹ * ∑ S ∈ (range w.length).powerset.erase ∅, |parityMean s S N| := by
  rw [blockMean_sub_eq s w hN hs hw, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 ^ w.length)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun S _ => ?_))
  rw [abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [blockSign, abs_prod]
  refine Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ?_)
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-! ## The criterion: vanishing parity correlations force normality -/

open Filter Topology

/-- The finite sum of nonempty parity correlations vanishes when each summand does. -/
theorem tendsto_sum_abs_parityMean (s : ℕ → ℕ) (L : ℕ)
    (h : ∀ S : Finset ℕ, S.Nonempty → Tendsto (parityMean s S) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ S ∈ (range L).powerset.erase ∅, |parityMean s S N|)
      atTop (𝓝 0) := by
  have : Tendsto (fun N => ∑ S ∈ (range L).powerset.erase ∅, |parityMean s S N|)
      atTop (𝓝 (∑ S ∈ (range L).powerset.erase ∅, (0 : ℝ))) := by
    refine tendsto_finset_sum _ (fun S hS => ?_)
    have hne : S.Nonempty := by
      rcases Finset.eq_empty_or_nonempty S with rfl | hne
      · exact absurd rfl (Finset.ne_of_mem_erase hS)
      · exact hne
    simpa using (h S hne).abs
  simpa using this

/-- **Block frequencies converge.**  If every nonempty parity correlation vanishes then every
binary block of length `L` occurs with frequency tending to `2⁻ᴸ`. -/
theorem tendsto_blockMean (s : ℕ → ℕ) (w : List ℕ)
    (hs : ∀ m, s m < 2) (hw : ∀ d ∈ w, d < 2)
    (h : ∀ S : Finset ℕ, S.Nonempty → Tendsto (parityMean s S) atTop (𝓝 0)) :
    Tendsto (blockMean s w) atTop (𝓝 ((2 ^ w.length : ℝ))⁻¹) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hmaj : Tendsto
      (fun N => (2 ^ w.length : ℝ)⁻¹ *
        ∑ S ∈ (range w.length).powerset.erase ∅, |parityMean s S N|) atTop (𝓝 0) := by
    simpa using (tendsto_sum_abs_parityMean s w.length h).const_mul ((2 ^ w.length : ℝ)⁻¹)
  refine squeeze_zero' (Eventually.of_forall (fun N => dist_nonneg)) ?_ hmaj
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.dist_eq]
  exact abs_blockMean_sub_le s w hN hs hw

/-- The clipped and unclipped window counts differ by at most `w.length`. -/
theorem abs_count_sub_blockCount_le (s : ℕ → ℕ) {w : List ℕ} (hw : w ≠ []) (N : ℕ) :
    |(countOccurrences w ((List.range N).map s) : ℝ) - (blockCount s w N : ℝ)|
      ≤ (w.length : ℝ) := by
  obtain ⟨h1, h2⟩ := card_filter_matchesAt_le s w hw N
  have h1' : (countOccurrences w ((List.range N).map s) : ℝ) ≤ (blockCount s w N : ℝ) := by
    simp only [blockCount]; exact_mod_cast h1
  have h2' : (blockCount s w N : ℝ)
      ≤ (countOccurrences w ((List.range N).map s) : ℝ) + (w.length : ℝ) := by
    simp only [blockCount]; exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- 🎯 **The Walsh criterion, sufficiency.**  A binary digit sequence whose every nonempty
parity correlation vanishes is normal in base two.

This is the digit-dual counterpart of `equidistributed_of_weyl`: the same conclusion reached
through the characters of the digit group rather than those of the circle.  The transfer is
lossless — `abs_blockMean_sub_le` carries no Erdős–Turán truncation term — and the only
analysis in the whole file is the `O(1)/N` boundary correction below. -/
theorem isNormalSequence_two_of_parityMean_tendsto (s : ℕ → ℕ) (hs : ∀ m, s m < 2)
    (h : ∀ S : Finset ℕ, S.Nonempty → Tendsto (parityMean s S) atTop (𝓝 0)) :
    IsNormalSequence 2 s := by
  intro w hwne hw
  have hmain : Tendsto (blockMean s w) atTop (𝓝 ((2 ^ w.length : ℝ))⁻¹) :=
    tendsto_blockMean s w hs hw h
  have hdiff : Tendsto
      (fun N => (countOccurrences w ((List.range N).map s) : ℝ) / N - blockMean s w N)
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ => (w.length : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, blockMean, div_sub_div_same, abs_div, abs_of_pos hNpos]
    gcongr
    exact abs_count_sub_blockCount_le s hwne N
  have := hmain.add hdiff
  simp only [add_zero] at this
  convert this using 2 with N
  · ring
  · norm_num

end NormalNumbers.Walsh
