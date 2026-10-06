/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentStretch

/-!
# The BFR bet: does the stretch count say anything about rationals near `K`?

Ren, 2026-10-05 (`KICKOFF-2026-10-05-stretch-poke-ADDENDUM-bfr.md`).  Four findings, each a
declaration here, so the stretch lane can grind them:

1. **The exact residue count is the covering bound.**  `card_lowResidue_le` (≤ `2^{k+1}` Cantor
   numerators per `q`) is the classical count `card_near_cantor_le`: `K` at scale `1/q` has `2ⁿ`
   pieces, each holding ≤ 4 fractions `p/q`, so `N_K(Q, 1/Q) ≲ Q^{1 + dim K}`, the known trivial
   bound.  The count transfers nothing new to Broderick–Fishman–Reich (Maze, `vacuous`).
2. **`RunEnteringCount` and a Bugeaud–Durand count are siblings.**  BD-type counts see rationals
   near `K` at resolution ≥ the cylinder; `RunEnteringCount` counts rationals within
   `q^{−τ} < 3^{−b}` of the `2^b` discrete endpoints, a measure-zero set.  Neither implies the
   other as stated (Maze, `vacuous`, prose tier).
3. **Inverse Cantor sums cancel numerically.**  `invSumShift` at `A = 0`, `b' = b`: `max_{3∤n}
   |S|/|C|` falls from 0.276 (`b = 6`) to 0.036 (`b = 14`), about `√(log 3^b / |C|)`, while the
   direct Riesz sum stays at 0.466 (`experiments/cantor_inverse_sums.py`).  Frozen as
   `InverseCantorSumBound` for the shifted sets the window count uses; the probe has not tested
   `A ≠ 0`.
4. **Single-sum cancellation is not enough.**  `windowCount_of_inverseSum` gives the window count
   only when `m > b − δ b'`, and `singleSum_insufficient` shows that even square-root saving
   misses every window with `m ≤ b/2`, which is where the binding windows sit (`m ≈ b/τ`).  So
   `RunEnteringCount` needs a bilinear estimate (Maze, `refuted`).
-/

open MeasureTheory Filter

namespace NormalNumbers.StretchBFR

open CantorExactExponentStretch

/-- Exponential sum over the inverses mod `3^b` of `A·3^{b'} + P`, `P` a depth-`b'` Cantor
numerator, over the terms prime to 3. -/
noncomputable def invSumShift (b b' A n : ℕ) : ℂ :=
  ∑ P ∈ (cantorInts b').filter (fun P => ¬ 3 ∣ A * 3 ^ b' + P),
    Complex.exp (2 * Real.pi * Complex.I *
      ((((n * (((A * 3 ^ b' + P : ℕ) : ZMod (3 ^ b))⁻¹).val : ℕ) : ℝ) / (3 : ℝ) ^ b : ℝ) : ℂ))

/-- **Inverse Cantor sums have a power saving**, uniformly over prefixes.  Confidence 60% (probe:
`A = 0`, `b' = b ≤ 14` only, consistent with square-root cancellation). -/
def InverseCantorSumBound (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ C : ℝ, ∀ b b' A n : ℕ, b' ≤ b → ¬ 3 ∣ n →
    ‖invSumShift b b' A n‖ ≤ C * 2 ^ b' * (3 : ℝ) ^ (-(δ * b'))

open Classical in
/-- The run-entering window count of `RunEnteringCountAt`, as a function. -/
noncomputable def windowCount (τ : ℝ) (A b b' m : ℕ) : ℕ :=
  ((cantorInts b').filter fun P => ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 3 ^ (m + 1) ∧ ∃ r : ℤ, r ≠ 0 ∧
      |(r : ℝ)| < 3 ^ b * (q : ℝ) ^ (1 - τ) ∧
      ((A * 3 ^ b' + P : ℕ) * q : ℤ) ≡ r [ZMOD 3 ^ b]).card

/-- **From inverse-sum cancellation to the window count.**  Confidence 80%.

English proof.  `P q ≡ r` iff `q ≡ r · P̄`.  Count pairs `(P, r)` with `r P̄ mod 3^b` in the
`q`-interval `I` (length `2·3ᵐ`), expand `1_I` in additive characters mod `3^b`
(`Σ_h |Î(h)| ≲ 3^b log 3^b`), and group `n = h r`: the `h = 0` term is the main term
`2^{b'} · #r · |I| / 3^b ≲ 2^{b'} 3^{(2−τ)m}`, and every other term is an `invSumShift`, bounded
by the hypothesis.  Error `≲ #r · 2^{b'} 3^{−δ b'} · (b + 1)` with `#r ≤ 2·3^{b−(τ−1)m}`. -/
theorem windowCount_of_inverseSum (δ : ℝ) (hS : InverseCantorSumBound δ) (τ : ℝ) (hτ : 2 < τ) :
    ∃ C : ℝ, ∀ A b b' m : ℕ, b' ≤ b → ((τ - 1) * m : ℝ) ≤ b →
      (windowCount τ A b b' m : ℝ) ≤
        C * (2 ^ b' * (3 : ℝ) ^ ((2 - τ) * m) +
          (3 : ℝ) ^ (b - (τ - 1) * m) * 2 ^ b' * (3 : ℝ) ^ (-(δ * b')) * (b + 1)) := by
  sorry

/-- **Single-sum cancellation cannot reach the bottom windows.**  The error term of
`windowCount_of_inverseSum` beats the main term only when `m > b − δ b'`.  With at most
square-root saving (`δ ≤ ½ log₃ 2 < ½`) and `m ≤ b/2`, that fails: `m ≤ b − δ b'`. -/
theorem singleSum_insufficient (δ b b' m : ℝ) (hδ : δ ≤ Real.logb 3 2 / 2)
    (hb' : b' ≤ b) (hb'0 : 0 ≤ b') (hm : m ≤ b / 2) : m ≤ b - δ * b' := by
  have hlog : Real.logb 3 2 < 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    norm_num
  have hδ1 : δ ≤ 1 / 2 := by linarith
  have : δ * b' ≤ b / 2 := by nlinarith
  linarith

open Classical in
/-- **The covering bound.**  For `q ≤ 3ⁿ`, at most `4 · 2ⁿ` fractions `p/q ∈ [0, 1]` lie within
`1/q` of the Cantor set.  Confidence 95%.  English proof: `K` is covered by the `2ⁿ` depth-`n`
intervals of length `3^{−n} ≤ 1/q`; the `1/q`-neighbourhood of each has length `< 3/q`, so holds
at most 4 points of `(1/q)ℤ`.  This is what `card_lowResidue_le` is, in BFR terms. -/
theorem card_near_cantor_le (q n : ℕ) (hq : 0 < q) (hn : q ≤ 3 ^ n) :
    ((Finset.range (q + 1)).filter fun p : ℕ =>
        ∃ x ∈ cantorSet, |x - (p : ℝ) / q| < 1 / q).card ≤ 4 * 2 ^ n := by
  sorry

end NormalNumbers.StretchBFR
