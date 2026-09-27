/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion

/-!
# Wall: rational affine maps preserve normality

D. D. Wall (1949 thesis): if `x` is normal in base `b` and `q ≠ 0`, `r` are rational, then
`q * x + r` is normal in base `b`.  `Maze.lean` cited this ("normality survives rational
multiplication") as a `.cited` row; this file proves it.

Suggested route (not binding):
* integer multiplier `m ≠ 0`: via `isNormal_iff_equidistributed_orbit` and Weyl, since
  `orbit b (m * x) n = m * orbit b x n mod 1` and `e(h·m·y)` is a Weyl test for `y`;
* adding a rational and dividing by an integer are the real lemmas; the standard proofs
  go through normality in base `b^k` or through subsequences along progressions.
-/

namespace NormalNumbers

/-- **Wall (1949)**: rational affine maps preserve base-`b` normality. -/
theorem isNormal_rat_mul_add (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (q r : ℚ) (hq : q ≠ 0)
    (hx : IsNormal b x) : IsNormal b ((q : ℝ) * x + r) := by
  sorry

end NormalNumbers
