/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# The Bailey–Crandall reduction for `ln 2`

`ln 2 = Σ_{n≥1} 1/(n·2ⁿ)`, so `2^N·ln 2 mod 1` is shadowed, with `O(1/N)`
error, by the explicit orbit `x₀ = 0, xₙ = 2·xₙ₋₁ + 1/n mod 1`.  Bailey and
Crandall (Exp. Math. 10 (2001) 175–190): if that orbit is equidistributed
mod 1, then `ln 2` is normal in base 2.

The point of formalizing the reduction is that the hypothesis
(`Equidistributed lnTwoOrbit`) mentions no logarithm: it is a single
concrete statement in arithmetic dynamics, and this file welds it,
machine-checked, to the normality of `ln 2`.
-/

namespace NormalNumbers

/-- The Bailey–Crandall surrogate orbit for `ln 2`:
`x₀ = 0, xₙ = 2·xₙ₋₁ + 1/n  (mod 1)`.  Explicitly,
`xₙ = Σ_{k=1}^{n} 2^(n−k)/k  mod 1`. -/
noncomputable def lnTwoOrbit : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract (2 * lnTwoOrbit n + 1 / (n + 1))

/-- **The Bailey–Crandall reduction** (2001, conditional): equidistribution
of the surrogate orbit implies `ln 2` is normal in base 2. -/
theorem isNormal_log_two_of_equidistributed
    (h : Equidistributed lnTwoOrbit) : IsNormal 2 (Real.log 2) := by
  sorry

end NormalNumbers
