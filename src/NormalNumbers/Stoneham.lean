/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# Stoneham's theorem

R. Stoneham (1973): `α₂,₃ = Σ_{n≥1} 1/(3ⁿ·2^(3ⁿ))` is normal in base 2 —
the only known normality proof for a number defined by an honest analytic
series rather than through its own digits.  The dynamical proof route is
Bailey–Crandall (Exp. Math. 11 (2002) 527–546): between the sparse kicks at
times `3ⁿ`, the orbit is pure doubling, and the discrepancy sums
geometrically.

(Contrast, for the eventual write-up: Bailey–Borwein showed `α₂,₃` is *not*
normal in base 6 — normality is a property of the pair (number, base).)
-/

namespace NormalNumbers

/-- The Stoneham constant `α₂,₃ = Σ_{n≥1} 1/(3ⁿ·2^(3ⁿ))`. -/
noncomputable def stoneham23 : ℝ :=
  ∑' n : ℕ, 1 / ((3 : ℝ) ^ (n + 1) * 2 ^ (3 ^ (n + 1)))

/-- **Stoneham's theorem** (1973): `α₂,₃` is normal in base 2. -/
theorem isNormal_two_stoneham23 : IsNormal 2 stoneham23 := by
  sorry

end NormalNumbers
