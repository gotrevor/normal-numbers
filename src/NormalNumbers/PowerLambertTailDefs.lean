/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerDivisorCoefficients

/-- Count power divisors larger than a cutoff. -/
def NormalNumbers.ArithmeticDisjunctivity.tailPowerDivisorCount (r D n : ℕ) : ℕ :=
  (n.divisors.filter fun d => D < d ∧ d ^ r ∣ n).card

namespace NormalNumbers.ArithmeticDisjunctivity

theorem tailPowerDivisorCount_zero (r D : ℕ) : tailPowerDivisorCount r D 0 = 0 := by
  simp [tailPowerDivisorCount]

end NormalNumbers.ArithmeticDisjunctivity
