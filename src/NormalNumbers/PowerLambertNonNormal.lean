/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertDisjunctivity
import NormalNumbers.PowerLambertTailExpansion
import NormalNumbers.PowerLambertTailCoefficients
import NormalNumbers.SmallCoefficientMean
import NormalNumbers.ArithmeticMeanObstruction
import NormalNumbers.WallRational

/-!
# The perfect-power Lambert normality boundary

The square and higher-power series have summably sparse source indices.
Removing a finite rational head leaves coefficients with a small summatory
bound.  Their orbit means cannot have the distribution required by normality.
Read `MAZE.md` and `docs/power-lambert-normality.md` before attempting to
upgrade the disjunctivity theorem for this particular family.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- The small-mean tail contradicts normality, which rational translation
would preserve.  The condition `r>=2` is essential to this proof. -/
@[blueprint (title := "Square and higher-power Lambert series are not normal in their defining bases")]
theorem not_isNormal_powerLambert (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ¬ IsNormal b (powerLambert b r) := by
  intro hnormal
  obtain ⟨q, hsplit⟩ := exists_rat_powerLambert_tail b r hb hr
  have htail := isNormal_rat_mul_add b hb (powerLambert b r) 1 (-q) (by norm_num) hnormal
  have htail' : IsNormal b (coefficientValue (tailPowerDivisorCount r 8) b) := by
    simpa [hsplit] using htail
  exact not_isNormal_of_orbit_sum_bound b hb _
    (orbit_sum_le_of_small_coefficients b hb _ (tailPowerDivisorCount_zero r 8)
      (prefix_tailPowerDivisorCount_bound r hr)) htail'

/-- An explicit arithmetic family separating disjunctivity from normality. -/
@[blueprint (title := "Perfect-power Lambert constants are disjunctive and nonnormal")]
theorem powerLambert_disjunctive_not_normal (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsDisjunctive b (powerLambert b r) ∧ ¬ IsNormal b (powerLambert b r) :=
  ⟨isDisjunctive_powerLambert b r hb (by omega), not_isNormal_powerLambert b r hb hr⟩

/-- The tempting general strengthening, stated so its failure is explicit. -/
def GenericArithmeticNormality : Prop :=
  ∀ f : ℕ → ℕ, CoefficientSystem f → ∀ b : ℕ, 2 ≤ b →
    IsNormal b (coefficientValue f b)

/-- The arithmetic hypotheses of the disjunctivity theorem do not imply
normality; the square-divisor coefficient system is a counterexample. -/
@[blueprint (title := "The generic arithmetic disjunctivity hypotheses do not imply normality")]
theorem not_genericArithmeticNormality : ¬ GenericArithmeticNormality := by
  intro h
  have hn := h (powerDivisorCount 2) (powerDivisorCount_system 2 (by omega)) 2 (by omega)
  apply not_isNormal_powerLambert 2 2 (by omega) (by omega)
  exact (congrArg (IsNormal 2)
    (powerLambert_eq_coefficientValue (b := 2) (r := 2) (by omega) (by omega))).mpr hn

/-- The summatory estimate used here already fails at a small finite
input for `r=1`.  The argument makes no claim about that member's normality. -/
theorem linear_power_prefix_control :
    (∑ n ∈ Finset.range 12, tailPowerDivisorCount 1 8 n) = 3 := by
  decide

/-- The square tail has nonzero arithmetic coefficients despite its
small average; it has not disappeared after the rational head removal. -/
theorem square_tail_positive_control : tailPowerDivisorCount 2 8 81 = 1 := by
  decide

end NormalNumbers.ArithmeticDisjunctivity
