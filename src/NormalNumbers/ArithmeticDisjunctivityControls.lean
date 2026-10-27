/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticCoefficientLemmas
import NormalNumbers.JointLambertArithmetic

/-!
# Positive and negative controls for the arithmetic coefficient class

The ordinary divisor function satisfies the interface.  Constant positive
coefficients and prime-power values restricted to powers of two fail the
coefficient-writing condition.  These are statements about the interface,
not assertions that every excluded coefficient sequence lacks disjunctivity.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- The original Erdos--Borwein coefficients give a nonvacuous control. -/
@[blueprint (title := "Ordinary divisor counts satisfy the generic arithmetic interface")]
theorem tau_coefficientSystem : CoefficientSystem SwingC2.tau where
  zero := by simp [SwingC2.tau]
  one := by simp [SwingC2.tau]
  mul := fun _ _ h => SwingC2.tau_mul_coprime h
  bound := fun _ => le_rfl
  prime := ⟨2, Or.inr rfl, fun _ hp => SwingC2.tau_prime hp⟩
  values := by
    intro A hA
    refine ⟨A - 1, by omega, ?_⟩
    intro p hp
    rw [JointLambert.tau_prime_pow hp]
    omega

/-- The coefficients of the rational geometric series. -/
def unitCoefficients (n : ℕ) : ℕ := if n = 0 then 0 else 1

/-- The interface does not mistake a constant coefficient sequence for a
word-writing source. -/
theorem not_unit_coefficientSystem : ¬ CoefficientSystem unitCoefficients := by
  intro h
  obtain ⟨e, _, he⟩ := h.values 3 (by omega)
  have hx := he 2 (by norm_num)
  simp [unitCoefficients] at hx

/-- The single-coefficient writing hypothesis excludes the power-of-two
obstruction already encountered for squarefree-indexed Lambert sums. -/
@[blueprint (title := "Power-of-two prime-power values fail the generic writer hypothesis")]
theorem not_coefficientSystem_of_powTwo_values (f : ℕ → ℕ)
    (hpow : ∀ p e : ℕ, p.Prime → 1 ≤ e → ∃ k : ℕ, f (p ^ e) = 2 ^ k) :
    ¬ CoefficientSystem f := by
  intro h
  obtain ⟨e, he, hvalue⟩ := h.values 3 (by omega)
  obtain ⟨k, hk⟩ := hpow 2 e (by norm_num) he
  have hv := hvalue 2 (by norm_num)
  have hlt : k < 2 := by
    by_contra hnot
    have hh : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  interval_cases k <;> norm_num at hk <;> omega

end NormalNumbers.ArithmeticDisjunctivity
