/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticDisjunctivityDefs
import NormalNumbers.PowerDivisorMultiplicativity

/-!
# Power-divisor coefficients

For `r ≥ 1`, the coefficient at `n` counts the positive integers whose
`r`-th power divides `n`.  This file records the arithmetic properties needed
by the generic coefficient theorem.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- Number of positive `r`-th roots of power divisors of `n`. -/
def powerDivisorCount (r n : ℕ) : ℕ :=
  (n.divisors.filter fun d => d ^ r ∣ n).card

theorem powerDivisorCount_zero (r : ℕ) : powerDivisorCount r 0 = 0 := by
  simp [powerDivisorCount]

theorem powerDivisorCount_one (r : ℕ) (_hr : 1 ≤ r) : powerDivisorCount r 1 = 1 := by
  simp [powerDivisorCount, Nat.divisors_one, Finset.filter_singleton]

theorem powerDivisorCount_le_tau (r n : ℕ) :
    powerDivisorCount r n ≤ NormalNumbers.SwingC2.tau n := by
  exact Finset.card_filter_le _ _

theorem powerDivisorCount_primePow (r e : ℕ) (hr : 1 ≤ r)
    {p : ℕ} (hp : p.Prime) :
    powerDivisorCount r (p ^ e) = e / r + 1 := by
  classical
  rw [powerDivisorCount, Nat.divisors_prime_pow hp]
  rw [Finset.filter_map]
  simp only [Finset.card_map]
  have hcond : ∀ i, ((p ^ i) ^ r ∣ p ^ e) ↔ i ≤ e / r := by
    intro i
    rw [← pow_mul, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    exact (Nat.le_div_iff_mul_le (by omega)).symm
  simp only [Function.comp_apply]
  change (((Finset.range (e + 1)).filter
    (fun i => (p ^ i) ^ r ∣ p ^ e)).card) = _
  simp_rw [hcond]
  have hq : e / r ≤ e := Nat.div_le_self _ _
  have hfilter : (Finset.range (e + 1)).filter (fun i => i ≤ e / r) =
      Finset.range (e / r + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  simp

@[blueprint (title := "Power-divisor counts satisfy the generic arithmetic hypotheses")]
theorem powerDivisorCount_system (r : ℕ) (hr : 1 ≤ r) :
    CoefficientSystem (powerDivisorCount r) := by
  refine ⟨powerDivisorCount_zero r, powerDivisorCount_one r hr, ?_,
    powerDivisorCount_le_tau r, ?_, ?_⟩
  · intro m n hcop
    simpa [powerDivisorCount] using powerDivisorCard_mul r hr m n hcop
  · by_cases hr1 : r = 1
    · subst r
      refine ⟨2, Or.inr rfl, ?_⟩
      intro p hp
      simpa using powerDivisorCount_primePow 1 1 (by omega) hp
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro p hp
      have hdiv : 1 / r = 0 := Nat.div_eq_of_lt (by omega)
      simpa [hdiv] using powerDivisorCount_primePow r 1 hr hp
  · intro A hA
    refine ⟨r * (A - 1), ?_, ?_⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · intro p hp
      rw [powerDivisorCount_primePow r (r * (A - 1)) hr hp]
      have hr0 : 0 < r := by omega
      rw [Nat.mul_div_cancel_left (A - 1) hr0]
      omega

end NormalNumbers.ArithmeticDisjunctivity
