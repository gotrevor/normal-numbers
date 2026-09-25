import NormalNumbers.ElliottDilatedRung
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.SmoothNumbers

/-!
# The crude Euler-product bound for a nonnegative multiplicative function

Step (a) of the leaf-2 attack order (`PENDING_WORK.md` Finding 2): for a nonnegative multiplicative
`f`, the truncated sum `∑_{m ≤ Y} f m` is bounded by the finite Euler product
`∏_{p ≤ Y} ∑_{k ≤ K} f (p^k)`, `K = ⌊log₂ Y⌋`.

mathlib has no partial-sum Euler expansion, so the route is the recipe of
`lean-primorial-sq-divisor-euler-product`: every `1 ≤ m ≤ Y` divides
`N = ∏_{p ≤ Y} p^K`, and a divisor sum *is* evaluable — `↑ζ * f` is multiplicative, its value at
`N` is the divisor sum, and `IsMultiplicative.map_prod` over the pairwise-coprime prime powers
turns it into the product of local factors.

This is the elementary half of Case A of `NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM`:
combined with `∏_{p ≤ Y} (1 + f p + …) ≪ log Y · exp(-Σ_Y)` it settles the regime
`log W ≥ θ log X` outright.  The thin-window regime needs Hall's inequality and is still open.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottEulerBound

open ArithmeticFunction
open scoped ArithmeticFunction
open scoped Function

/-- Every `1 ≤ m ≤ Y` has all its prime exponents `≤ log₂ Y`. -/
theorem factorization_le_log {Y m : ℕ} (hm : 1 ≤ m) (hmY : m ≤ Y) (p : ℕ) :
    m.factorization p ≤ Nat.log 2 Y := by
  by_cases hp : p.Prime
  · have hdvd : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
    have hple : 2 ≤ p := hp.two_le
    have h1 : 2 ^ m.factorization p ≤ p ^ m.factorization p :=
      Nat.pow_le_pow_left hple _
    have h2 : p ^ m.factorization p ≤ m := Nat.le_of_dvd (by omega) hdvd
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The `log₂ Y`-th power of the primorial: every `1 ≤ m ≤ Y` divides it. -/
noncomputable def eulerModulus (Y : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow (Y + 1), p ^ Nat.log 2 Y

theorem eulerModulus_ne_zero (Y : ℕ) : eulerModulus Y ≠ 0 := by
  rw [eulerModulus]
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  have := (Nat.mem_primesBelow.mp hp).2
  exact pow_ne_zero _ this.pos.ne'

theorem dvd_eulerModulus {Y m : ℕ} (hm : 1 ≤ m) (hmY : m ≤ Y) : m ∣ eulerModulus Y := by
  refine (Nat.factorization_prime_le_iff_dvd (by omega) (eulerModulus_ne_zero Y)).mp ?_
  intro p hp
  by_cases hpm : p ∣ m
  · have hpY : p < Y + 1 := by
      have := Nat.le_of_dvd (by omega) hpm
      omega
    have hmem : p ∈ Nat.primesBelow (Y + 1) := Nat.mem_primesBelow.mpr ⟨hpY, hp⟩
    have hpow : p ^ Nat.log 2 Y ∣ eulerModulus Y := by
      rw [eulerModulus]; exact Finset.dvd_prod_of_mem _ hmem
    have hKle : Nat.log 2 Y ≤ (eulerModulus Y).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp (eulerModulus_ne_zero Y)).mp hpow
    exact (factorization_le_log hm hmY p).trans hKle
  · simp [Nat.factorization_eq_zero_of_not_dvd hpm]

/-- **The crude Euler-product bound.**  For a nonnegative multiplicative `f`,
`∑_{m ≤ Y} f m ≤ ∏_{p ≤ Y} ∑_{k ≤ log₂ Y} f (p^k)`. -/
theorem sum_Icc_le_euler_product {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hnn : ∀ n : ℕ, 0 ≤ f n) (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, f m ≤
      ∏ p ∈ Nat.primesBelow (Y + 1), ∑ k ∈ Finset.range (Nat.log 2 Y + 1), f (p ^ k) := by
  classical
  set K := Nat.log 2 Y with hK
  set N := eulerModulus Y with hN
  have hNne : N ≠ 0 := eulerModulus_ne_zero Y
  -- the truncated sum is dominated by the divisor sum of `N`
  have hsub : Finset.Icc 1 Y ⊆ N.divisors := by
    intro m hm
    obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp hm
    exact Nat.mem_divisors.mpr ⟨dvd_eulerModulus hm1 hmY, hNne⟩
  have hstep : ∑ m ∈ Finset.Icc 1 Y, f m ≤ ∑ d ∈ N.divisors, f d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦ hnn i)
  -- the divisor sum factors
  have hzf : ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul hf
  have hdiv : ∑ d ∈ N.divisors, f d = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) N :=
    coe_zeta_mul_apply.symm
  have hcop : ((Nat.primesBelow (Y + 1) : Finset ℕ) : Set ℕ).Pairwise
      (Nat.Coprime on fun p ↦ p ^ K) := by
    intro p hp q hq hne
    have hpp := (Nat.mem_primesBelow.mp (by exact_mod_cast hp)).2
    have hqp := (Nat.mem_primesBelow.mp (by exact_mod_cast hq)).2
    exact Nat.Coprime.pow K K ((Nat.coprime_primes hpp hqp).mpr hne)
  have hprod : ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) N =
      ∏ p ∈ Nat.primesBelow (Y + 1), ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) (p ^ K) := by
    rw [hN, eulerModulus, ← hK]
    exact hzf.map_prod (fun p ↦ p ^ K) _ hcop
  have hlocal : ∀ p ∈ Nat.primesBelow (Y + 1),
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) (p ^ K) =
        ∑ k ∈ Finset.range (K + 1), f (p ^ k) := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp]
  calc ∑ m ∈ Finset.Icc 1 Y, f m ≤ ∑ d ∈ N.divisors, f d := hstep
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) N := hdiv
    _ = ∏ p ∈ Nat.primesBelow (Y + 1), ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) (p ^ K) := hprod
    _ = _ := Finset.prod_congr rfl hlocal

end NormalNumbers.ElliottEulerBound

#print axioms NormalNumbers.ElliottEulerBound.sum_Icc_le_euler_product
