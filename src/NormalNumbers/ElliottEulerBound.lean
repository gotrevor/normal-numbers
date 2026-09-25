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

/-! ## From the Euler product to `exp(∑_p f p)` -/

/-- The telescoping sum `∑_{2 ≤ n ≤ Y} 1/(n(n-1)) = 1 - 1/Y`. -/
theorem sum_Icc_inv_mul_pred (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 2 Y, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (Y : ℝ) := by
  induction Y with
  | zero => omega
  | succ Y ih =>
    rcases Nat.eq_or_lt_of_le hY with h1 | h1
    · have : Y = 0 := by omega
      subst this
      norm_num
    · have hY1 : 1 ≤ Y := by omega
      have hins : Finset.Icc 2 (Y + 1) = insert (Y + 1) (Finset.Icc 2 Y) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (Y + 1) ∉ Finset.Icc 2 Y := by simp
      rw [hins, Finset.sum_insert hnot, ih hY1]
      have hYr : (0 : ℝ) < Y := by exact_mod_cast hY1
      have hcast : (((Y + 1 : ℕ) : ℝ)) = (Y : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      field_simp
      rw [show (Y : ℝ) + 1 - 1 = (Y : ℝ) by ring, div_self hYr.ne']
      ring

/-- The prime tail `∑_{p ≤ Y} 1/(p(p-1)) ≤ 1`. -/
theorem sum_primesBelow_inv_mul_pred_le_one (Y : ℕ) :
    ∑ p ∈ Nat.primesBelow (Y + 1), (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos Y with hY | hY
  · subst hY
    simp [Nat.primesBelow_one]
  have hsub : Nat.primesBelow (Y + 1) ⊆ Finset.Icc 2 Y := by
    intro p hp
    obtain ⟨hpY, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.two_le, by omega⟩
  have hnn : ∀ n ∈ Finset.Icc 2 Y, n ∉ Nat.primesBelow (Y + 1) →
      0 ≤ (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn _
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
    have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    exact le_of_lt (by positivity)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  rw [sum_Icc_inv_mul_pred Y hY] at hle
  have : (0 : ℝ) ≤ 1 / (Y : ℝ) := by positivity
  linarith

/-- **The local factor bound.**  For `f` multiplicative with `f n ≤ 1/n`, the `p`-local Euler
factor is at most `1 + f p + 1/(p(p-1))`. -/
theorem local_factor_le {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hnn : ∀ n : ℕ, 0 ≤ f n) (hbd : ∀ n : ℕ, 0 < n → f n ≤ 1 / (n : ℝ))
    {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), f (p ^ k) ≤ 1 + f p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  classical
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / (p : ℝ) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hppos]; linarith
  rcases Nat.lt_or_ge K 2 with hK | hK
  · -- `K ≤ 1`: only the terms `k = 0, 1` occur
    have htail : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    interval_cases K
    · rw [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, hf.map_one]
      linarith [hnn p, htail]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, pow_one, hf.map_one]
      linarith
  · -- split off `k = 0, 1` and bound the rest geometrically
    have hsplit : ∑ k ∈ Finset.range (K + 1), f (p ^ k) =
        f 1 + f p + ∑ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) := by
      have h1 : Finset.range (K + 1) = Finset.range 2 ∪ Finset.Ico 2 (K + 1) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico] <;> omega
      rw [h1, Finset.sum_union (by
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive 0 2 (K + 1))]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp
    have htailbd : ∑ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) ≤
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have hterm : ∀ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) ≤ r ^ k := by
        intro k hk
        have hkpos : 0 < p ^ k := pow_pos hp.pos k
        have := hbd (p ^ k) hkpos
        have hcast : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by push_cast; ring
        rw [hcast] at this
        calc f (p ^ k) ≤ 1 / (p : ℝ) ^ k := this
          _ = r ^ k := by rw [hr, div_pow, one_pow]
      refine (Finset.sum_le_sum hterm).trans ?_
      have hgeom : ∑ k ∈ Finset.Ico 2 (K + 1), r ^ k =
          r ^ 2 * ∑ j ∈ Finset.range (K - 1), r ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum,
          show K + 1 - 2 = K - 1 by omega]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [pow_add]
      rw [hgeom]
      have hpartial : ∑ j ∈ Finset.range (K - 1), r ^ j ≤ 1 / (1 - r) := by
        rw [geom_sum_eq (ne_of_lt hr1)]
        rw [show (r ^ (K - 1) - 1) / (r - 1) = (1 - r ^ (K - 1)) / (1 - r) by
          rw [← neg_sub (r ^ (K - 1)) 1, ← neg_sub r 1, neg_div_neg_eq]]
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        have : 0 ≤ r ^ (K - 1) := by positivity
        nlinarith
      have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
      calc r ^ 2 * ∑ j ∈ Finset.range (K - 1), r ^ j ≤ r ^ 2 * (1 / (1 - r)) := by
            exact mul_le_mul_of_nonneg_left hpartial hr2
        _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
            rw [hr]
            rw [div_pow, one_pow]
            have h1 : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
              field_simp
            rw [h1]
            field_simp
    rw [hsplit, hf.map_one]
    linarith

/-- **The crude Euler bound in exponential form.**  For `f` multiplicative, nonnegative, with
`f n ≤ 1/n`, the truncated sum is at most `exp(1 + ∑_{p ≤ Y} f p)`.

With `f m = h m / m` for `h` nonnegative multiplicative and `1`-bounded, this is the elementary
mean-value bound `∑_{m ≤ Y} h(m)/m ≪ exp(∑_{p ≤ Y} h(p)/p)` used in Case A of
`NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM`. -/
theorem sum_Icc_le_exp_prime_sum {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hnn : ∀ n : ℕ, 0 ≤ f n) (hbd : ∀ n : ℕ, 0 < n → f n ≤ 1 / (n : ℝ)) (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, f m ≤
      Real.exp (1 + ∑ p ∈ Nat.primesBelow (Y + 1), f p) := by
  classical
  refine (sum_Icc_le_euler_product hf hnn Y).trans ?_
  have hloc : ∀ p ∈ Nat.primesBelow (Y + 1),
      ∑ k ∈ Finset.range (Nat.log 2 Y + 1), f (p ^ k) ≤
        Real.exp (f p + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    refine (local_factor_le hf hnn hbd hpp _).trans ?_
    have := Real.add_one_le_exp (f p + 1 / ((p : ℝ) * ((p : ℝ) - 1)))
    linarith
  have hnn' : ∀ p ∈ Nat.primesBelow (Y + 1),
      (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 Y + 1), f (p ^ k) :=
    fun p _ ↦ Finset.sum_nonneg fun k _ ↦ hnn _
  calc ∏ p ∈ Nat.primesBelow (Y + 1), ∑ k ∈ Finset.range (Nat.log 2 Y + 1), f (p ^ k)
      ≤ ∏ p ∈ Nat.primesBelow (Y + 1),
          Real.exp (f p + 1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.prod_le_prod hnn' hloc
    _ = Real.exp (∑ p ∈ Nat.primesBelow (Y + 1),
          (f p + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 + ∑ p ∈ Nat.primesBelow (Y + 1), f p) := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_add_distrib]
        linarith [sum_primesBelow_inv_mul_pred_le_one Y]


/-! ## Mertens: the exponential bound becomes `≪ log Y · exp(-Σ_Y)` -/

/-- The defect `Σ_Y = ∑_{p ≤ Y} (1/p - f p)`, nonnegative when `f p ≤ 1/p`. -/
noncomputable def primeDefect (f : ArithmeticFunction ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y, ((p : ℝ)⁻¹ - f p)

/-- **The crude mean-value bound in the form Case A consumes.**  For `f` multiplicative,
nonnegative, with `f n ≤ 1/n`,
`∑_{m ≤ Y} f m ≤ exp(1 + B) · log Y · exp(-Σ_Y)`,
with `B = Erdos67b.PrimeEstimates.mertensBound` the absolute Mertens constant and
`Σ_Y = ∑_{p ≤ Y}(1/p - f p)`.

So a large defect — Case A's hypothesis — makes the logarithmic mean of `f` small compared with
`log Y`, which is what the thick-window regime of
`NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM` needs. -/
theorem sum_Icc_le_log_mul_exp_neg_defect {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hnn : ∀ n : ℕ, 0 ≤ f n) (hbd : ∀ n : ℕ, 0 < n → f n ≤ 1 / (n : ℝ)) {Y : ℕ} (hY : 2 ≤ Y) :
    ∑ m ∈ Finset.Icc 1 Y, f m ≤
      Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * Real.log (Y : ℝ) *
        Real.exp (-primeDefect f Y) := by
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  -- Mertens' second theorem, upper direction
  have hmert := Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hY
  have hmert' : Erdos67b.PrimeEstimates.primeReciprocals Y ≤
      Real.log (Real.log (Y : ℝ)) + Erdos67b.PrimeEstimates.mertensBound := by
    have := abs_le.mp hmert
    linarith [this.2]
  -- the prime sum of `f` is the reciprocal sum minus the defect
  have hsplit : ∑ p ∈ Nat.primesLE Y, f p =
      Erdos67b.PrimeEstimates.primeReciprocals Y - primeDefect f Y := by
    rw [primeDefect, Erdos67b.PrimeEstimates.primeReciprocals,
      Erdos784.Analytic.primeReciprocals, Finset.sum_sub_distrib]
    ring
  have hkey : 1 + ∑ p ∈ Nat.primesLE Y, f p ≤
      (1 + Erdos67b.PrimeEstimates.mertensBound) + Real.log (Real.log (Y : ℝ)) +
        (-primeDefect f Y) := by
    rw [hsplit]; linarith
  calc ∑ m ∈ Finset.Icc 1 Y, f m
      ≤ Real.exp (1 + ∑ p ∈ Nat.primesBelow (Y + 1), f p) :=
        sum_Icc_le_exp_prime_sum hf hnn hbd Y
    _ = Real.exp (1 + ∑ p ∈ Nat.primesLE Y, f p) := by rw [Nat.primesLE]
    _ ≤ Real.exp ((1 + Erdos67b.PrimeEstimates.mertensBound) +
          Real.log (Real.log (Y : ℝ)) + (-primeDefect f Y)) := Real.exp_le_exp.mpr hkey
    _ = Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * Real.log (Y : ℝ) *
          Real.exp (-primeDefect f Y) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hlogY]


end NormalNumbers.ElliottEulerBound

#print axioms NormalNumbers.ElliottEulerBound.sum_Icc_le_euler_product
#print axioms NormalNumbers.ElliottEulerBound.sum_Icc_le_exp_prime_sum
#print axioms NormalNumbers.ElliottEulerBound.sum_Icc_le_log_mul_exp_neg_defect
