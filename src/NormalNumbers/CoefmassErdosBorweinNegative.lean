/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import ErdosProblems.Erdos67.PrimeEstimates

/-!
# Random Erdős–Borwein subseries: the negative side (above exponent `ln 2`)

Statements copied VERBATIM from the private KB packet `NNErdosBorweinRandom.lean` at 7eb1c8f3
(namespace relocated).  Paper-accepted by codex2 at 95% (mail 20261012T051355Z).  Paper argument:
`nn-erdos-borwein-random-2026-10-12.md`, section "Marginal-only proof".  LOCAL-ONLY branch.

Recommended order: `largeDivisorMass_moment_small` → `typicalDivisorMass_small` (Markov) →
`ebRandom_ae_not_normal_of_marginal_bound` → `ebRandom_ae_not_normal` (marginals of a
`BernoulliLawNat` satisfy the marginal bound; `C ≥ 0` from `m = 2`).
-/

namespace NormalNumbers.ErdosBorweinRandom

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Independent Bernoulli selections of positive integers (index `0` unused). -/
def BernoulliLawNat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) : Prop :=
  (∀ m, 0 ≤ delta m ∧ delta m ≤ 1) ∧
  (∀ m, Measurable (X m)) ∧ iIndepFun X μ ∧
    ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)

/-- The random Erdős–Borwein subseries `Σ_{m ≥ 1, X_m} 1/(b^m - 1)`. -/
noncomputable def ebLambert {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool) (w : Ω) : ℝ :=
  ∑' m : ℕ, (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)

/-- Weighted large-divisor mass `Σ_{d ∣ n, d > M} (log d)^{-a}`. -/
noncomputable def largeDivisorMass (a : ℝ) (M n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => M < d), Real.rpow (Real.log d) (-a)

/-- The exponent choice behind the fractional-moment argument: immediately to the right of zero,
the secant slope of `s ↦ 2^s` is smaller than any `a > log 2`. -/
lemma exists_erdosBorwein_moment_exponent (a : ℝ) (ha : Real.log 2 < a) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ (2 : ℝ) ^ s - 1 < a * s := by
  have hderiv : HasDerivAt (fun s : ℝ => (2 : ℝ) ^ s) (Real.log 2) 0 := by
    convert (hasDerivAt_id (x := (0 : ℝ))).const_rpow (by norm_num : (0 : ℝ) < 2) using 1 <;>
      norm_num
  have htend : Tendsto (fun s : ℝ => s⁻¹ * ((2 : ℝ) ^ s - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Real.log 2)) := by
    convert hderiv.tendsto_slope_zero_right using 1 <;> simp [smul_eq_mul]
  obtain ⟨δ, hδ, hclose⟩ := (Metric.tendsto_nhdsWithin_nhds.mp htend)
    (a - Real.log 2) (sub_pos.mpr ha)
  let s : ℝ := min (δ / 2) (1 / 2)
  have hsδ : s ≤ δ / 2 := min_le_left _ _
  have hsone : s ≤ 1 / 2 := min_le_right _ _
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hdist : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    linarith
  have hclose' := hclose (show s ∈ Set.Ioi (0 : ℝ) from hs) hdist
  rw [Real.dist_eq] at hclose'
  have hquot : s⁻¹ * ((2 : ℝ) ^ s - 1) < a := by
    have := lt_of_le_of_lt
      (le_abs_self (s⁻¹ * ((2 : ℝ) ^ s - 1) - Real.log 2)) hclose'
    linarith
  have hdiv : ((2 : ℝ) ^ s - 1) / s < a := by
    simpa [div_eq_mul_inv, mul_comm] using hquot
  refine ⟨s, hs, ?_, ?_⟩
  · linarith
  · exact (div_lt_iff₀ hs).mp hdiv

/-- The upper Mertens estimate needed by the Euler-product part of the moment argument. -/
lemma primeReciprocalMass_le_log_log_add (X : ℕ) (hX : 2 ≤ X) :
    (∑ p ∈ X.primesLE, 1 / (p : ℝ)) ≤
      Real.log (Real.log (X : ℝ)) + Erdos67.PrimeEstimates.mertensBound := by
  have h := Erdos67.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hX
  rw [abs_le] at h
  simpa [Erdos67.PrimeEstimates.primeReciprocals,
    Erdos784.Analytic.primeReciprocals, one_div, add_comm] using h.2

/-! ### The smooth-divisor Euler majorant -/

/-- Concavity gives the sharp secant-line majorant
`(r+1)^s ≤ 1 + (2^s-1)r`.  Keeping the coefficient `2^s-1`, rather than replacing it by
`s`, is what leaves a positive exponent gap when `a > log 2`. -/
lemma rpow_nat_succ_le_secant (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) ^ s ≤ 1 + ((2 : ℝ) ^ s - 1) * r := by
  rcases eq_or_lt_of_le hs1 with rfl | hs1
  · norm_num [add_comm]
  rcases r with _ | r
  · simp
  rcases r with _ | r
  · norm_num
  have hconc := Real.strictConcaveOn_rpow hs hs1
  have hsec := hconc.secant_strict_mono
    (a := (1 : ℝ)) (x := 2) (y := ((r + 3 : ℕ) : ℝ))
    (by norm_num) (by norm_num)
    (by simp only [Set.mem_Ici]; positivity)
    (by norm_num)
    (by exact_mod_cast (show r + 3 ≠ 1 by omega))
    (by exact_mod_cast (show 2 < r + 3 by omega))
  norm_num only [Real.one_rpow] at hsec
  push_cast at hsec ⊢
  have hr : (0 : ℝ) < r + 2 := by positivity
  have hden : ((r : ℝ) + 3 - 1) = r + 2 := by ring
  rw [hden, div_lt_iff₀ hr] at hsec
  norm_num at hsec
  have h := (sub_lt_iff_lt_add.mp hsec).le
  have hr3 : (r : ℝ) + 1 + 1 + 1 = r + 3 := by ring
  have hr2 : (r : ℝ) + 1 + 1 = r + 2 := by ring
  rw [hr3, hr2]
  linarith

/-- Number of divisors contributed by prime powers at primes at most `y`. -/
def smoothDivisorCount (y n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≤ y), (n.factorization p + 1)

/-- The fractional moment of the smooth divisor count is bounded by a product whose local
coefficient is exactly `2^s-1`. -/
lemma smoothDivisorCount_rpow_le_factorizationMajorant
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (y n : ℕ) :
    ((smoothDivisorCount y n : ℕ) : ℝ) ^ s ≤
      ∏ p ∈ n.primeFactors.filter (fun p => p ≤ y),
        (1 + ((2 : ℝ) ^ s - 1) * n.factorization p) := by
  rw [smoothDivisorCount, Nat.cast_prod]
  let S := n.primeFactors.filter (fun p => p ≤ y)
  change (∏ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ)) ^ s ≤ _
  rw [← Real.finsetProd_rpow S (fun p => ((n.factorization p + 1 : ℕ) : ℝ))
    (fun p hp => by positivity) s]
  gcongr with p hp
  exact rpow_nat_succ_le_secant s hs hs1 (n.factorization p)

lemma momentPrimeCoefficient_nonneg (s : ℝ) (hs : 0 < s) :
    0 ≤ (2 : ℝ) ^ s - 1 := by
  linarith [Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hs.le]

lemma momentPrimeCoefficient_le_one (s : ℝ) (hs1 : s ≤ 1) :
    (2 : ℝ) ^ s - 1 ≤ 1 := by
  have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1
  norm_num at this ⊢
  linarith

/-- The geometric sum of valuation indicators has the required first-order prime term and a
summable prime-power error. -/
lemma momentPrimeFactor_le (s : ℝ) (hs1 : s ≤ 1) (p : ℕ) (hp : 2 ≤ p) :
    1 + ((2 : ℝ) ^ s - 1) / (p - 1) ≤
      1 + ((2 : ℝ) ^ s - 1) / p + 1 / ((p : ℝ) * (p - 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hq := momentPrimeCoefficient_le_one s hs1
  have hid : ((2 : ℝ) ^ s - 1) / (p - 1) =
      ((2 : ℝ) ^ s - 1) / p + ((2 : ℝ) ^ s - 1) / (p * (p - 1)) := by
    field_simp [hp0.ne', hp1.ne']
    ring
  have hden : 0 < (p : ℝ) * (p - 1) := mul_pos hp0 hp1
  have hfrac : ((2 : ℝ) ^ s - 1) / (p * (p - 1)) ≤ 1 / (p * (p - 1)) :=
    (div_le_div_iff_of_pos_right hden).2 hq
  rw [hid]
  linarith

/-- A finite Euler product is controlled by the exponential of its linearized prime sum. -/
lemma momentEulerProduct_le_exp (s : ℝ) (hs : 0 < s) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    ∏ p ∈ P, (1 + ((2 : ℝ) ^ s - 1) / p + 1 / ((p : ℝ) * (p - 1))) ≤
      Real.exp (((2 : ℝ) ^ s - 1) * ∑ p ∈ P, 1 / (p : ℝ) +
        ∑ p ∈ P, 1 / ((p : ℝ) * (p - 1))) := by
  let x : ℕ → ℝ := fun p => ((2 : ℝ) ^ s - 1) / p + 1 / ((p : ℝ) * (p - 1))
  have hx : ∀ p ∈ P, 0 ≤ x p := by
    intro p hp
    have hpN := hP p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hp1 : (0 : ℝ) < p - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
      linarith
    dsimp [x]
    exact add_nonneg (div_nonneg (momentPrimeCoefficient_nonneg s hs) hp0.le)
      (div_nonneg zero_le_one (mul_nonneg hp0.le hp1.le))
  calc
    ∏ p ∈ P, (1 + ((2 : ℝ) ^ s - 1) / p + 1 / ((p : ℝ) * (p - 1))) =
        ∏ p ∈ P, (1 + x p) := by simp [x, add_assoc]
    _ ≤ ∏ p ∈ P, Real.exp (x p) := by
      apply Finset.prod_le_prod
      · intro p hp
        linarith [hx p hp]
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp (x p)
    _ = Real.exp (∑ p ∈ P, x p) := by rw [Real.exp_sum]
    _ = _ := by
      congr 1
      simp only [x, Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [mul_one_div]

/-- The prime-power error telescopes even before restricting to primes. -/
lemma reciprocalPrimePowerError_sum_Icc (X : ℕ) (hX : 2 ≤ X) :
    ∑ p ∈ Finset.Icc 2 X, 1 / ((p : ℝ) * (p - 1)) = 1 - 1 / (X : ℝ) := by
  induction X, hX using Nat.le_induction with
  | base => norm_num
  | succ X hX ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hX0 : (X : ℝ) ≠ 0 := by positivity
      have hXs0 : ((X : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp [hX0, hXs0]
      ring

lemma reciprocalPrimePowerError_sum_le_one
    (X : ℕ) (P : Finset ℕ) (hP : P ⊆ Finset.Icc 2 X) :
    ∑ p ∈ P, 1 / ((p : ℝ) * (p - 1)) ≤ 1 := by
  calc
    ∑ p ∈ P, 1 / ((p : ℝ) * (p - 1)) ≤
        ∑ p ∈ Finset.Icc 2 X, 1 / ((p : ℝ) * (p - 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hP
      intro p hpP hp
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hpP).1
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
      have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
      exact div_nonneg zero_le_one (mul_nonneg hp0 hp1)
    _ ≤ 1 := by
      by_cases hX : 2 ≤ X
      · rw [reciprocalPrimePowerError_sum_Icc X hX]
        have : 0 ≤ 1 / (X : ℝ) := by positivity
        linarith
      · have : Finset.Icc 2 X = ∅ := Finset.Icc_eq_empty (by omega)
        simp [this]

/-- The complete finite Euler-product bound used in the smooth-divisor moment estimate. -/
lemma momentEulerProduct_le_mertens
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (X : ℕ) (hX : 2 ≤ X) :
    ∏ p ∈ X.primesLE, (1 + ((2 : ℝ) ^ s - 1) / (p - 1)) ≤
      Real.exp (((2 : ℝ) ^ s - 1) *
        (Real.log (Real.log (X : ℝ)) + Erdos67.PrimeEstimates.mertensBound) + 1) := by
  let q : ℝ := (2 : ℝ) ^ s - 1
  have hq : 0 ≤ q := momentPrimeCoefficient_nonneg s hs
  have hp2 : ∀ p ∈ X.primesLE, 2 ≤ p := fun p hp => Nat.two_le_of_mem_primesLE hp
  have hsub : X.primesLE ⊆ Finset.Icc 2 X := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Nat.two_le_of_mem_primesLE hp, Nat.le_of_mem_primesLE hp⟩
  have hprime := primeReciprocalMass_le_log_log_add X hX
  have herr := reciprocalPrimePowerError_sum_le_one X X.primesLE hsub
  calc
    ∏ p ∈ X.primesLE, (1 + ((2 : ℝ) ^ s - 1) / (p - 1)) ≤
        ∏ p ∈ X.primesLE,
          (1 + ((2 : ℝ) ^ s - 1) / p + 1 / ((p : ℝ) * (p - 1))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (0 : ℝ) < p - 1 := by
          have : (1 : ℝ) < p := by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp)
          linarith
        exact add_nonneg zero_le_one (div_nonneg hq hp1.le)
      · intro p hp
        exact momentPrimeFactor_le s hs1 p (hp2 p hp)
    _ ≤ Real.exp (q * ∑ p ∈ X.primesLE, 1 / (p : ℝ) +
        ∑ p ∈ X.primesLE, 1 / ((p : ℝ) * (p - 1))) := by
      exact momentEulerProduct_le_exp s hs X.primesLE hp2
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hprime hq
      dsimp [q] at hmul ⊢
      linarith

/-- Mertens' bound in the power form used by the dyadic block argument.  The leading exponent is
exactly `2^s-1`; all prime-power contributions are absorbed into the constant. -/
lemma momentEulerProduct_le_log_rpow
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (X : ℕ) (hX : 2 ≤ X) :
    ∏ p ∈ X.primesLE, (1 + ((2 : ℝ) ^ s - 1) / (p - 1)) ≤
      Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
        (Real.log (X : ℝ)) ^ ((2 : ℝ) ^ s - 1) := by
  refine (momentEulerProduct_le_mertens s hs hs1 X hX).trans_eq ?_
  have hXr : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hXr
  rw [Real.rpow_def_of_pos hlog]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Uniform vanishing fractional moment of the large-divisor mass.  Choose `0 < s ≤ 1` with
`q = 2^s - 1 < a s`.  `τ(n_y)^s = 1 * g_y` with `g_y ≥ 0`, so for EVERY `T`,
`(1/T) Σ_{n ≤ T} τ(n_y)^s ≤ ∏_{p ≤ y}(1 + q/p + 1/(p(p-1))) ≤ A_s (log y)^q`; prime powers are
retained.  Subadditivity of `t^s` over log-dyadic blocks gives
`(1/T) Σ μ_M^s ≤ A_s 2^q Σ_{ℓ ≥ L} 2^{-(as-q)ℓ} → 0`.  Implies `typicalDivisorMass_small` by Markov.
Paper confidence 95% (codex2); unproved in Lean. -/
theorem largeDivisorMass_moment_small (a : ℝ) (ha : Real.log 2 < a) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
        (∑ n ∈ Finset.Icc 1 N, Real.rpow (largeDivisorMass a M n) s) ≤ ε * N := by
  obtain ⟨s, hs, hs1, hgap⟩ := exists_erdosBorwein_moment_exponent a ha
  refine ⟨s, hs, hs1, ?_⟩
  intro ε hε
  sorry

/-- **Typical divisor mass is small above `ln 2`.**  Dyadic blocks in `log d`.  The divisors
`d ≤ y` of `n` divide the `y`-smooth part `n_y`, so their number is at most `τ(n_y)`.  Use
`(1/N) Σ_{n ≤ N} τ(n_y)^s ≤ ∏_{p ≤ y}(1 + (2^s-1)/p + O(p^{-2})) ≤ C (log y)^{2^s-1}`, which needs
only an upper Mertens bound.  Markov at level `ε·2^{j(a-η)}` on block `j`, with `log y_j = 2^{j+1}`,
gives a geometric series exactly when `a - η > (2^s-1)/s`, and `(2^s-1)/s → ln 2` as `s → 0⁺`. -/
theorem typicalDivisorMass_small (a : ℝ) (ha : Real.log 2 < a) (ε η : ℝ) (hε : 0 < ε)
    (hη : 0 < η) :
    ∃ M : ℕ, ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (fun n => ε < largeDivisorMass a M n)).card : ℝ) ≤ η * N := by
  obtain ⟨s, hs, -, hmoment⟩ := largeDivisorMass_moment_small a ha
  have hεs : 0 < Real.rpow ε s := Real.rpow_pos_of_pos hε s
  obtain ⟨M, hM, hbound⟩ := hmoment (η * Real.rpow ε s) (mul_pos hη hεs)
  refine ⟨M, fun N hN => ?_⟩
  let S := (Finset.Icc 1 N).filter (fun n => ε < largeDivisorMass a M n)
  have hmass_nonneg : ∀ n, 0 ≤ largeDivisorMass a M n := by
    intro n
    unfold largeDivisorMass
    apply Finset.sum_nonneg
    intro d hd
    have hdM : M < d := (Finset.mem_filter.mp hd).2
    have hd1 : 1 ≤ d := by omega
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hd1)) _
  have hlower : (S.card : ℝ) * Real.rpow ε s ≤
      ∑ n ∈ Finset.Icc 1 N, Real.rpow (largeDivisorMass a M n) s := by
    calc
      (S.card : ℝ) * Real.rpow ε s = ∑ _n ∈ S, Real.rpow ε s := by
        simp [mul_comm]
      _ ≤ ∑ n ∈ S, Real.rpow (largeDivisorMass a M n) s := by
        apply Finset.sum_le_sum
        intro n hn
        exact (Real.rpow_lt_rpow hε.le (Finset.mem_filter.mp hn).2 hs).le
      _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.rpow (largeDivisorMass a M n) s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n _ _
        exact Real.rpow_nonneg (hmass_nonneg n) _
  have hupper := hbound N hN
  have hmul : (S.card : ℝ) * Real.rpow ε s ≤ (η * N) * Real.rpow ε s := by
    calc
      (S.card : ℝ) * Real.rpow ε s ≤
          ∑ n ∈ Finset.Icc 1 N, Real.rpow (largeDivisorMass a M n) s := hlower
      _ ≤ (η * Real.rpow ε s) * N := hupper
      _ = (η * N) * Real.rpow ε s := by ring
  change (S.card : ℝ) ≤ η * N
  exact (mul_le_mul_iff_of_pos_right hεs).mp hmul

/-- **Marginal decay alone forces non-normality** (strengthens `ebRandom_ae_not_normal`).
Proof outline:
1. Use the exact residual `R_M(n) = Σ_{j ≥ 1} b^{-j} D_M(n+j)`, with
   `D_M(t) = #{m > M selected : m ∣ t}`.  `b^n Y_M - R_M(n) ∈ ℤ`, so `frac ≤ R_M`.
2. By subadditivity and Jensen, `E[frac^s] ≤ C^s Σ_j b^{-js} μ_M(n+j)^s`.
3. Shifting by `j` costs at most `1+j`, which is summable against `b^{-js}`.
4. On the normality event the orbit average of `frac^s` tends to `1/(s+1)`.  Fatou then bounds
   `P(normal)` by a quantity that vanishes as `M → ∞`.
Paper confidence 95% (codex2); unproved in Lean. -/
@[blueprint (title := "Marginal decay alone forces random Erdős–Borwein non-normality")]
theorem ebRandom_ae_not_normal_of_marginal_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hMeas : ∀ m, Measurable (X m))
    (a C : ℝ) (ha : Real.log 2 < a) (hC : 0 ≤ C)
    (hMarginal : ∀ m : ℕ, 2 ≤ m →
      μ {w | X m w = true} ≤ ENNReal.ofReal (C * Real.rpow (Real.log m) (-a))) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

/-- **Non-normality beyond finite mass.**  Paper proof:
1. Remove the rational head `m ≤ M`.
2. `frac(b^n Y_M) ≤ 2 Σ_{j ≥ 1} b^{-j} d_{S,M}(n+j)`, since `α_m(n) = b^{m-j}/(b^m-1)` with
   `m ∣ n+j`.
3. `E_X 1[d_{S,M}(n) ≥ 1] ≤ C · largeDivisorMass a M n`; the `j > J` tail is handled by the typical
   bound plus Markov in `X`.
4. So `E_X` of the density of `{n ≤ N : frac ≥ ε'}` is small, uniformly in `N`.
5. Fatou gives non-normality with positive probability.  Normality is a tail event (finite changes
   are rational shifts, Wall), so Kolmogorov's 0-1 law makes it almost sure. -/
@[blueprint (title := "Random Erdős–Borwein subseries are non-normal above exponent ln 2")]
theorem ebRandom_ae_not_normal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (a C : ℝ) (ha : Real.log 2 < a)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * Real.rpow (Real.log m) (-a)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  obtain ⟨hdelta_range, hMeas, -, hLaw⟩ := hX
  have hweight : 0 < Real.rpow (Real.log 2) (-a) :=
    Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  have hprod : 0 ≤ C * Real.rpow (Real.log 2) (-a) :=
    (hdelta_range 2).1.trans (hdelta 2 (by omega))
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left hprod hweight
  apply ebRandom_ae_not_normal_of_marginal_bound μ X hMeas a C ha hC
  intro m hm
  rw [hLaw m]
  exact ENNReal.ofReal_le_ofReal (hdelta m hm)

end NormalNumbers.ErdosBorweinRandom
