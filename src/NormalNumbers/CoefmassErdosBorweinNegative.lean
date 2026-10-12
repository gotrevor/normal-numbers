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

/-! ### Exact averaging of the factorization majorant -/

/-- The squarefree coefficient whose divisor sum is the factorization majorant, restricted to
the finite set of relevant primes. -/
noncomputable def smoothMomentCoeff (q : ℝ) (P : Finset ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∈ P then q else 0)

lemma smoothMomentCoeff_mult (q : ℝ) (P : Finset ℕ) :
    (smoothMomentCoeff q P).IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

lemma smoothMomentCoeff_prime_pow (q : ℝ) (P : Finset ℕ) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) : smoothMomentCoeff q P (p ^ k) = if p ∈ P then q else 0 := by
  simp [smoothMomentCoeff, ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_pow, hp.primeFactors, hk]

noncomputable def smoothMomentSum (q : ℝ) (P : Finset ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * smoothMomentCoeff q P

lemma smoothMomentSum_apply (q : ℝ) (P : Finset ℕ) (n : ℕ) :
    smoothMomentSum q P n = ∑ d ∈ n.divisors, smoothMomentCoeff q P d := by
  exact ArithmeticFunction.coe_zeta_mul_apply

lemma smoothMomentSum_mult (q : ℝ) (P : Finset ℕ) :
    (smoothMomentSum q P).IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul (smoothMomentCoeff_mult q P)

lemma smoothMomentSum_prime_pow (q : ℝ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    smoothMomentSum q P (p ^ k) = 1 + (if p ∈ P then q else 0) * k := by
  induction k with
  | zero => simp [smoothMomentSum, smoothMomentCoeff]
  | succ k ih =>
      rw [smoothMomentSum_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
      rw [← Nat.sum_divisors_prime_pow hp, ← smoothMomentSum_apply, ih]
      rw [smoothMomentCoeff_prime_pow q P hp (Nat.succ_ne_zero k)]
      push_cast
      ring

lemma smoothMomentSum_eq_product (q : ℝ) (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothMomentSum q P n =
      ∏ p ∈ n.primeFactors.filter (fun p => p ∈ P),
        (1 + q * n.factorization p) := by
  rw [Nat.multiplicative_factorization (smoothMomentSum q P)
    (fun _ _ h => (smoothMomentSum_mult q P).map_mul_of_coprime h)
    (smoothMomentSum_mult q P).map_one hn]
  rw [Finsupp.prod]
  rw [Finset.prod_congr (Nat.support_factorization n)
    (fun p hp => smoothMomentSum_prime_pow q P (Nat.prime_of_mem_primeFactors hp)
      (n.factorization p))]
  simp only [ite_mul, zero_mul]
  simp_rw [add_ite, add_zero]
  rw [Finset.prod_ite]
  simp

noncomputable def smoothMomentWeight (q : ℝ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  smoothMomentCoeff q P n / n

lemma smoothMomentWeight_one (q : ℝ) (P : Finset ℕ) : smoothMomentWeight q P 1 = 1 := by
  simp [smoothMomentWeight, smoothMomentCoeff]

lemma smoothMomentWeight_mult (q : ℝ) (P : Finset ℕ) {m n : ℕ} (h : m.Coprime n) :
    smoothMomentWeight q P (m * n) =
      smoothMomentWeight q P m * smoothMomentWeight q P n := by
  simp only [smoothMomentWeight, (smoothMomentCoeff_mult q P).map_mul_of_coprime h,
    Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma smoothMomentWeight_prime_pow (q : ℝ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    smoothMomentWeight q P (p ^ k) =
      if k = 0 then 1 else (if p ∈ P then q else 0) / (p : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp [smoothMomentWeight_one]
  · rw [if_neg hk]
    simp only [smoothMomentWeight, Nat.cast_pow, smoothMomentCoeff_prime_pow q P hp hk]

lemma smoothMomentCoeff_nonneg (q : ℝ) (hq : 0 ≤ q) (P : Finset ℕ) (n : ℕ) :
    0 ≤ smoothMomentCoeff q P n := by
  by_cases hn : n = 0
  · simp [hn, smoothMomentCoeff]
  · rw [smoothMomentCoeff, ArithmeticFunction.prodPrimeFactors_apply hn]
    apply Finset.prod_nonneg
    intro p hp
    split_ifs
    · exact hq
    · exact le_rfl

lemma smoothMomentWeight_nonneg (q : ℝ) (hq : 0 ≤ q) (P : Finset ℕ) (n : ℕ) :
    0 ≤ smoothMomentWeight q P n := by
  exact div_nonneg (smoothMomentCoeff_nonneg q hq P n) (by positivity)

lemma smoothMomentWeight_local_hasSum (q : ℝ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hpP : p ∈ P) : HasSum (fun k : ℕ => smoothMomentWeight q P (p ^ k))
      (1 + q / (p - 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hratio0 : 0 ≤ (1 : ℝ) / p := by positivity
  have hratio1 : (1 : ℝ) / p < 1 := by
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hp1
  have hgeom0 := (hasSum_geometric_of_lt_one hratio0 hratio1).mul_left (q / (p : ℝ))
  have hgeom : HasSum (fun k : ℕ => q / (p : ℝ) ^ (k + 1)) (q / (p - 1)) := by
    have hpne : (p : ℝ) ≠ 0 := hp0.ne'
    have hp1ne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hfun : (fun k : ℕ => q / (p : ℝ) ^ (k + 1)) =
        (fun k : ℕ => q / (p : ℝ) * ((1 : ℝ) / p) ^ k) := by
      funext k
      rw [pow_succ, div_mul_eq_div_div]
      simp only [div_eq_mul_inv, one_mul, inv_pow]
      ring
    have hval : q / ((p : ℝ) - 1) = q / (p : ℝ) * (1 - 1 / (p : ℝ))⁻¹ := by
      field_simp [hpne, hp1ne]
    rw [hfun, hval]
    exact hgeom0
  apply (hasSum_nat_add_iff' 1).mp
  simpa [smoothMomentWeight_prime_pow q P hp, hpP] using hgeom

lemma smoothMomentWeight_local_summable (q : ℝ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖smoothMomentWeight q P (p ^ k)‖) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  let c : ℝ := |if p ∈ P then q else 0| / p
  have hgeom : Summable (fun k : ℕ => c * ((1 : ℝ) / p) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) (by
      simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hp1)).mul_left c
  have htail : Summable (fun k : ℕ => ‖smoothMomentWeight q P (p ^ (k + 1))‖) := by
    apply hgeom.congr
    intro k
    rw [smoothMomentWeight_prime_pow q P hp (k + 1)]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Real.norm_eq_abs,
      abs_div, abs_pow, abs_of_pos hp0]
    dsimp [c]
    rw [pow_succ, div_mul_eq_div_div]
    simp only [div_eq_mul_inv, one_mul, inv_pow]
    ring
  exact (summable_nat_add_iff 1).mp htail

lemma smoothMomentWeight_euler_hasSum (q : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun m : Nat.factoredNumbers P => smoothMomentWeight q P m)
      (∏ p ∈ P, (1 + q / (p - 1))) := by
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (smoothMomentWeight_one q P) (smoothMomentWeight_mult q P)
    (fun hp => smoothMomentWeight_local_summable q P hp) P
  have hfilter : P.filter Nat.Prime = P := Finset.filter_eq_self.mpr hP
  rw [hfilter] at h
  have hprod : (∏ p ∈ P, ∑' (n : ℕ), smoothMomentWeight q P (p ^ n)) =
      ∏ p ∈ P, (1 + q / (p - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact (smoothMomentWeight_local_hasSum q P (hP p hp) hp).tsum_eq
  rw [← hprod]
  exact h.2

lemma smoothMomentWeight_eq_zero_of_not_factored (q : ℝ) (P : Finset ℕ) {n : ℕ}
    (hn : n ∉ Nat.factoredNumbers P) : smoothMomentWeight q P n = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0, smoothMomentWeight]
  have hnsub : ¬n.primeFactors ⊆ P := by
    intro hsub
    exact hn (Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr ⟨hn0, hsub⟩)
  obtain ⟨p, hpn, hpP⟩ := Finset.not_subset.mp hnsub
  have hc : smoothMomentCoeff q P n = 0 := by
    rw [smoothMomentCoeff, ArithmeticFunction.prodPrimeFactors_apply hn0]
    apply Finset.prod_eq_zero hpn
    simp [hpP]
  simp [smoothMomentWeight, hc]

lemma smoothMomentWeight_support_subset (q : ℝ) (P : Finset ℕ) :
    Function.support (smoothMomentWeight q P) ⊆ Nat.factoredNumbers P := by
  intro n hn
  by_contra hnot
  exact hn (smoothMomentWeight_eq_zero_of_not_factored q P hnot)

lemma smoothMomentWeight_summable (q : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (smoothMomentWeight q P) := by
  have hsub : Summable (fun m : Nat.factoredNumbers P => smoothMomentWeight q P m) :=
    (smoothMomentWeight_euler_hasSum q P hP).summable
  have hind : Summable ((Nat.factoredNumbers P).indicator (smoothMomentWeight q P)) :=
    summable_subtype_iff_indicator.mp hsub
  have heq : (Nat.factoredNumbers P).indicator (smoothMomentWeight q P) =
      smoothMomentWeight q P := by
    funext n
    by_cases hn : n ∈ Nat.factoredNumbers P
    · simp [hn]
    · simp [hn, smoothMomentWeight_eq_zero_of_not_factored q P hn]
  rwa [heq] at hind

lemma smoothMomentWeight_tsum (q : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑' n : ℕ, smoothMomentWeight q P n = ∏ p ∈ P, (1 + q / (p - 1)) := by
  rw [← tsum_subtype_eq_of_support_subset (smoothMomentWeight_support_subset q P)]
  exact (smoothMomentWeight_euler_hasSum q P hP).tsum_eq

lemma divisors_eq_Ioc_filter_dvd_of_mem {n N : ℕ} (hn : n ∈ Finset.Ioc 0 N) :
    n.divisors = (Finset.Ioc 0 N).filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hdn, hn0⟩
    have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hnpos,
      (Nat.le_of_dvd hnpos hdn).trans (Finset.mem_Ioc.mp hn).2⟩, hdn⟩
  · rintro ⟨⟨-, -⟩, hdn⟩
    exact ⟨hdn, (Finset.mem_Ioc.mp hn).1.ne'⟩

lemma smoothMomentSum_sum_eq (q : ℝ) (P : Finset ℕ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, smoothMomentSum q P n =
      ∑ d ∈ Finset.Ioc 0 N, smoothMomentCoeff q P d * (N / d : ℕ) := by
  calc
    ∑ n ∈ Finset.Ioc 0 N, smoothMomentSum q P n =
        ∑ n ∈ Finset.Ioc 0 N,
          ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => d ∣ n), smoothMomentCoeff q P d := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [smoothMomentSum_apply, divisors_eq_Ioc_filter_dvd_of_mem hn]
    _ = ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 N,
          if d ∣ n then smoothMomentCoeff q P d else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑ d ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc 0 N,
          if d ∣ n then smoothMomentCoeff q P d else 0 := Finset.sum_comm
    _ = ∑ d ∈ Finset.Ioc 0 N, smoothMomentCoeff q P d * (N / d : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

/-- Exact uniform averaging bound for the factorization majorant.  Counting multiples supplies
`⌊N/d⌋ ≤ N/d`; the remaining sum is the finite-prime Euler product. -/
lemma factorizationMajorant_sum_le (q : ℝ) (hq : 0 ≤ q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
      ∏ p ∈ n.primeFactors.filter (fun p => p ∈ P),
        (1 + q * n.factorization p)) ≤
      N * ∏ p ∈ P, (1 + q / (p - 1)) := by
  calc
    (∑ n ∈ Finset.Ioc 0 N,
      ∏ p ∈ n.primeFactors.filter (fun p => p ∈ P),
        (1 + q * n.factorization p)) =
        ∑ n ∈ Finset.Ioc 0 N, smoothMomentSum q P n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [smoothMomentSum_eq_product q P (Finset.mem_Ioc.mp hn).1.ne']
    _ = ∑ d ∈ Finset.Ioc 0 N, smoothMomentCoeff q P d * (N / d : ℕ) :=
      smoothMomentSum_sum_eq q P N
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (N : ℝ) * smoothMomentWeight q P d := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        smoothMomentCoeff q P d * (N / d : ℕ) ≤
            smoothMomentCoeff q P d * ((N : ℝ) / d) := by
          exact mul_le_mul_of_nonneg_left
            (Nat.cast_div_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d)
            (smoothMomentCoeff_nonneg q hq P d)
        _ = (N : ℝ) * smoothMomentWeight q P d := by
          unfold smoothMomentWeight
          ring
    _ = (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, smoothMomentWeight q P d := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * ∑' d : ℕ, smoothMomentWeight q P d := by
      apply mul_le_mul_of_nonneg_left
      · exact (smoothMomentWeight_summable q P hP).sum_le_tsum (Finset.Ioc 0 N)
          (fun d hd => smoothMomentWeight_nonneg q hq P d)
      · positivity
    _ = N * ∏ p ∈ P, (1 + q / (p - 1)) := by
      rw [smoothMomentWeight_tsum q P hP]

/-- The smooth-divisor fractional moment has the exact Euler-product average needed by the
dyadic argument, uniformly in the averaging cutoff. -/
lemma smoothDivisorCount_rpow_sum_le_eulerProduct
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (y N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((smoothDivisorCount y n : ℕ) : ℝ) ^ s) ≤
      N * ∏ p ∈ y.primesLE, (1 + ((2 : ℝ) ^ s - 1) / (p - 1)) := by
  have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  calc
    (∑ n ∈ Finset.Ioc 0 N, ((smoothDivisorCount y n : ℕ) : ℝ) ^ s) ≤
        ∑ n ∈ Finset.Ioc 0 N,
          ∏ p ∈ n.primeFactors.filter (fun p => p ≤ y),
            (1 + ((2 : ℝ) ^ s - 1) * n.factorization p) := by
      apply Finset.sum_le_sum
      intro n hn
      exact smoothDivisorCount_rpow_le_factorizationMajorant s hs hs1 y n
    _ = ∑ n ∈ Finset.Ioc 0 N,
          ∏ p ∈ n.primeFactors.filter (fun p => p ∈ y.primesLE),
            (1 + ((2 : ℝ) ^ s - 1) * n.factorization p) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hfilter : n.primeFactors.filter (fun p => p ≤ y) =
          n.primeFactors.filter (fun p => p ∈ y.primesLE) := by
        ext p
        simp only [Finset.mem_filter, Nat.mem_primesLE]
        constructor
        · rintro ⟨hpn, hpy⟩
          exact ⟨hpn, hpy, Nat.prime_of_mem_primeFactors hpn⟩
        · rintro ⟨hpn, hpy, -⟩
          exact ⟨hpn, hpy⟩
      rw [hfilter]
    _ ≤ N * ∏ p ∈ y.primesLE, (1 + ((2 : ℝ) ^ s - 1) / (p - 1)) := by
      exact factorizationMajorant_sum_le ((2 : ℝ) ^ s - 1)
        (momentPrimeCoefficient_nonneg s hs) y.primesLE
        (fun p hp => Nat.prime_of_mem_primesLE hp) N

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

/-- Uniform power-form bound for the averaged smooth-divisor fractional moment. -/
lemma smoothDivisorCount_rpow_sum_le_log_rpow
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (y : ℕ) (hy : 2 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((smoothDivisorCount y n : ℕ) : ℝ) ^ s) ≤
      N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
        (Real.log (y : ℝ)) ^ ((2 : ℝ) ^ s - 1)) := by
  calc
    (∑ n ∈ Finset.Icc 1 N, ((smoothDivisorCount y n : ℕ) : ℝ) ^ s) ≤
        N * ∏ p ∈ y.primesLE, (1 + ((2 : ℝ) ^ s - 1) / (p - 1)) :=
      smoothDivisorCount_rpow_sum_le_eulerProduct s hs hs1 y N
    _ ≤ N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
        (Real.log (y : ℝ)) ^ ((2 : ℝ) ^ s - 1)) := by
      exact mul_le_mul_of_nonneg_left (momentEulerProduct_le_log_rpow s hs hs1 y hy) (by positivity)

/-! ### Divisors supported on the small primes -/

/-- The part of `n` supported on primes at most `y`. -/
def smoothPart (y n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≤ y), p ^ n.factorization p

lemma smoothPart_ne_zero (y n : ℕ) : smoothPart y n ≠ 0 := by
  unfold smoothPart
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

lemma smoothPart_factorization (y n p : ℕ) :
    (smoothPart y n).factorization p =
      if p ∈ n.primeFactors.filter (fun p => p ≤ y) then n.factorization p else 0 := by
  let P := n.primeFactors.filter (fun p => p ≤ y)
  change (∏ q ∈ P, q ^ n.factorization q).factorization p =
    if p ∈ P then n.factorization p else 0
  rw [Nat.factorization_prod_apply]
  · by_cases hp : p ∈ P
    · rw [if_pos hp]
      calc
        (∑ q ∈ P, (q ^ n.factorization q).factorization p) =
            (p ^ n.factorization p).factorization p := by
          apply Finset.sum_eq_single p
          · intro q hq hqp
            rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).factorization_pow]
            simp [hqp]
          · simp [hp]
        _ = n.factorization p := by
          rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).factorization_pow]
          simp
    · rw [if_neg hp]
      apply Finset.sum_eq_zero
      intro q hq
      have hqp : q ≠ p := by
        intro hqp
        subst q
        exact hp hq
      rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).factorization_pow]
      simp [hqp]
  · intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).ne_zero

lemma smoothPart_primeFactors (y n : ℕ) :
    (smoothPart y n).primeFactors = n.primeFactors.filter (fun p => p ≤ y) := by
  let P := n.primeFactors.filter (fun p => p ≤ y)
  have hpart : smoothPart y n ≠ 0 := smoothPart_ne_zero y n
  ext p
  rw [Nat.mem_primeFactors_of_ne_zero hpart]
  constructor
  · rintro ⟨hpprime, hpdiv⟩
    have hfac := (hpprime.dvd_iff_one_le_factorization hpart).mp hpdiv
    rw [smoothPart_factorization] at hfac
    by_cases hpP : p ∈ P
    · exact hpP
    · simp [P, hpP] at hfac
  · intro hpP
    have hpn : p ∈ n.primeFactors := (Finset.mem_filter.mp hpP).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpn
    refine ⟨hpprime, (hpprime.dvd_iff_one_le_factorization hpart).mpr ?_⟩
    rw [smoothPart_factorization, if_pos hpP]
    have hn : n ≠ 0 := (Nat.mem_primeFactors.mp hpn).2.2
    exact (hpprime.dvd_iff_one_le_factorization hn).mp (Nat.dvd_of_mem_primeFactors hpn)

lemma smoothPart_card_divisors (y n : ℕ) :
    (smoothPart y n).divisors.card = smoothDivisorCount y n := by
  rw [Nat.card_divisors (smoothPart_ne_zero y n), smoothPart_primeFactors]
  unfold smoothDivisorCount
  apply Finset.prod_congr rfl
  intro p hp
  rw [smoothPart_factorization, if_pos hp]

/-- Every divisor of `n` that is at most `y` divides the `y`-smooth part of `n`; hence the
number of such divisors is bounded by the product of the available prime-exponent choices. -/
lemma card_divisors_filter_le_smoothDivisorCount (y n : ℕ) :
    (n.divisors.filter (fun d => d ≤ y)).card ≤ smoothDivisorCount y n := by
  rw [← smoothPart_card_divisors y n]
  apply Finset.card_le_card
  intro d hd
  have hdmem := (Finset.mem_filter.mp hd).1
  have hdy := (Finset.mem_filter.mp hd).2
  have hdn : d ∣ n := (Nat.mem_divisors.mp hdmem).1
  have hn : n ≠ 0 := (Nat.mem_divisors.mp hdmem).2
  have hd0 : d ≠ 0 := fun hd0 => by subst d; simp at hdmem
  have hpart : smoothPart y n ≠ 0 := smoothPart_ne_zero y n
  apply Nat.mem_divisors.mpr
  refine ⟨(Nat.factorization_le_iff_dvd hd0 hpart).mp ?_, hpart⟩
  rw [Finsupp.le_def]
  intro p
  by_cases hpprime : p.Prime
  · by_cases hpd : p ∣ d
    · have hp_le_d : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpd
      have hpn : p ∈ n.primeFactors := hpprime.mem_primeFactors (hpd.trans hdn) hn
      have hpP : p ∈ n.primeFactors.filter (fun p => p ≤ y) :=
        Finset.mem_filter.mpr ⟨hpn, hp_le_d.trans hdy⟩
      rw [smoothPart_factorization, if_pos hpP]
      exact (Nat.factorization_le_iff_dvd hd0 hn).mpr hdn p
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime d hpprime]
    exact Nat.zero_le _

/-! ### Logarithmic dyadic blocks -/

/-- Integer cutoffs `2^(2^ℓ)`.  These replace ceilings of `exp (2^ℓ)` and make the eventual
partition of divisors entirely discrete, while changing only the harmless constant `log 2`. -/
def dyadicExpCutoff (ℓ : ℕ) : ℕ := 2 ^ (2 ^ ℓ)

lemma dyadicExpCutoff_two_le (ℓ : ℕ) : 2 ≤ dyadicExpCutoff ℓ := by
  unfold dyadicExpCutoff
  exact Nat.le_pow (Nat.two_pow_pos ℓ)

lemma dyadicExpCutoff_le_succ (ℓ : ℕ) :
    dyadicExpCutoff ℓ ≤ dyadicExpCutoff (ℓ + 1) := by
  unfold dyadicExpCutoff
  apply Nat.pow_le_pow_right
  · omega
  · exact Nat.pow_le_pow_right (by omega) (Nat.le_succ ℓ)

lemma log_dyadicExpCutoff (ℓ : ℕ) :
    Real.log (dyadicExpCutoff ℓ : ℝ) = (2 : ℝ) ^ ℓ * Real.log 2 := by
  unfold dyadicExpCutoff
  push_cast
  rw [Real.log_pow]
  norm_num

/-- Contribution of divisors in one double-exponential block. -/
noncomputable def divisorBlockMass (a : ℝ) (ℓ n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter
    (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1)),
    Real.rpow (Real.log d) (-a)

lemma divisorBlockMass_nonneg (a : ℝ) (ℓ n : ℕ) : 0 ≤ divisorBlockMass a ℓ n := by
  unfold divisorBlockMass
  exact Finset.sum_nonneg fun d hd => Real.rpow_nonneg (Real.log_nonneg (by
    have hcutd := (Finset.mem_filter.mp hd).2.1
    have hd1 : 1 ≤ d := (show 1 ≤ dyadicExpCutoff ℓ by
      exact (by omega : 1 ≤ 2).trans (dyadicExpCutoff_two_le ℓ)).trans hcutd.le
    exact_mod_cast hd1)) _

lemma divisorBlock_card_le (n ℓ : ℕ) :
    (n.divisors.filter
      (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1))).card ≤
      smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n := by
  refine (Finset.card_le_card ?_).trans
    (card_divisors_filter_le_smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n)
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, hd.2.2⟩

/-- Each block is bounded by its left-end weight times the number of divisors supported on
primes below the right endpoint. -/
lemma divisorBlockMass_le (a : ℝ) (ha : 0 < a) (ℓ n : ℕ) :
    divisorBlockMass a ℓ n ≤
      (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) *
        Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a) := by
  let S := n.divisors.filter
    (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1))
  have hcut_pos : (0 : ℝ) < dyadicExpCutoff ℓ := by
    exact_mod_cast (show 0 < dyadicExpCutoff ℓ from
      lt_of_lt_of_le (by omega) (dyadicExpCutoff_two_le ℓ))
  have hlogcut_pos : 0 < Real.log (dyadicExpCutoff ℓ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < dyadicExpCutoff ℓ by
      exact lt_of_lt_of_le (by omega) (dyadicExpCutoff_two_le ℓ)))
  have hterm : ∀ d ∈ S, Real.rpow (Real.log d) (-a) ≤
      Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a) := by
    intro d hd
    have hcutd : (dyadicExpCutoff ℓ : ℝ) ≤ d := by
      exact_mod_cast (Finset.mem_filter.mp hd).2.1.le
    have hdpos : (0 : ℝ) < d := hcut_pos.trans_le hcutd
    have hlogle : Real.log (dyadicExpCutoff ℓ : ℝ) ≤ Real.log d :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hcut_pos)
        (Set.mem_Ioi.mpr hdpos) hcutd
    rw [log_dyadicExpCutoff] at hlogle
    exact Real.rpow_le_rpow_of_nonpos
      (by simpa [log_dyadicExpCutoff] using hlogcut_pos) hlogle (neg_nonpos.mpr ha.le)
  calc
    divisorBlockMass a ℓ n = ∑ d ∈ S, Real.rpow (Real.log d) (-a) := rfl
    _ ≤ ∑ _d ∈ S, Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a) := by
      exact Finset.sum_le_sum fun d hd => hterm d hd
    _ = (S.card : ℝ) * Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a) := by
      simp [mul_comm]
    _ ≤ (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) *
        Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast divisorBlock_card_le n ℓ)
        (Real.rpow_nonneg (by positivity) _)

/-- The already-proved smooth-divisor estimate controls the averaged fractional moment of one
double-exponential block, uniformly in the averaging cutoff `N`. -/
lemma divisorBlockMass_rpow_sum_le
    (a s : ℝ) (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (ℓ N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Real.rpow (divisorBlockMass a ℓ n) s) ≤
      Real.rpow (Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a)) s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  let w := Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a)
  have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hpoint : ∀ n, Real.rpow (divisorBlockMass a ℓ n) s ≤
      Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
        Real.rpow w s := by
    intro n
    calc
      Real.rpow (divisorBlockMass a ℓ n) s ≤
          Real.rpow ((smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * w) s := by
        exact Real.rpow_le_rpow (divisorBlockMass_nonneg a ℓ n)
          (by simpa [w] using divisorBlockMass_le a ha ℓ n) hs.le
      _ = Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
          Real.rpow w s := by
        exact Real.mul_rpow (by positivity) hw
  calc
    (∑ n ∈ Finset.Icc 1 N, Real.rpow (divisorBlockMass a ℓ n) s) ≤
        ∑ n ∈ Finset.Icc 1 N,
          Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
            Real.rpow w s := by
      exact Finset.sum_le_sum fun n _ => hpoint n
    _ = Real.rpow w s *
        ∑ n ∈ Finset.Icc 1 N,
          Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s := by
      simp [Finset.mul_sum, mul_comm]
    _ ≤ Real.rpow w s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
      exact mul_le_mul_of_nonneg_left
        (smoothDivisorCount_rpow_sum_le_log_rpow s hs hs1 (dyadicExpCutoff (ℓ + 1))
          (dyadicExpCutoff_two_le (ℓ + 1)) N)
        (Real.rpow_nonneg hw _)
    _ = _ := by rfl

/-! ### Assembly of the logarithmic blocks -/

/-- Splitting once at the next double-exponential cutoff separates the first block from the
remaining large-divisor mass. -/
lemma largeDivisorMass_cutoff_step (a : ℝ) (ℓ n : ℕ) :
    largeDivisorMass a (dyadicExpCutoff ℓ) n =
      divisorBlockMass a ℓ n + largeDivisorMass a (dyadicExpCutoff (ℓ + 1)) n := by
  rw [largeDivisorMass, divisorBlockMass, largeDivisorMass]
  let S := n.divisors.filter (fun d => dyadicExpCutoff ℓ < d)
  let p := fun d : ℕ => d ≤ dyadicExpCutoff (ℓ + 1)
  calc
    (∑ d ∈ S, Real.rpow (Real.log d) (-a)) =
        (∑ d ∈ S.filter p, Real.rpow (Real.log d) (-a)) +
          ∑ d ∈ S.filter (fun d => ¬p d), Real.rpow (Real.log d) (-a) :=
      (Finset.sum_filter_add_sum_filter_not S p
        (fun d => Real.rpow (Real.log d) (-a))).symm
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr
        · ext d
          simp [S, p, and_assoc]
        · intro d hd
          rfl
      · apply Finset.sum_congr
        · ext d
          simp only [S, p, Finset.mem_filter, Nat.not_le]
          have hcut := dyadicExpCutoff_le_succ ℓ
          constructor
          · rintro ⟨⟨hd, -⟩, hnext⟩
            exact ⟨hd, hnext⟩
          · rintro ⟨hd, hnext⟩
            exact ⟨⟨hd, hcut.trans_lt hnext⟩, hnext⟩
        · intro d hd
          rfl

/-- Iterating the one-step split leaves a finite initial collection of blocks and one tail. -/
lemma largeDivisorMass_cutoff_iterate (a : ℝ) (L K n : ℕ) :
    largeDivisorMass a (dyadicExpCutoff L) n =
      (∑ i ∈ Finset.range K, divisorBlockMass a (L + i) n) +
        largeDivisorMass a (dyadicExpCutoff (L + K)) n := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [ih, Finset.sum_range_succ, largeDivisorMass_cutoff_step]
      simp only [Nat.add_assoc]
      ring

lemma index_le_dyadicExpCutoff_add (L n : ℕ) : n ≤ dyadicExpCutoff (L + n) := by
  have hn_pow : n ≤ 2 ^ n := n.lt_two_pow_self.le
  have hn_exp : n ≤ 2 ^ (L + n) := hn_pow.trans (Nat.pow_le_pow_right (by omega) (Nat.le_add_left n L))
  unfold dyadicExpCutoff
  exact hn_pow.trans (Nat.pow_le_pow_right (by omega) hn_exp)

lemma largeDivisorMass_eq_block_sum (a : ℝ) (L n : ℕ) (hn : 1 ≤ n) :
    largeDivisorMass a (dyadicExpCutoff L) n =
      ∑ i ∈ Finset.range n, divisorBlockMass a (L + i) n := by
  rw [largeDivisorMass_cutoff_iterate a L n n]
  have htail : largeDivisorMass a (dyadicExpCutoff (L + n)) n = 0 := by
    unfold largeDivisorMass
    apply Finset.sum_eq_zero
    intro d hd
    have hdn : d ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
    have hcutd := (Finset.mem_filter.mp hd).2
    have hcutn := index_le_dyadicExpCutoff_add L n
    omega
  rw [htail, add_zero]

/-- Fractional powers are subadditive over finite sums of nonnegative reals. -/
lemma rpow_finset_sum_le_sum_rpow {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (∑ i ∈ S, f i) s ≤ ∑ i ∈ S, Real.rpow (f i) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Real.zero_rpow hs.ne']
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine (Real.rpow_add_le_add_rpow (hf i (Finset.mem_insert_self i S))
        (Finset.sum_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)) hs.le hs1).trans ?_
      exact add_le_add_right (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) _

/-- The analytic expression in the one-block estimate is a fixed constant times a geometric
factor. -/
lemma divisorBlockMomentBound_eq_geometric (a s : ℝ) (ℓ N : ℕ) :
    Real.rpow (Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a)) s *
      (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
        Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) =
      N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
        Real.rpow (Real.log 2) (-a * s + ((2 : ℝ) ^ s - 1)) *
        Real.rpow 2 ((2 : ℝ) ^ s - 1)) *
        (Real.rpow 2 (-(a * s - ((2 : ℝ) ^ s - 1)))) ^ ℓ := by
  simp only [Real.rpow_eq_pow]
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo :
      ((2 : ℝ) ^ ℓ) ^ (-a * s) * ((2 : ℝ) ^ (ℓ + 1)) ^ ((2 : ℝ) ^ s - 1) =
        (2 : ℝ) ^ ((2 : ℝ) ^ s - 1) *
          ((2 : ℝ) ^ (-(a * s - ((2 : ℝ) ^ s - 1))) : ℝ) ^ ℓ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (ℓ : ℝ) * (-a * s) + (ℓ + 1 : ℕ) * ((2 : ℝ) ^ s - 1) =
        ((2 : ℝ) ^ s - 1) + (-(a * s - ((2 : ℝ) ^ s - 1))) * ℓ by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hlog :
      Real.log 2 ^ (-a * s) * Real.log 2 ^ ((2 : ℝ) ^ s - 1) =
        Real.log 2 ^ (-a * s + ((2 : ℝ) ^ s - 1)) := by
    exact (Real.rpow_add hlogpos _ _).symm
  rw [log_dyadicExpCutoff]
  rw [← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ) ^ ℓ * Real.log 2) (-a) s]
  rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) ^ ℓ) hlogpos.le]
  rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (ℓ + 1)) hlogpos.le]
  calc
    _ = N * Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
        (((2 : ℝ) ^ ℓ) ^ (-a * s) * ((2 : ℝ) ^ (ℓ + 1)) ^ ((2 : ℝ) ^ s - 1)) *
        (Real.log 2 ^ (-a * s) * Real.log 2 ^ ((2 : ℝ) ^ s - 1)) := by ring
    _ = _ := by rw [htwo, hlog]; ring

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
  let q : ℝ := (2 : ℝ) ^ s - 1
  let κ : ℝ := a * s - q
  let r : ℝ := Real.rpow 2 (-κ)
  let C : ℝ := Real.exp (q * Erdos67.PrimeEstimates.mertensBound + 1) *
    Real.rpow (Real.log 2) (-a * s + q) * Real.rpow 2 q
  have ha0 : 0 < a := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have hκ : 0 < κ := by simpa [κ, q] using sub_pos.mpr hgap
  have hr0 : 0 ≤ r := by
    simp only [r]
    exact Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hκ)
  have hC : 0 < C := by
    simp only [C]
    exact mul_pos
      (mul_pos (Real.exp_pos _)
        (Real.rpow_pos_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) _))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hone_r : 0 < 1 - r := sub_pos.mpr hr1
  let K : ℝ := C * (1 - r)⁻¹
  have hK : 0 < K := mul_pos hC (inv_pos.mpr hone_r)
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (div_pos hε hK) hr1
  have hchoice : K * r ^ L < ε := by
    exact (lt_div_iff₀' hK).mp (by simpa [mul_comm] using hL)
  refine ⟨dyadicExpCutoff L, dyadicExpCutoff_two_le L, ?_⟩
  intro N hN
  have hblock : ∀ ℓ : ℕ,
      (∑ n ∈ Finset.Icc 1 N, Real.rpow (divisorBlockMass a ℓ n) s) ≤
        N * C * r ^ ℓ := by
    intro ℓ
    calc
      (∑ n ∈ Finset.Icc 1 N, Real.rpow (divisorBlockMass a ℓ n) s) ≤
          Real.rpow (Real.rpow ((2 : ℝ) ^ ℓ * Real.log 2) (-a)) s *
            (N * (Real.exp (((2 : ℝ) ^ s - 1) *
              Erdos67.PrimeEstimates.mertensBound + 1) *
              Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ))
                ((2 : ℝ) ^ s - 1))) :=
        divisorBlockMass_rpow_sum_le a s ha0 hs hs1 ℓ N
      _ = N * C * r ^ ℓ := by
        simpa [q, κ, r, C] using divisorBlockMomentBound_eq_geometric a s ℓ N
  have hgeom : ∀ m : ℕ, (∑ i ∈ Finset.range m, r ^ i) ≤ (1 - r)⁻¹ := by
    intro m
    calc
      (∑ i ∈ Finset.range m, r ^ i) ≤ ∑' i : ℕ, r ^ i := by
        exact (hasSum_geometric_of_lt_one hr0 hr1).summable.sum_le_tsum
          (Finset.range m) (fun i hi => pow_nonneg hr0 i)
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hmass : ∀ n ∈ Finset.Icc 1 N,
      Real.rpow (largeDivisorMass a (dyadicExpCutoff L) n) s ≤
        ∑ i ∈ Finset.range N, Real.rpow (divisorBlockMass a (L + i) n) s := by
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    calc
      Real.rpow (largeDivisorMass a (dyadicExpCutoff L) n) s =
          Real.rpow (∑ i ∈ Finset.range n, divisorBlockMass a (L + i) n) s := by
        rw [largeDivisorMass_eq_block_sum a L n hnI.1]
      _ ≤ ∑ i ∈ Finset.range n, Real.rpow (divisorBlockMass a (L + i) n) s := by
        exact rpow_finset_sum_le_sum_rpow (Finset.range n)
          (fun i => divisorBlockMass a (L + i) n)
          (fun i hi => divisorBlockMass_nonneg a (L + i) n) s hs hs1
      _ ≤ ∑ i ∈ Finset.range N, Real.rpow (divisorBlockMass a (L + i) n) s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnI.2)
        intro i hiN hin
        exact Real.rpow_nonneg (divisorBlockMass_nonneg a (L + i) n) _
  calc
    (∑ n ∈ Finset.Icc 1 N,
        Real.rpow (largeDivisorMass a (dyadicExpCutoff L) n) s) ≤
        ∑ n ∈ Finset.Icc 1 N,
          ∑ i ∈ Finset.range N, Real.rpow (divisorBlockMass a (L + i) n) s := by
      exact Finset.sum_le_sum fun n hn => hmass n hn
    _ = ∑ i ∈ Finset.range N,
        ∑ n ∈ Finset.Icc 1 N, Real.rpow (divisorBlockMass a (L + i) n) s := by
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ Finset.range N, N * C * r ^ (L + i) := by
      exact Finset.sum_le_sum fun i hi => hblock (L + i)
    _ = N * C * r ^ L * (∑ i ∈ Finset.range N, r ^ i) := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
      ring
    _ ≤ N * C * r ^ L * (1 - r)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (hgeom N) (by positivity)
    _ = N * (K * r ^ L) := by
      simp only [K]
      ring
    _ ≤ ε * N := by
      calc
        (N : ℝ) * (K * r ^ L) ≤ N * ε :=
          mul_le_mul_of_nonneg_left hchoice.le (by positivity)
        _ = ε * N := by ring

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

/-! ### Random selected-divisor moments -/

/-- The positive-integer Lambert denominators form a summable family. -/
lemma summable_ebLambert_denom (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun m : ℕ => (1 : ℝ) / ((b : ℝ) ^ (m + 1) - 1)) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hgeom : Summable (fun m : ℕ => 2 * (1 / (b : ℝ)) ^ (m + 1)) := by
    exact ((summable_geometric_of_lt_one (by positivity)
      (by simpa using one_div_lt_one_div_of_lt zero_lt_one hb1)).mul_left 2).comp_injective
        Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun m => by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (one_le_pow₀ hb1.le))) (fun m => ?_) hgeom
  have hpow : (2 : ℝ) ≤ (b : ℝ) ^ (m + 1) := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ = (b : ℝ) ^ 1 := by ring
      _ ≤ (b : ℝ) ^ (m + 1) := pow_le_pow_right₀ hb1.le (by omega)
  have hden : 0 < (b : ℝ) ^ (m + 1) - 1 := by linarith
  have hbpowpos : (0 : ℝ) < (b : ℝ) ^ (m + 1) := by positivity
  calc
    1 / ((b : ℝ) ^ (m + 1) - 1) ≤ 2 / (b : ℝ) ^ (m + 1) := by
      rw [div_le_div_iff₀ hden hbpowpos]
      nlinarith
    _ = 2 * (1 / (b : ℝ)) ^ (m + 1) := by
      rw [div_pow]
      simp only [one_pow]
      ring

/-- Every selected Erdős--Borwein subseries is absolutely summable. -/
lemma summable_ebLambert_terms (b : ℕ) (hb : 2 ≤ b)
    {Ω : Type*} (X : ℕ → Ω → Bool) (w : Ω) :
    Summable (fun m : ℕ =>
      (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) := by
  apply (summable_ebLambert_denom b hb).of_norm_bounded
  intro m
  have hbR : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hden : 0 < (b : ℝ) ^ (m + 1) - 1 :=
    sub_pos.mpr (one_lt_pow₀ hbR (by omega))
  split_ifs <;> simp only [norm_div, Real.norm_eq_abs, abs_one, abs_zero, zero_div]
  · rw [abs_of_pos hden]
  · exact div_nonneg (by norm_num) hden.le

/-- The selected Erdős--Borwein series is measurable when every coordinate is measurable. -/
lemma measurable_ebLambert (b : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) :
    Measurable (ebLambert b X) := by
  unfold ebLambert
  exact Measurable.tsum fun m => by
    have hm : Measurable (fun w => if X (m + 1) w then (1 : ℝ) else 0) :=
      (measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp (hX (m + 1))
    exact hm.div_const _

/-- Number of selected divisors of `n` lying strictly above `M`, viewed as a real random
variable.  It is a finite sum even though the selected set itself can be infinite. -/
noncomputable def selectedDivisorCount {Ω : Type*} (X : ℕ → Ω → Bool)
    (M n : ℕ) (w : Ω) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => M < m), if X m w then 1 else 0

lemma selectedDivisorCount_nonneg {Ω : Type*} (X : ℕ → Ω → Bool) (M n : ℕ) (w : Ω) :
    0 ≤ selectedDivisorCount X M n w := by
  unfold selectedDivisorCount
  exact Finset.sum_nonneg fun m _ => by split_ifs <;> positivity

lemma selectedDivisorCount_le_card_divisors {Ω : Type*} (X : ℕ → Ω → Bool)
    (M n : ℕ) (w : Ω) : selectedDivisorCount X M n w ≤ n.divisors.card := by
  unfold selectedDivisorCount
  calc
    (∑ m ∈ n.divisors.filter (fun m => M < m), if X m w then (1 : ℝ) else 0) ≤
        ∑ _m ∈ n.divisors.filter (fun m => M < m), (1 : ℝ) := by
      exact Finset.sum_le_sum fun m _ => by split_ifs <;> norm_num
    _ = ((n.divisors.filter (fun m => M < m)).card : ℝ) := by simp
    _ ≤ n.divisors.card := by exact_mod_cast Finset.card_filter_le _ _

lemma measurable_selectedDivisorCount {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (M n : ℕ) :
    Measurable (selectedDivisorCount X M n) := by
  unfold selectedDivisorCount
  exact Finset.measurable_sum _ fun m _ =>
    (measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp (hX m)

lemma integrable_selectedDivisorCount {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n : ℕ) :
    Integrable (selectedDivisorCount X M n) μ := by
  apply Integrable.of_bound (measurable_selectedDivisorCount X hX M n).aestronglyMeasurable
    n.divisors.card
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (selectedDivisorCount_nonneg X M n w)]
  exact selectedDivisorCount_le_card_divisors X M n w

lemma integral_selectedIndicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (m : ℕ) :
    (∫ w, (if X m w then (1 : ℝ) else 0) ∂μ) = μ.real {w | X m w = true} := by
  let A : Set Ω := {w | X m w = true}
  have hA : MeasurableSet A := (hX m) (measurableSet_singleton true)
  have hfun : (fun w => if X m w then (1 : ℝ) else 0) = A.indicator (fun _ => 1) := by
    funext w
    by_cases hw : X m w = true
    · simp [A, hw]
    · have hw' : X m w = false := Bool.eq_false_of_not_eq_true hw
      simp [A, hw']
  rw [hfun, integral_indicator_const _ hA]
  simp [A]

/-- The expectation of the selected-divisor count uses only the one-coordinate marginals. -/
lemma integral_selectedDivisorCount {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n : ℕ) :
    (∫ w, selectedDivisorCount X M n w ∂μ) =
      ∑ m ∈ n.divisors.filter (fun m => M < m), μ.real {w | X m w = true} := by
  unfold selectedDivisorCount
  calc
    (∫ w, ∑ m ∈ n.divisors.filter (fun m => M < m),
        (if X m w then (1 : ℝ) else 0) ∂μ) =
        ∑ m ∈ n.divisors.filter (fun m => M < m),
          ∫ w, (if X m w then (1 : ℝ) else 0) ∂μ := by
      apply integral_finsetSum
      intro m hm
      apply Integrable.of_bound
        ((measurable_of_finite (f := fun z : Bool => if z then (1 : ℝ) else 0)).comp
          (hX m)).aestronglyMeasurable 1
      exact Eventually.of_forall fun w => by
        simp only [Function.comp_apply]
        split_ifs <;> norm_num
    _ = _ := Finset.sum_congr rfl fun m _ => integral_selectedIndicator μ X hX m

/-- Jensen converts the marginal first-moment estimate into exactly the fractional divisor
moment used by `largeDivisorMass_moment_small`.  No independence is used. -/
lemma integral_selectedDivisorCount_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m))
    (a C s : ℝ) (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hMarginal : ∀ m : ℕ, 2 ≤ m →
      μ {w | X m w = true} ≤ ENNReal.ofReal (C * Real.rpow (Real.log m) (-a)))
    (M n : ℕ) (hM : 2 ≤ M) :
    (∫ w, Real.rpow (selectedDivisorCount X M n w) s ∂μ) ≤
      Real.rpow C s * Real.rpow (largeDivisorMass a M n) s := by
  have hD0 : ∀ w, 0 ≤ selectedDivisorCount X M n w :=
    selectedDivisorCount_nonneg X M n
  have hDint := integrable_selectedDivisorCount μ X hX M n
  have hDpowMeas : Measurable (fun w => Real.rpow (selectedDivisorCount X M n w) s) :=
    (Real.continuous_rpow_const hs.le).measurable.comp
      (measurable_selectedDivisorCount X hX M n)
  have hDpowInt : Integrable (fun w => Real.rpow (selectedDivisorCount X M n w) s) μ := by
    apply Integrable.of_bound hDpowMeas.aestronglyMeasurable
      (Real.rpow (n.divisors.card : ℝ) s)
    filter_upwards [] with w
    rw [Real.norm_eq_abs]
    calc
      |Real.rpow (selectedDivisorCount X M n w) s| =
          Real.rpow (selectedDivisorCount X M n w) s :=
        abs_of_nonneg (Real.rpow_nonneg (hD0 w) _)
      _ ≤ Real.rpow (n.divisors.card : ℝ) s :=
        Real.rpow_le_rpow (hD0 w)
          (selectedDivisorCount_le_card_divisors X M n w) hs.le
  have hmean : (∫ w, selectedDivisorCount X M n w ∂μ) ≤ C * largeDivisorMass a M n := by
    rw [integral_selectedDivisorCount μ X hX M n]
    unfold largeDivisorMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hmM : M < m := (Finset.mem_filter.mp hm).2
    have hprod0 : 0 ≤ C * Real.rpow (Real.log m) (-a) :=
      mul_nonneg hC (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))) _)
    calc
      μ.real {w | X m w = true} = (μ {w | X m w = true}).toReal := rfl
      _ ≤ (ENNReal.ofReal (C * Real.rpow (Real.log m) (-a))).toReal := by
        exact ENNReal.toReal_mono (by simp) (hMarginal m (by omega))
      _ = C * Real.rpow (Real.log m) (-a) := ENNReal.toReal_ofReal hprod0
  have hJensen : (∫ w, Real.rpow (selectedDivisorCount X M n w) s ∂μ) ≤
      Real.rpow (∫ w, selectedDivisorCount X M n w ∂μ) s := by
    change (∫ w, selectedDivisorCount X M n w ^ s ∂μ) ≤
      (∫ w, selectedDivisorCount X M n w ∂μ) ^ s
    exact (Real.concaveOn_rpow hs.le hs1).le_map_integral
      (Real.continuous_rpow_const hs.le).continuousOn isClosed_Ici
      (Eventually.of_forall hD0) hDint hDpowInt
  calc
    (∫ w, Real.rpow (selectedDivisorCount X M n w) s ∂μ) ≤
        Real.rpow (∫ w, selectedDivisorCount X M n w ∂μ) s := hJensen
    _ ≤ Real.rpow (C * largeDivisorMass a M n) s := by
      exact Real.rpow_le_rpow (integral_nonneg hD0) hmean hs.le
    _ = Real.rpow C s * Real.rpow (largeDivisorMass a M n) s := by
      exact Real.mul_rpow hC (by
        unfold largeDivisorMass
        exact Finset.sum_nonneg fun m hm => Real.rpow_nonneg
          (Real.log_nonneg (by
            have hmM : M < m := (Finset.mem_filter.mp hm).2
            exact_mod_cast (show 1 ≤ m by omega))) _)

/-! ### Lambert tails and shift residuals -/

/-- The selected Lambert tail after deleting the first `M` positive indices. -/
noncomputable def ebLambertTail {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool)
    (M : ℕ) (w : Ω) : ℝ :=
  ∑' j : ℕ, (if X (M + j + 1) w then (1 : ℝ) else 0) /
    ((b : ℝ) ^ (M + j + 1) - 1)

/-- The full selected Lambert series is its finite head plus `ebLambertTail`. -/
lemma ebLambert_eq_head_add_tail (b : ℕ) (hb : 2 ≤ b) {Ω : Type*}
    (X : ℕ → Ω → Bool) (M : ℕ) (w : Ω) :
    ebLambert b X w =
      (∑ m ∈ Finset.range M,
        (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)) +
        ebLambertTail b X M w := by
  let f : ℕ → ℝ := fun m =>
    (if X (m + 1) w then (1 : ℝ) else 0) / ((b : ℝ) ^ (m + 1) - 1)
  have hf : Summable f := summable_ebLambert_terms b hb X w
  rw [ebLambert, show (fun m => (if X (m + 1) w then (1 : ℝ) else 0) /
      ((b : ℝ) ^ (m + 1) - 1)) = f from rfl]
  rw [← hf.sum_add_tsum_nat_add M]
  unfold ebLambertTail
  apply congrArg (fun z => (∑ m ∈ Finset.range M, f m) + z)
  apply tsum_congr
  intro j
  simp only [f]
  rw [show j + M + 1 = M + j + 1 by omega]

/-- The geometric shift residual
`Σ_{j ≥ 1} b⁻ʲ #{m > M : X_m = 1, m ∣ n+j}`. -/
noncomputable def shiftResidual {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool)
    (M n : ℕ) (w : Ω) : ℝ :=
  ∑' j : ℕ, (1 / (b : ℝ)) ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w

/-- The residual converges pointwise; the crude divisor bound is only linear and is absorbed by
the geometric weight. -/
lemma summable_shiftResidual_terms {Ω : Type*} (b : ℕ) (hb : 2 ≤ b)
    (X : ℕ → Ω → Bool) (M n : ℕ) (w : Ω) :
    Summable (fun j : ℕ =>
      (1 / (b : ℝ)) ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w) := by
  let r : ℝ := 1 / (b : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    rw [div_lt_one (by positivity : (0 : ℝ) < b)]
    exact_mod_cast (show 1 < b by omega)
  have hgeom : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_norm_lt_one hr1
  have hjgeom : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr1)
  have hmajor : Summable (fun j : ℕ => r * ((n + 1 : ℝ) * r ^ j + (j : ℝ) * r ^ j)) :=
    ((hgeom.mul_left ((n : ℝ) + 1)).add hjgeom).mul_left r
  apply hmajor.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr0 _)
    (selectedDivisorCount_nonneg X M _ w))]
  calc
    r ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w ≤
        r ^ (j + 1) * ((n + j + 1 : ℕ) : ℝ) := by
      have hcount : selectedDivisorCount X M (n + j + 1) w ≤ (n + j + 1 : ℕ) := by
        exact (selectedDivisorCount_le_card_divisors X M (n + j + 1) w).trans
          (by exact_mod_cast Nat.card_divisors_le_self (n + j + 1))
      exact mul_le_mul_of_nonneg_left hcount (pow_nonneg hr0 _)
    _ = r * ((n + 1 : ℝ) * r ^ j + (j : ℝ) * r ^ j) := by
      push_cast
      rw [pow_succ]
      ring

lemma shiftResidual_nonneg {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool)
    (M n : ℕ) (w : Ω) : 0 ≤ shiftResidual b X M n w := by
  unfold shiftResidual
  exact tsum_nonneg fun j => mul_nonneg (pow_nonneg (by positivity) _)
    (selectedDivisorCount_nonneg X M _ w)

lemma measurable_shiftResidual {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (M n : ℕ) :
    Measurable (shiftResidual b X M n) := by
  unfold shiftResidual
  exact Measurable.tsum fun j =>
    (measurable_selectedDivisorCount X hX M (n + j + 1)).const_mul _

/-- `selectedDivisorCount` really is the cardinality of the selected divisor filter. -/
lemma selectedDivisorCount_eq_card {Ω : Type*} (X : ℕ → Ω → Bool)
    (M n : ℕ) (w : Ω) :
    selectedDivisorCount X M n w =
      (((n.divisors.filter (fun m => M < m)).filter (fun m => X m w)).card : ℝ) := by
  unfold selectedDivisorCount
  simp [Finset.filter_filter]

lemma selectedDivisorCount_rpow_le_self {Ω : Type*} (X : ℕ → Ω → Bool)
    (M n : ℕ) (w : Ω) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (selectedDivisorCount X M n w) s ≤ selectedDivisorCount X M n w := by
  rw [selectedDivisorCount_eq_card]
  by_cases hcard : ((n.divisors.filter (fun m => M < m)).filter (fun m => X m w)).card = 0
  · simp [hcard, Real.zero_rpow hs.ne']
  · exact Real.rpow_le_self_of_one_le (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcard)) hs1

/-- The fractional powers of the residual terms are themselves summable. -/
lemma summable_shiftResidual_rpow_terms {Ω : Type*} (b : ℕ) (hb : 2 ≤ b)
    (X : ℕ → Ω → Bool) (M n : ℕ) (w : Ω) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Summable (fun j : ℕ => Real.rpow
      ((1 / (b : ℝ)) ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w) s) := by
  let r : ℝ := 1 / (b : ℝ)
  let q : ℝ := Real.rpow r s
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < b)]
    exact_mod_cast (show 1 < b by omega)
  have hq0 : 0 ≤ q := Real.rpow_nonneg hr0 _
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact Real.rpow_lt_one hr0 hr1 hs
  have hgeom : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_norm_lt_one hq1
  have hjgeom : Summable (fun j : ℕ => (j : ℝ) * q ^ j) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hq1)
  have hmajor : Summable (fun j : ℕ => q * ((n + 1 : ℝ) * q ^ j + (j : ℝ) * q ^ j)) :=
    ((hgeom.mul_left ((n : ℝ) + 1)).add hjgeom).mul_left q
  apply hmajor.of_norm_bounded
  intro j
  have hD0 := selectedDivisorCount_nonneg X M (n + j + 1) w
  have hterm0 : 0 ≤ r ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w :=
    mul_nonneg (pow_nonneg hr0 _) hD0
  have hweight : Real.rpow (r ^ (j + 1)) s = q ^ (j + 1) := by
    calc
      Real.rpow (r ^ (j + 1)) s = Real.rpow r ((j + 1 : ℕ) * s) :=
        (Real.rpow_natCast_mul hr0 (j + 1) s).symm
      _ = Real.rpow r (s * (j + 1 : ℕ)) := by congr 1; ring
      _ = (Real.rpow r s) ^ (j + 1) := Real.rpow_mul_natCast hr0 s (j + 1)
      _ = q ^ (j + 1) := rfl
  change |Real.rpow (r ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w) s| ≤ _
  calc
    |Real.rpow (r ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w) s| =
        Real.rpow (r ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w) s :=
      abs_of_nonneg (Real.rpow_nonneg hterm0 _)
    _ = q ^ (j + 1) * Real.rpow (selectedDivisorCount X M (n + j + 1) w) s := by
      exact (Real.mul_rpow (pow_nonneg hr0 _) hD0).trans
        (congrArg (fun z => z * Real.rpow (selectedDivisorCount X M (n + j + 1) w) s) hweight)
    _ ≤ q ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w := by
      exact mul_le_mul_of_nonneg_left
        (selectedDivisorCount_rpow_le_self X M _ w s hs hs1) (pow_nonneg hq0 _)
    _ ≤ q ^ (j + 1) * ((n + j + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        ((selectedDivisorCount_le_card_divisors X M _ w).trans
          (by exact_mod_cast Nat.card_divisors_le_self (n + j + 1))) (pow_nonneg hq0 _)
    _ = q * ((n + 1 : ℝ) * q ^ j + (j : ℝ) * q ^ j) := by
      push_cast
      rw [pow_succ]
      ring

/-- Fractional-power subadditivity passes from finite residuals to the convergent residual. -/
lemma shiftResidual_rpow_le_tsum {Ω : Type*} (b : ℕ) (hb : 2 ≤ b)
    (X : ℕ → Ω → Bool) (M n : ℕ) (w : Ω) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (shiftResidual b X M n w) s ≤
      ∑' j : ℕ, Real.rpow
        ((1 / (b : ℝ)) ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w) s := by
  let f : ℕ → ℝ := fun j =>
    (1 / (b : ℝ)) ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w
  have hf : Summable f := summable_shiftResidual_terms b hb X M n w
  have hfpow : Summable (fun j => Real.rpow (f j) s) :=
    summable_shiftResidual_rpow_terms b hb X M n w s hs hs1
  apply le_of_tendsto_of_tendsto'
    ((Real.continuousAt_rpow_const (∑' j, f j) s (Or.inr hs.le)).tendsto.comp
      hf.hasSum.tendsto_sum_nat)
    hfpow.hasSum.tendsto_sum_nat
  intro J
  exact rpow_finset_sum_le_sum_rpow (Finset.range J) f
    (fun j hj => mul_nonneg (pow_nonneg (by positivity) _)
      (selectedDivisorCount_nonneg X M _ w)) s hs hs1

/-- The finite residual used before passing to the infinite series. -/
noncomputable def shiftResidualPartial {Ω : Type*} (b : ℕ) (X : ℕ → Ω → Bool)
    (M n J : ℕ) (w : Ω) : ℝ :=
  ∑ j ∈ Finset.range J,
    (1 / (b : ℝ)) ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w

lemma integrable_selectedDivisorCount_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun w => Real.rpow (selectedDivisorCount X M n w) s) μ := by
  apply Integrable.of_bound
    ((Real.continuous_rpow_const hs.le).measurable.comp
      (measurable_selectedDivisorCount X hX M n)).aestronglyMeasurable
    (Real.rpow (n.divisors.card : ℝ) s)
  filter_upwards [] with w
  change |Real.rpow (selectedDivisorCount X M n w) s| ≤ _
  calc
    |Real.rpow (selectedDivisorCount X M n w) s| =
        Real.rpow (selectedDivisorCount X M n w) s :=
      abs_of_nonneg (Real.rpow_nonneg (selectedDivisorCount_nonneg X M n w) _)
    _ ≤ Real.rpow (n.divisors.card : ℝ) s :=
      Real.rpow_le_rpow (selectedDivisorCount_nonneg X M n w)
        (selectedDivisorCount_le_card_divisors X M n w) hs.le

/-- The finite shift residual obeys exactly the expected marginal/Jensen moment estimate.
This is the integrable finite approximation to the infinite residual bound. -/
lemma integral_shiftResidualPartial_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m))
    (a C s : ℝ) (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hMarginal : ∀ m : ℕ, 2 ≤ m →
      μ {w | X m w = true} ≤ ENNReal.ofReal (C * Real.rpow (Real.log m) (-a)))
    (M n J : ℕ) (hM : 2 ≤ M) :
    (∫ w, Real.rpow (shiftResidualPartial b X M n J w) s ∂μ) ≤
      Real.rpow C s * ∑ j ∈ Finset.range J,
        Real.rpow ((1 / (b : ℝ)) ^ (j + 1)) s *
          Real.rpow (largeDivisorMass a M (n + j + 1)) s := by
  let r : ℝ := 1 / (b : ℝ)
  let f : ℕ → Ω → ℝ := fun j w =>
    r ^ (j + 1) * selectedDivisorCount X M (n + j + 1) w
  let g : ℕ → Ω → ℝ := fun j w => Real.rpow (f j w) s
  have hr0 : 0 ≤ r := by positivity
  have hf0 : ∀ j w, 0 ≤ f j w := fun j w =>
    mul_nonneg (pow_nonneg hr0 _) (selectedDivisorCount_nonneg X M _ w)
  have hDpowInt : ∀ j, Integrable
      (fun w => Real.rpow (selectedDivisorCount X M (n + j + 1) w) s) μ := fun j =>
    integrable_selectedDivisorCount_rpow μ X hX M (n + j + 1) s hs
  have hgInt : ∀ j, Integrable (g j) μ := by
    intro j
    have hconst : ∀ w, g j w = Real.rpow (r ^ (j + 1)) s *
        Real.rpow (selectedDivisorCount X M (n + j + 1) w) s := by
      intro w
      exact Real.mul_rpow (pow_nonneg hr0 _) (selectedDivisorCount_nonneg X M _ w)
    rw [funext hconst]
    exact (hDpowInt j).const_mul _
  have hsumInt : Integrable (fun w => ∑ j ∈ Finset.range J, g j w) μ :=
    integrable_finsetSum (Finset.range J) fun j hj => hgInt j
  have hpartialMeas : Measurable (shiftResidualPartial b X M n J) := by
    unfold shiftResidualPartial
    exact Finset.measurable_sum _ fun j hj =>
      (measurable_selectedDivisorCount X hX M (n + j + 1)).const_mul _
  have hleftInt : Integrable (fun w => Real.rpow (shiftResidualPartial b X M n J w) s) μ := by
    apply hsumInt.mono'
    · exact ((Real.continuous_rpow_const hs.le).measurable.comp hpartialMeas).aestronglyMeasurable
    · filter_upwards [] with w
      change |Real.rpow (∑ j ∈ Finset.range J, f j w) s| ≤ _
      calc
        |Real.rpow (∑ j ∈ Finset.range J, f j w) s| =
            Real.rpow (∑ j ∈ Finset.range J, f j w) s :=
          abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun j hj => hf0 j w) _)
        _ ≤ ∑ j ∈ Finset.range J, g j w :=
          rpow_finset_sum_le_sum_rpow (Finset.range J) (fun j => f j w)
            (fun j hj => hf0 j w) s hs hs1
  calc
    (∫ w, Real.rpow (shiftResidualPartial b X M n J w) s ∂μ) ≤
        ∫ w, ∑ j ∈ Finset.range J, g j w ∂μ := by
      apply integral_mono hleftInt hsumInt
      intro w
      exact rpow_finset_sum_le_sum_rpow (Finset.range J) (fun j => f j w)
        (fun j hj => hf0 j w) s hs hs1
    _ = ∑ j ∈ Finset.range J, ∫ w, g j w ∂μ := by
      exact integral_finsetSum _ fun j hj => hgInt j
    _ ≤ ∑ j ∈ Finset.range J,
        Real.rpow (r ^ (j + 1)) s *
          (Real.rpow C s * Real.rpow (largeDivisorMass a M (n + j + 1)) s) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjensen := integral_selectedDivisorCount_rpow_le μ X hX a C s hC hs hs1
        hMarginal M (n + j + 1) hM
      have hconst : ∀ w, g j w = Real.rpow (r ^ (j + 1)) s *
          Real.rpow (selectedDivisorCount X M (n + j + 1) w) s := by
        intro w
        exact Real.mul_rpow (pow_nonneg hr0 _) (selectedDivisorCount_nonneg X M _ w)
      rw [show (∫ w, g j w ∂μ) = Real.rpow (r ^ (j + 1)) s *
          ∫ w, Real.rpow (selectedDivisorCount X M (n + j + 1) w) s ∂μ by
        simp_rw [hconst]; rw [integral_const_mul]]
      exact mul_le_mul_of_nonneg_left hjensen (Real.rpow_nonneg (pow_nonneg hr0 _) _)
    _ = Real.rpow C s * ∑ j ∈ Finset.range J,
        Real.rpow ((1 / (b : ℝ)) ^ (j + 1)) s *
          Real.rpow (largeDivisorMass a M (n + j + 1)) s := by
      simp only [r]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

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
