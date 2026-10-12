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
