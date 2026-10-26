/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinNegative

/-!
# Marginal criterion for sub-power Erdős--Borwein weights

This file isolates the probabilistic/Fatou part of the sub-power argument.  Its hypotheses involve
only the one-coordinate marginals.  The remaining arithmetic task is to verify that the capped
deterministic residual tends to zero for `subpowerWeight`.
-/

namespace NormalNumbers.ErdosBorweinSubpower

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinRandom

/-- Expected number of selected divisors above `M`, expressed using only the marginal masses. -/
noncomputable def marginalDivisorMass (delta : ℕ → ℝ) (M n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => M < m), delta m

lemma marginalDivisorMass_nonneg (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m) (M n : ℕ) :
    0 ≤ marginalDivisorMass delta M n := by
  unfold marginalDivisorMass
  exact Finset.sum_nonneg fun m _ => hdelta m

lemma marginalDivisorMass_le_card_divisors (delta : ℕ → ℝ)
    (hdelta : ∀ m, delta m ≤ 1) (M n : ℕ) :
    marginalDivisorMass delta M n ≤ n.divisors.card := by
  unfold marginalDivisorMass
  calc
    (∑ m ∈ n.divisors.filter (fun m => M < m), delta m) ≤
        ∑ _m ∈ n.divisors.filter (fun m => M < m), (1 : ℝ) := by
      exact Finset.sum_le_sum fun m _ => hdelta m
    _ = ((n.divisors.filter (fun m => M < m)).card : ℝ) := by simp
    _ ≤ n.divisors.card := by exact_mod_cast Finset.card_filter_le _ _

/-! ### Weighted logarithmic blocks

The sub-power argument uses the same double-exponential divisor blocks as the power-weight
argument, but the weight and the fractional-moment exponent now vary with the block.  The next
lemmas separate the combinatorial and Markov steps from the eventual real-variable estimates for
the particular sub-power weight. -/

/-- Contribution of an arbitrary weight from one double-exponential divisor block. -/
noncomputable def weightedDivisorBlockMass (weight : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter
    (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1)), weight d

lemma weightedDivisorBlockMass_nonneg (weight : ℕ → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (ℓ n : ℕ) :
    0 ≤ weightedDivisorBlockMass weight ℓ n := by
  unfold weightedDivisorBlockMass
  exact Finset.sum_nonneg fun d _ => hweight d

/-- A pointwise cap on the weight throughout a block converts its mass to the already-controlled
smooth-divisor count at the right endpoint. -/
lemma weightedDivisorBlockMass_le_smoothDivisorCount
    (weight : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W) (ℓ n : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) → weight d ≤ W) :
    weightedDivisorBlockMass weight ℓ n ≤
      (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W := by
  let S := n.divisors.filter
    (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1))
  calc
    weightedDivisorBlockMass weight ℓ n = ∑ d ∈ S, weight d := rfl
    _ ≤ ∑ _d ∈ S, W := by
      exact Finset.sum_le_sum fun d hd =>
        hweight d (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hd).2.2
    _ = (S.card : ℝ) * W := by simp [mul_comm]
    _ ≤ (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast divisorBlock_card_le n ℓ) hW

/-- Fractional moment of an arbitrary weighted block.  All dependence on the weight is through a
single block cap `W`; the smooth-divisor Euler product is uniform in `s ∈ (0,1]`. -/
lemma weightedDivisorBlockMass_rpow_sum_le
    (weight : ℕ → ℝ) (W s : ℝ) (hweight0 : ∀ d, 0 ≤ weight d) (hW : 0 ≤ W)
    (hs : 0 < s) (hs1 : s ≤ 1) (ℓ N : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) → weight d ≤ W) :
    (∑ n ∈ Finset.Icc 1 N, Real.rpow (weightedDivisorBlockMass weight ℓ n) s) ≤
      Real.rpow W s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  have hpoint : ∀ n, Real.rpow (weightedDivisorBlockMass weight ℓ n) s ≤
      Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s * Real.rpow W s := by
    intro n
    calc
      Real.rpow (weightedDivisorBlockMass weight ℓ n) s ≤
          Real.rpow ((smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W) s := by
        exact Real.rpow_le_rpow (weightedDivisorBlockMass_nonneg weight hweight0 ℓ n)
          (weightedDivisorBlockMass_le_smoothDivisorCount weight W hW ℓ n hweight) hs.le
      _ = Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
          Real.rpow W s := by
        exact Real.mul_rpow (by positivity) hW
  calc
    (∑ n ∈ Finset.Icc 1 N, Real.rpow (weightedDivisorBlockMass weight ℓ n) s) ≤
        ∑ n ∈ Finset.Icc 1 N,
          Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
            Real.rpow W s := by
      exact Finset.sum_le_sum fun n _ => hpoint n
    _ = Real.rpow W s *
        ∑ n ∈ Finset.Icc 1 N,
          Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s := by
      simp [Finset.mul_sum, mul_comm]
    _ ≤ Real.rpow W s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
      exact mul_le_mul_of_nonneg_left
        (smoothDivisorCount_rpow_sum_le_log_rpow s hs hs1 (dyadicExpCutoff (ℓ + 1))
          (dyadicExpCutoff_two_le (ℓ + 1)) N)
        (Real.rpow_nonneg hW _)

/-- Per-block counting Chernoff bound.  This is the exact form needed before summing over the shift
thresholds and over blocks: every large value pays `Y^s`, while the numerator is the uniform
smooth-divisor fractional moment. -/
lemma weightedDivisorBlockMass_large_card_mul_rpow_le
    (weight : ℕ → ℝ) (W Y s : ℝ) (hweight0 : ∀ d, 0 ≤ weight d) (hW : 0 ≤ W)
    (hY : 0 ≤ Y) (hs : 0 < s) (hs1 : s ≤ 1) (ℓ N : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) → weight d ≤ W) :
    (((Finset.Icc 1 N).filter
        (fun n => Y < weightedDivisorBlockMass weight ℓ n)).card : ℝ) * Real.rpow Y s ≤
      Real.rpow W s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  let S := (Finset.Icc 1 N).filter
    (fun n => Y < weightedDivisorBlockMass weight ℓ n)
  calc
    (S.card : ℝ) * Real.rpow Y s = ∑ _n ∈ S, Real.rpow Y s := by simp [mul_comm]
    _ ≤ ∑ n ∈ S, Real.rpow (weightedDivisorBlockMass weight ℓ n) s := by
      exact Finset.sum_le_sum fun n hn =>
        (Real.rpow_lt_rpow hY (Finset.mem_filter.mp hn).2 hs).le
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.rpow (weightedDivisorBlockMass weight ℓ n) s := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => Real.rpow_nonneg
          (weightedDivisorBlockMass_nonneg weight hweight0 ℓ n) _)
    _ ≤ _ := weightedDivisorBlockMass_rpow_sum_le weight W s hweight0 hW hs hs1 ℓ N hweight

/-! ### The analytic Chernoff exponent -/

/-- Cubic Taylor control in the exact form used for the variable block exponent. -/
lemma exp_sub_one_sub_le_sq_half_add_cube {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 + x ^ 3 := by
  have h := Real.exp_bound' hx0 hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  nlinarith [mul_nonneg (sq_nonneg x) hx0]

/-- Algebraic core of the per-block exponent estimate.  The two displayed identities are exactly
what the later specialization `σ = sqrt (c log u / u)` supplies. -/
lemma chernoffExponent_le
    (u c σ : ℝ) (hu : 0 ≤ u) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hsq : u * σ ^ 2 = c * Real.log u)
    (hlin : σ * Real.sqrt (c * u * Real.log u) = c * Real.log u) :
    u * (Real.exp σ - 1 - σ) - σ * Real.sqrt (c * u * Real.log u) ≤
      -(c / 2) * Real.log u + u * σ ^ 3 := by
  have h := mul_le_mul_of_nonneg_left (exp_sub_one_sub_le_sq_half_add_cube hσ0 hσ1) hu
  rw [mul_add] at h
  have hquad : u * (σ ^ 2 / 2) = c * Real.log u / 2 := by
    rw [← mul_div_assoc, hsq]
  rw [hquad] at h
  rw [hlin]
  linarith

/-- The variable Chernoff exponent attached to a logarithmic block parameter `u`. -/
noncomputable def blockSigma (c u : ℝ) : ℝ :=
  Real.sqrt (c * Real.log u / u)

lemma blockSigma_sq (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    u * blockSigma c u ^ 2 = c * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  rw [blockSigma, Real.sq_sqrt (div_nonneg (mul_nonneg hc hlog) hu0.le)]
  field_simp

lemma blockSigma_mul_sqrt (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    blockSigma c u * Real.sqrt (c * u * Real.log u) = c * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hA : 0 ≤ c * Real.log u := mul_nonneg hc (Real.log_nonneg hu)
  have hsqrtu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  rw [blockSigma, Real.sqrt_div hA]
  rw [show c * u * Real.log u = u * (c * Real.log u) by ring, Real.sqrt_mul hu0.le]
  field_simp [ne_of_gt hsqrtu]
  rw [Real.sq_sqrt hA]

lemma blockSigma_cubic (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    u * blockSigma c u ^ 3 = c * Real.log u * blockSigma c u := by
  calc
    u * blockSigma c u ^ 3 = (u * blockSigma c u ^ 2) * blockSigma c u := by ring
    _ = c * Real.log u * blockSigma c u := by rw [blockSigma_sq c u hc hu]

lemma blockSigma_le_one (c u : ℝ) (hu : 1 ≤ u)
    (hbudget : c * Real.log u ≤ u) : blockSigma c u ≤ 1 := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  rw [blockSigma, Real.sqrt_le_one]
  exact (div_le_one hu0).mpr hbudget

/-- The per-block exponent bound after substituting `σ = sqrt(c log u / u)`.  Subsequent work only
has to make the cubic remainder small and choose `u` large enough that `σ ≤ 1`. -/
lemma chernoffExponent_blockSigma_le
    (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) (hbudget : c * Real.log u ≤ u) :
    u * (Real.exp (blockSigma c u) - 1 - blockSigma c u) -
        blockSigma c u * Real.sqrt (c * u * Real.log u) ≤
      -(c / 2) * Real.log u + u * blockSigma c u ^ 3 := by
  exact chernoffExponent_le u c (blockSigma c u) (zero_le_one.trans hu) (Real.sqrt_nonneg _)
    (blockSigma_le_one c u hu hbudget) (blockSigma_sq c u hc hu)
    (blockSigma_mul_sqrt c u hc hu)

/-- Explicit slack form of the exponent estimate.  Once `blockSigma c u ≤ ρ`, any fixed
`ρ < 1/2` turns the cubic remainder into only a `ρ`-fraction of the main decay. -/
lemma chernoffExponent_blockSigma_le_slack
    (c u ρ : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) (hρhalf : ρ < 1 / 2)
    (hσρ : blockSigma c u ≤ ρ) :
    u * (Real.exp (blockSigma c u) - 1 - blockSigma c u) -
        blockSigma c u * Real.sqrt (c * u * Real.log u) ≤
      -(1 / 2 - ρ) * c * Real.log u := by
  have hσ1 : blockSigma c u ≤ 1 := by linarith
  have hmain := chernoffExponent_le u c (blockSigma c u) (zero_le_one.trans hu)
    (Real.sqrt_nonneg _) hσ1 (blockSigma_sq c u hc hu)
    (blockSigma_mul_sqrt c u hc hu)
  have hclog : 0 ≤ c * Real.log u := mul_nonneg hc (Real.log_nonneg hu)
  have hcubic : u * blockSigma c u ^ 3 ≤ c * Real.log u * ρ := by
    rw [blockSigma_cubic c u hc hu]
    exact mul_le_mul_of_nonneg_left hσρ hclog
  calc
    u * (Real.exp (blockSigma c u) - 1 - blockSigma c u) -
        blockSigma c u * Real.sqrt (c * u * Real.log u) ≤
        -(c / 2) * Real.log u + u * blockSigma c u ^ 3 := hmain
    _ ≤ -(c / 2) * Real.log u + c * Real.log u * ρ := by
      simpa [add_comm] using add_le_add_left hcubic (-(c / 2) * Real.log u)
    _ = -(1 / 2 - ρ) * c * Real.log u := by ring

/-- The deterministic residual obtained by replacing every selector by its marginal mass. -/
noncomputable def marginalShiftResidual (b : ℕ) (delta : ℕ → ℝ)
    (M n : ℕ) : ℝ :=
  ∑' j : ℕ, (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1)

lemma summable_marginalShiftResidual_terms (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (M n : ℕ) :
    Summable (fun j : ℕ =>
      (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1)) := by
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
    (marginalDivisorMass_nonneg delta (fun m => (hdelta m).1) M _))]
  calc
    r ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) ≤
        r ^ (j + 1) * ((n + j + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
          ((marginalDivisorMass_le_card_divisors delta (fun m => (hdelta m).2) M _).trans
            (by exact_mod_cast Nat.card_divisors_le_self (n + j + 1)))
          (pow_nonneg hr0 _)
    _ = r * ((n + 1 : ℝ) * r ^ j + (j : ℝ) * r ^ j) := by
      push_cast
      rw [pow_succ]
      ring

lemma marginalShiftResidual_nonneg (b : ℕ) (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m) (M n : ℕ) :
    0 ≤ marginalShiftResidual b delta M n := by
  unfold marginalShiftResidual
  exact tsum_nonneg fun j => mul_nonneg (pow_nonneg (by positivity) _)
    (marginalDivisorMass_nonneg delta hdelta M _)

/-- Cesàro average of the deterministic residual, capped at one. -/
noncomputable def cappedMarginalResidualAverage (b : ℕ) (delta : ℕ → ℝ)
    (M N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, min 1 (marginalShiftResidual b delta M n)) / N

/-- Cesàro average of the random residual, capped at one. -/
noncomputable def cappedShiftResidualAverage {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) : ℝ :=
  (∑ n ∈ Finset.range N, min 1 (shiftResidual b X M n w)) / N

lemma cappedShiftResidualAverage_nonneg {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) :
    0 ≤ cappedShiftResidualAverage b X M N w := by
  unfold cappedShiftResidualAverage
  exact div_nonneg (Finset.sum_nonneg fun n _ =>
    le_min zero_le_one (shiftResidual_nonneg b X M n w)) (by positivity)

lemma measurable_cappedShiftResidualAverage {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (M N : ℕ) :
    Measurable (cappedShiftResidualAverage b X M N) := by
  unfold cappedShiftResidualAverage
  exact (Finset.measurable_sum _ fun n _ =>
    measurable_const.min (measurable_shiftResidual b X hX M n)).div_const _

/-- Finite approximation to the capped random residual average. -/
noncomputable def cappedShiftResidualPartialAverage {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N J : ℕ) (w : Ω) : ℝ :=
  (∑ n ∈ Finset.range N, min 1 (shiftResidualPartial b X M n J w)) / N

lemma cappedShiftResidualPartialAverage_nonneg {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N J : ℕ) (w : Ω) :
    0 ≤ cappedShiftResidualPartialAverage b X M N J w := by
  unfold cappedShiftResidualPartialAverage
  exact div_nonneg (Finset.sum_nonneg fun n _ =>
    le_min zero_le_one (shiftResidualPartial_nonneg b X M n J w)) (by positivity)

lemma measurable_cappedShiftResidualPartialAverage {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (M N J : ℕ) :
    Measurable (cappedShiftResidualPartialAverage b X M N J) := by
  unfold cappedShiftResidualPartialAverage
  exact (Finset.measurable_sum _ fun n _ =>
    measurable_const.min (measurable_shiftResidualPartial b X hX M n J)).div_const _

lemma integrable_shiftResidualPartial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : ℕ) (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n J : ℕ) :
    Integrable (shiftResidualPartial b X M n J) μ := by
  simpa using integrable_shiftResidualPartial_rpow μ b X hX M n J 1 zero_lt_one

lemma integrable_min_one_shiftResidualPartial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : ℕ) (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n J : ℕ) :
    Integrable (fun w => min 1 (shiftResidualPartial b X M n J w)) μ := by
  apply Integrable.of_bound
    (measurable_const.min (measurable_shiftResidualPartial b X hX M n J)).aestronglyMeasurable 1
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg
    (le_min zero_le_one (shiftResidualPartial_nonneg b X M n J w))]
  exact min_le_left _ _

lemma integrable_cappedShiftResidualPartialAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : ℕ) (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M N J : ℕ) :
    Integrable (cappedShiftResidualPartialAverage b X M N J) μ := by
  unfold cappedShiftResidualPartialAverage
  exact (integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_min_one_shiftResidualPartial μ b X hX M n J).div_const _

lemma integral_selectedDivisorCount_eq_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)) (M n : ℕ) :
    (∫ w, selectedDivisorCount X M n w ∂μ) = marginalDivisorMass delta M n := by
  rw [integral_selectedDivisorCount μ X hX M n]
  unfold marginalDivisorMass
  apply Finset.sum_congr rfl
  intro m hm
  rw [Measure.real, hLaw m, ENNReal.toReal_ofReal (hdelta m)]

lemma integral_shiftResidualPartial_eq_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (delta : ℕ → ℝ)
    (X : ℕ → Ω → Bool) (hdelta : ∀ m, 0 ≤ delta m)
    (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)) (M n J : ℕ) :
    (∫ w, shiftResidualPartial b X M n J w ∂μ) =
      ∑ j ∈ Finset.range J,
        (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) := by
  unfold shiftResidualPartial
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, integral_selectedDivisorCount_eq_marginal μ delta X hdelta hX hLaw]
  · intro j hj
    exact (integrable_selectedDivisorCount μ X hX M (n + j + 1)).const_mul _

lemma integral_min_one_shiftResidualPartial_le_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)) (M n J : ℕ) :
    (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤
      min 1 (marginalShiftResidual b delta M n) := by
  have hInt := integrable_shiftResidualPartial μ b X hX M n J
  have hminInt := integrable_min_one_shiftResidualPartial μ b X hX M n J
  have hleOne : (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤ 1 := by
    calc
      (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤
          ∫ _w, (1 : ℝ) ∂μ :=
        integral_mono hminInt (integrable_const _) (fun w => min_le_left _ _)
      _ = 1 := by simp
  have hlePartial : (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤
      ∫ w, shiftResidualPartial b X M n J w ∂μ :=
    integral_mono hminInt hInt (fun w => min_le_right _ _)
  have hpartial : (∫ w, shiftResidualPartial b X M n J w ∂μ) ≤
      marginalShiftResidual b delta M n := by
    rw [integral_shiftResidualPartial_eq_marginal μ b delta X (fun m => (hdelta m).1)
      hX hLaw]
    unfold marginalShiftResidual
    exact (summable_marginalShiftResidual_terms b hb delta hdelta M n).sum_le_tsum
      (Finset.range J) (fun j hj => mul_nonneg (pow_nonneg (by positivity) _)
        (marginalDivisorMass_nonneg delta (fun m => (hdelta m).1) M _))
  exact le_min hleOne (hlePartial.trans hpartial)

lemma integral_cappedShiftResidualPartialAverage_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m))
    (M N J : ℕ) :
    (∫ w, cappedShiftResidualPartialAverage b X M N J w ∂μ) ≤
      cappedMarginalResidualAverage b delta M N := by
  unfold cappedShiftResidualPartialAverage cappedMarginalResidualAverage
  rw [integral_div]
  rw [integral_finsetSum]
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun n hn =>
        integral_min_one_shiftResidualPartial_le_marginal μ b hb delta X hdelta hX hLaw M n J)
      (by positivity)
  · intro n hn
    exact integrable_min_one_shiftResidualPartial μ b X hX M n J

lemma tendsto_cappedShiftResidualPartialAverage {Ω : Type*}
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) :
    Tendsto (fun J => cappedShiftResidualPartialAverage b X M N J w) atTop
      (nhds (cappedShiftResidualAverage b X M N w)) := by
  unfold cappedShiftResidualPartialAverage cappedShiftResidualAverage
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro n hn
  exact tendsto_const_nhds.min (tendsto_shiftResidualPartial b hb X M n w)

/-- The expected capped residual average is bounded by its deterministic marginal counterpart. -/
lemma lintegral_cappedShiftResidualAverage_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m))
    (M N : ℕ) :
    (∫⁻ w, ENNReal.ofReal (cappedShiftResidualAverage b X M N w) ∂μ) ≤
      ENNReal.ofReal (cappedMarginalResidualAverage b delta M N) := by
  let f : ℕ → Ω → ENNReal := fun J w =>
    ENNReal.ofReal (cappedShiftResidualPartialAverage b X M N J w)
  let F : Ω → ENNReal := fun w =>
    ENNReal.ofReal (cappedShiftResidualAverage b X M N w)
  have hfMeas : ∀ J, Measurable (f J) := fun J =>
    (measurable_cappedShiftResidualPartialAverage b X hX M N J).ennreal_ofReal
  have hlim : ∀ w, Tendsto (fun J => f J w) atTop (nhds (F w)) := by
    intro w
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_cappedShiftResidualPartialAverage b hb X M N w)
  have hpartial : ∀ J, (∫⁻ w, f J w ∂μ) ≤
      ENNReal.ofReal (cappedMarginalResidualAverage b delta M N) := by
    intro J
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_cappedShiftResidualPartialAverage μ b X hX M N J)
      (Eventually.of_forall fun w => cappedShiftResidualPartialAverage_nonneg b X M N J w)]
    exact ENNReal.ofReal_le_ofReal
      (integral_cappedShiftResidualPartialAverage_le μ b hb delta X hdelta hX hLaw M N J)
  have hfatou := lintegral_liminf_le hfMeas (μ := μ) (u := atTop)
  have hpoint : (fun w => liminf (fun J => f J w) atTop) = F := by
    funext w
    exact (hlim w).liminf_eq
  rw [hpoint] at hfatou
  exact hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hpartial))

lemma orbitAverage_le_cappedShiftResidualAverage {Ω : Type*}
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) :
    (∑ n ∈ Finset.range N, NormalNumbers.orbit b (ebLambertTail b X M w) n) / N ≤
      cappedShiftResidualAverage b X M N w := by
  unfold cappedShiftResidualAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro n hn
  have hfract : NormalNumbers.orbit b (ebLambertTail b X M w) n ≤
      shiftResidual b X M n w := by
    simpa only [NormalNumbers.orbit, mul_comm] using
      fract_pow_mul_ebLambertTail_le_shiftResidual b hb X M n w
  exact le_min (Int.fract_lt_one _).le hfract

/-- A normal deleted-head orbit forces a positive capped residual average. -/
lemma isNormal_eventually_cappedShiftResidualAverage_ge {Ω : Type*}
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (M : ℕ) (w : Ω)
    (hnormal : NormalNumbers.IsNormal b (ebLambertTail b X M w)) :
    ∀ᶠ N : ℕ in atTop,
      normalMomentThreshold 1 ≤ cappedShiftResidualAverage b X M N w := by
  let u : ℕ → ℝ := NormalNumbers.orbit b (ebLambertTail b X M w)
  have hequid : NormalNumbers.Equidistributed u := by
    exact (NormalNumbers.isNormal_iff_equidistributed_orbit b hb _).mp hnormal
  have htend : Tendsto
      (fun N => (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) / N)
      atTop (nhds (1 / 2 : ℝ)) := by
    have h := hequid (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hvisit : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) ≤ (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) / N :=
    (htend.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))).mono
      fun N hN => hN.le
  filter_upwards [hvisit, eventually_ge_atTop 1] with N hfreq hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlower : (1 / 2 : ℝ) * (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) ≤
      ∑ n ∈ Finset.range N, u n := by
    calc
      (1 / 2 : ℝ) * (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) =
          ∑ n ∈ (Finset.range N).filter (fun n => u n ∈ Set.Ico (1 / 2) 1), (1 / 2 : ℝ) := by
        unfold NormalNumbers.visitCount
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ n ∈ (Finset.range N).filter (fun n => u n ∈ Set.Ico (1 / 2) 1), u n := by
        apply Finset.sum_le_sum
        intro n hn
        exact (Finset.mem_filter.mp hn).2.1
      _ ≤ ∑ n ∈ Finset.range N, u n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n hn hnot
        exact Int.fract_nonneg _
  calc
    normalMomentThreshold 1 = (1 / 2 : ℝ) * (1 / 4) := by
      norm_num [normalMomentThreshold]
    _ ≤ (1 / 2 : ℝ) *
        ((NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) / N) :=
      mul_le_mul_of_nonneg_left hfreq (by norm_num)
    _ = ((1 / 2 : ℝ) * (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ)) / N := by ring
    _ ≤ (∑ n ∈ Finset.range N, u n) / N :=
      div_le_div_of_nonneg_right hlower hNpos.le
    _ ≤ cappedShiftResidualAverage b X M N w := by
      exact orbitAverage_le_cappedShiftResidualAverage b hb X M N w

/-- Uniform expectation control bounds the measure of the eventual positive capped-residual event. -/
lemma measure_eventually_cappedShiftResidualAverage_ge_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m))
    (M : ℕ) (ε R : ℝ) (hε : 0 < ε)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      (∫⁻ w, ENNReal.ofReal (cappedShiftResidualAverage b X M N w) ∂μ) ≤
        ENNReal.ofReal R) :
    μ {w | ∀ᶠ N : ℕ in atTop,
      ε ≤ cappedShiftResidualAverage b X M N w} ≤ ENNReal.ofReal (R / ε) := by
  let E : ℕ → Set Ω := fun N => {w | ε ≤ cappedShiftResidualAverage b X M N w}
  let T : ℕ → Set Ω := fun K => {w | ∀ N, K ≤ N → w ∈ E N}
  have hE : ∀ N : ℕ, 1 ≤ N → μ (E N) ≤ ENNReal.ofReal (R / ε) := by
    intro N hN
    have hset : {w | ENNReal.ofReal ε ≤
        ENNReal.ofReal (cappedShiftResidualAverage b X M N w)} = E N := by
      ext w
      simp only [E, Set.mem_setOf_eq]
      exact ENNReal.ofReal_le_ofReal_iff (cappedShiftResidualAverage_nonneg b X M N w)
    have hmarkov := mul_meas_ge_le_lintegral
      ((measurable_cappedShiftResidualAverage b X hX M N).ennreal_ofReal)
      (ENNReal.ofReal ε) (μ := μ)
    rw [hset] at hmarkov
    rw [ENNReal.ofReal_div_of_pos hε]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hε)))
      (Or.inl ENNReal.ofReal_ne_top)).2
    rw [mul_comm]
    exact hmarkov.trans (hbound N hN)
  have hTmono : Monotone T := by
    intro K L hKL w hw N hLN
    exact hw N (hKL.trans hLN)
  have hT : ∀ K, μ (T K) ≤ ENNReal.ofReal (R / ε) := by
    intro K
    calc
      μ (T K) ≤ μ (E (max K 1)) := by
        apply measure_mono
        intro w hw
        exact hw (max K 1) (le_max_left K 1)
      _ ≤ ENNReal.ofReal (R / ε) := hE (max K 1) (le_max_right K 1)
  have hunion : μ (⋃ K, T K) ≤ ENNReal.ofReal (R / ε) := by
    rw [hTmono.measure_iUnion]
    exact iSup_le hT
  have heq : {w | ∀ᶠ N : ℕ in atTop,
      ε ≤ cappedShiftResidualAverage b X M N w} = ⋃ K, T K := by
    ext w
    constructor
    · intro hw
      obtain ⟨K, hK⟩ := eventually_atTop.1 hw
      exact Set.mem_iUnion.2 ⟨K, hK⟩
    · intro hw
      obtain ⟨K, hK⟩ := Set.mem_iUnion.1 hw
      exact eventually_atTop.2 ⟨K, hK⟩
  rw [heq]
  exact hunion

/-- Marginal-only capped-residual criterion for random Erdős--Borwein non-normality. -/
theorem ae_not_normal_of_capped_marginal_residual
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (htail : ∀ b : ℕ, 2 ≤ b → ∀ η : ℝ, 0 < η →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
        cappedMarginalResidualAverage b delta M N ≤ η) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  classical
  obtain ⟨hdelta, hMeas, -, hLaw⟩ := hX
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · have hbase : ∀ᵐ w ∂μ, ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
      rw [ae_iff]
      simp only [not_not]
      let A : Set Ω := {w | NormalNumbers.IsNormal b (ebLambert b X w)}
      change μ A = 0
      by_contra hA0
      have hAtop : μ A ≠ ⊤ := measure_ne_top μ A
      let p : ℝ := (μ A).toReal
      have hp : 0 < p := ENNReal.toReal_pos hA0 hAtop
      let ε : ℝ := normalMomentThreshold 1
      have hε : 0 < ε := normalMomentThreshold_pos 1
      let η : ℝ := p * ε / 2
      have hη : 0 < η := by dsimp [η]; positivity
      obtain ⟨M, hM, htailM⟩ := htail b hb η hη
      have hlintegral : ∀ N : ℕ, 1 ≤ N →
          (∫⁻ w, ENNReal.ofReal (cappedShiftResidualAverage b X M N w) ∂μ) ≤
            ENNReal.ofReal η := by
        intro N hN
        exact (lintegral_cappedShiftResidualAverage_le μ b hb delta X hdelta hMeas hLaw M N).trans
          (ENNReal.ofReal_le_ofReal (htailM N hN))
      let E : Set Ω := {w | ∀ᶠ N : ℕ in atTop,
        ε ≤ cappedShiftResidualAverage b X M N w}
      have hE : μ E ≤ ENNReal.ofReal (η / ε) := by
        exact measure_eventually_cappedShiftResidualAverage_ge_le μ b X hMeas M ε η hε
          hlintegral
      have hsub : A ⊆ E := by
        intro w hw
        have hnormal := ebLambertTail_isNormal_of_ebLambert b hb X M w hw
        exact isNormal_eventually_cappedShiftResidualAverage_ge b hb X M w hnormal
      have hmeasure : μ A ≤ ENNReal.ofReal (η / ε) := (measure_mono hsub).trans hE
      have hp_le : p ≤ η / ε := by
        dsimp [p]
        exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hη.le hε.le) hmeasure
      have hhalf : η / ε = p / 2 := by
        dsimp [η]
        field_simp
      rw [hhalf] at hp_le
      linarith
    filter_upwards [hbase] with w hw
    exact fun _ => hw
  · exact ae_of_all μ fun w hb' => (hb hb').elim

end NormalNumbers.ErdosBorweinSubpower
