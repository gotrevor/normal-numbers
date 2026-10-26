/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinSubpower
import NormalNumbers.CoefmassErdosBorweinSubpowerKubAux

/-!
# Non-normality below the sub-power weight for every `c > 1`, given `KubiliusTV`
(personal-c5, 2026-10-25)

All definitions and the headline are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never
edit them.  `KubiliusTV` is a named literature hypothesis: never prove, weaken or axiomatize it.  The
same three definitions live in the sibling branch `~/src/nn-eb-endpoint`
(`CoefmassErdosBorweinEndpointKub.lean`); that file's model lemmas are a reference to adapt.  The
paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Non-normal for c > 1 given
KubiliusTV"; the plan is in `EB-SUBPOWER-KUB-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinSubpowerKub

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinRandom NormalNumbers.ErdosBorweinSubpower

/-- The primes `≤ y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

theorem primesUpTo_eq_primesLE (y : ℕ) : primesUpTo y = y.primesLE := rfl

open Classical in
/-- Mass of `A` under the Kubilius model: each prime `p ≤ y` is included independently with
probability `1/p`. -/
noncomputable def kubiliusMass (y : ℕ) (A : Set (Finset ℕ)) : ℝ :=
  ∑ S ∈ (primesUpTo y).powerset,
    if S ∈ A then ∏ p ∈ primesUpTo y, (if p ∈ S then (1 / p : ℝ) else 1 - 1 / p) else 0

open Classical in
/-- Literature input: the Kubilius-model total-variation bound (Tenenbaum 1999, Théorème 1.1 and
(1.7), as quoted by Ford, arXiv 2408.03803v4, Theorem A), at `ε = 1/2`, projected to divisibility
indicators.  A named hypothesis, not an axiom. -/
def KubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 2 ≤ y → y ≤ N → ∀ A : Set (Finset ℕ),
    |(((Finset.Icc 1 N).filter (fun n => n.primeFactors.filter (· ≤ y) ∈ A)).card : ℝ) / N -
        kubiliusMass y A| ≤
      C * (Real.rpow (Real.log N / Real.log y) (-(Real.log N / Real.log y)) +
        Real.rpow N (-(1 / 2 : ℝ)))

open Classical in
/-- The packet's Kubilius mass is the finite Bernoulli subset model used by the maximal
inequality. -/
theorem kubiliusMass_eq_bernoulliSubsetMass (y : ℕ) (A : Set (Finset ℕ)) :
    kubiliusMass y A =
      bernoulliSubsetMass (primesUpTo y) (fun p ↦ (1 / p : ℝ)) A := rfl

theorem kubiliusParameter_nonneg (y p : ℕ) (_hp : p ∈ primesUpTo y) :
    (0 : ℝ) ≤ 1 / p := by positivity

theorem kubiliusParameter_le_one (y p : ℕ) (hp : p ∈ primesUpTo y) :
    (1 / p : ℝ) ≤ 1 := by
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  exact (div_le_one (by positivity)).mpr hpR

open Classical in
/-- Doob's exponential maximal inequality in the packet's Kubilius model.  The primes are exposed
in increasing order, and the empty prefix is included in `centeredBernoulliHit`. -/
theorem kubiliusMass_centeredBernoulliHit_le_exp (y : ℕ) (θ h : ℝ) (hθ : 0 ≤ θ) :
    kubiliusMass y
        {S | centeredBernoulliHit (fun p : ℕ ↦ (1 / p : ℝ)) h 0
          ((primesUpTo y).sort (· ≤ ·)) S} ≤
      Real.exp ((Real.exp θ - 1 - θ) *
        ∑ p ∈ primesUpTo y, (1 / p : ℝ) - θ * h) := by
  rw [kubiliusMass_eq_bernoulliSubsetMass]
  have hmax := bernoulliSubsetMass_centeredBernoulliHit_le_exp
    ((primesUpTo y).sort (· ≤ ·)) ((primesUpTo y).sort_nodup (· ≤ ·))
    (fun p ↦ (1 / p : ℝ))
    (fun p hp ↦ kubiliusParameter_nonneg y p
      ((Finset.mem_sort (· ≤ ·)).mp hp))
    (fun p hp ↦ kubiliusParameter_le_one y p
      ((Finset.mem_sort (· ≤ ·)).mp hp)) θ h hθ
  simpa only [Finset.sort_toFinset] using hmax

open Classical in
/-- Prefix-sum form of the finite Kubilius maximal inequality. -/
theorem kubiliusMass_exists_centeredPrefixSum_ge_le_exp (y : ℕ) (θ h : ℝ) (hθ : 0 ≤ θ) :
    kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k} ≤
      Real.exp ((Real.exp θ - 1 - θ) *
        ∑ p ∈ primesUpTo y, (1 / p : ℝ) - θ * h) := by
  simpa only [zero_add, centeredBernoulliHit_iff_exists_prefix] using
    kubiliusMass_centeredBernoulliHit_le_exp y θ h hθ

open Classical in
/-- Mertens specialization of the finite Kubilius maximal inequality. -/
theorem kubiliusMass_centeredBernoulliHit_le_exp_mertens
    (y : ℕ) (hy : 2 ≤ y) (θ h : ℝ) (hθ : 0 ≤ θ) :
    kubiliusMass y
        {S | centeredBernoulliHit (fun p : ℕ ↦ (1 / p : ℝ)) h 0
          ((primesUpTo y).sort (· ≤ ·)) S} ≤
      Real.exp ((Real.exp θ - 1 - θ) *
        (Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound) - θ * h) := by
  have hprime : (∑ p ∈ primesUpTo y, (1 / p : ℝ)) ≤
      Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound := by
    simpa only [primesUpTo_eq_primesLE] using primeReciprocalMass_le_log_log_add y hy
  have hcoef : 0 ≤ Real.exp θ - 1 - θ := by
    linarith [Real.add_one_le_exp θ]
  refine (kubiliusMass_centeredBernoulliHit_le_exp y θ h hθ).trans ?_
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hprime hcoef) (θ * h)

open Classical in
/-- Cubic-MGF form used on each geometric block of log-log prime cutoffs. -/
theorem kubiliusMass_exists_centeredPrefixSum_ge_le_exp_cubic
    (y : ℕ) (hy : 2 ≤ y) (θ h : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k} ≤
      Real.exp ((θ ^ 2 / 2 + θ ^ 3) *
        (Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound) - θ * h) := by
  have hprime : (∑ p ∈ primesUpTo y, (1 / p : ℝ)) ≤
      Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound := by
    simpa only [primesUpTo_eq_primesLE] using primeReciprocalMass_le_log_log_add y hy
  have hsum0 : 0 ≤ ∑ p ∈ primesUpTo y, (1 / p : ℝ) := by positivity
  have hcoef := exp_sub_one_sub_id_le_half_sq_add_cube hθ0 hθ1
  have hcubic0 : 0 ≤ θ ^ 2 / 2 + θ ^ 3 := by positivity
  have hmul : (Real.exp θ - 1 - θ) * ∑ p ∈ primesUpTo y, (1 / p : ℝ) ≤
      (θ ^ 2 / 2 + θ ^ 3) *
        (Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound) :=
    mul_le_mul hcoef hprime hsum0 hcubic0
  have hmax := kubiliusMass_exists_centeredPrefixSum_ge_le_exp y θ h hθ0
  refine hmax.trans ?_
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right hmul (θ * h)

open Classical in
/-- The cubic maximal inequality optimized at `θ = h / U`.  Here `U` is any upper bound for
the Mertens variance at the terminal prime cutoff.  The extra parameter `x` is the auxiliary
threshold that will subsequently be summed geometrically. -/
theorem kubiliusMass_exists_centeredPrefixSum_ge_add_le_exp_optimized
    (y : ℕ) (hy : 2 ≤ y) (h U x : ℝ) (hh : 0 ≤ h) (hU : 0 < U)
    (hhU : h ≤ U) (_hx : 0 ≤ x)
    (hvar : Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤ U) :
    kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h + x ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k} ≤
      Real.exp (-h ^ 2 / (2 * U) + h ^ 3 / U ^ 2 - h * x / U) := by
  have hθ0 : 0 ≤ h / U := div_nonneg hh hU.le
  have hθ1 : h / U ≤ 1 := (div_le_one hU).2 hhU
  have hcoef : 0 ≤ (h / U) ^ 2 / 2 + (h / U) ^ 3 := by positivity
  have hmax := kubiliusMass_exists_centeredPrefixSum_ge_le_exp_cubic
    y hy (h / U) (h + x) hθ0 hθ1
  refine hmax.trans ?_
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hvar hcoef
  calc
    ((h / U) ^ 2 / 2 + (h / U) ^ 3) *
          (Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound) -
        h / U * (h + x) ≤
      ((h / U) ^ 2 / 2 + (h / U) ^ 3) * U - h / U * (h + x) :=
        sub_le_sub_right hmul _
    _ = -h ^ 2 / (2 * U) + h ^ 3 / U ^ 2 - h * x / U := by
      field_simp [ne_of_gt hU]
      ring

/-- The optimized exponential tails have an exact geometric sum. -/
theorem hasSum_kubiliusOptimizedTail (E h U : ℝ) (hh : 0 < h) (hU : 0 < U) :
    HasSum (fun j : ℕ ↦ Real.exp (E - h * (j : ℝ) / U))
      (Real.exp E * (1 - Real.exp (-h / U))⁻¹) := by
  have hratio0 : 0 ≤ Real.exp (-h / U) := (Real.exp_pos _).le
  have hratio1 : Real.exp (-h / U) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hh) hU
  have hgeom := (hasSum_geometric_of_lt_one hratio0 hratio1).mul_left (Real.exp E)
  have hfun : (fun j : ℕ ↦ Real.exp (E - h * (j : ℝ) / U)) =
      fun j : ℕ ↦ Real.exp E * Real.exp (-h / U) ^ j := by
    funext j
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  exact hgeom

/-- Summing the auxiliary thresholds costs at most `2U/h`, provided the optimizing parameter is
at most `1/2`.  This is the discrete counterpart of integrating the exponential maximal tail. -/
theorem tsum_kubiliusOptimizedTail_le (E h U : ℝ) (hh : 0 < h) (hU : 0 < U)
    (hhU : 2 * h ≤ U) :
    (∑' j : ℕ, Real.exp (E - h * (j : ℝ) / U)) ≤
      Real.exp E * (2 * U / h) := by
  rw [(hasSum_kubiliusOptimizedTail E h U hh hU).tsum_eq]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hσ0 : 0 < 2 * h / U := div_pos (mul_pos (by norm_num) hh) hU
  have hσ1 : 2 * h / U ≤ 1 := (div_le_one hU).2 hhU
  have hinv := one_sub_exp_neg_half_inv_le (2 * h / U) hσ0 hσ1
  have hexp : -(2 * h / U) / 2 = -h / U := by ring
  rw [hexp] at hinv
  calc
    (1 - Real.exp (-h / U))⁻¹ ≤ 4 / (2 * h / U) := hinv
    _ = 2 * U / h := by
      field_simp [ne_of_gt hh, ne_of_gt hU]
      ring

open Classical in
/-- One geometric log-log block, already summed over every auxiliary integer threshold.  This is
the model-side estimate used before the `KubiliusTV` transfer. -/
theorem sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_optimized
    (y : ℕ) (hy : 2 ≤ y) (h U : ℝ) (hh : 0 < h) (hU : 0 < U)
    (hhU : 2 * h ≤ U)
    (hvar : Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤ U)
    (J : ℕ) :
    (∑ j ∈ Finset.range J, kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h + j ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k}) ≤
      Real.exp (-h ^ 2 / (2 * U) + h ^ 3 / U ^ 2) * (2 * U / h) := by
  let E : ℝ := -h ^ 2 / (2 * U) + h ^ 3 / U ^ 2
  have hhU' : h ≤ U := by linarith
  have hterm : ∀ j : ℕ,
      kubiliusMass y
          {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
            h + j ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
              ((primesUpTo y).sort (· ≤ ·)) k} ≤
        Real.exp (E - h * (j : ℝ) / U) := by
    intro j
    exact kubiliusMass_exists_centeredPrefixSum_ge_add_le_exp_optimized
      y hy h U j hh.le hU hhU' (by positivity) hvar
  have hsum := (hasSum_kubiliusOptimizedTail E h U hh hU).summable
  calc
    (∑ j ∈ Finset.range J, kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h + j ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k}) ≤
        ∑ j ∈ Finset.range J, Real.exp (E - h * (j : ℝ) / U) := by
      exact Finset.sum_le_sum fun j _ ↦ hterm j
    _ ≤ ∑' j : ℕ, Real.exp (E - h * (j : ℝ) / U) :=
      hsum.sum_le_tsum (Finset.range J) (fun j _ ↦ (Real.exp_pos _).le)
    _ ≤ Real.exp E * (2 * U / h) :=
      tsum_kubiliusOptimizedTail_le E h U hh hU hhU

/-! ### Geometric log-log blocks -/

/-- The geometric block ratio chosen strictly between `1` and `c`. -/
noncomputable def kubiliusBlockRatio (c : ℝ) : ℝ := (1 + c) / 2

/-- Exponent left after integrating the maximal tail across one geometric block. -/
noncomputable def kubiliusGeometricDecayExponent (c : ℝ) : ℝ :=
  1 / 2 - c / (2 * kubiliusBlockRatio c)

theorem one_lt_kubiliusBlockRatio {c : ℝ} (hc : 1 < c) :
    1 < kubiliusBlockRatio c := by
  unfold kubiliusBlockRatio
  linarith

theorem kubiliusBlockRatio_lt {c : ℝ} (hc : 1 < c) :
    kubiliusBlockRatio c < c := by
  unfold kubiliusBlockRatio
  linarith

theorem kubiliusGeometricDecayExponent_neg {c : ℝ} (hc : 1 < c) :
    kubiliusGeometricDecayExponent c < 0 := by
  have hr0 : 0 < 2 * kubiliusBlockRatio c := by
    positivity [one_lt_kubiliusBlockRatio hc]
  rw [kubiliusGeometricDecayExponent]
  apply sub_neg.mpr
  apply (lt_div_iff₀ hr0).2
  nlinarith [kubiliusBlockRatio_lt hc]

/-- Exact exponent produced by the optimized maximal inequality at the ideal barrier
`h = u * blockSigma c u` and variance cap `U = r*u`. -/
theorem kubiliusOptimizedExponent_eq (c r u : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (hu : 1 ≤ u) :
    -(u * blockSigma c u) ^ 2 / (2 * (r * u)) +
        (u * blockSigma c u) ^ 3 / (r * u) ^ 2 =
      (-c / (2 * r) + c * blockSigma c u / r ^ 2) * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hsq := blockSigma_sq c u hc hu
  have hcub := blockSigma_cubic c u hc hu
  calc
    -(u * blockSigma c u) ^ 2 / (2 * (r * u)) +
          (u * blockSigma c u) ^ 3 / (r * u) ^ 2 =
        -(u * blockSigma c u ^ 2) / (2 * r) +
          (u * blockSigma c u ^ 3) / r ^ 2 := by
            field_simp [ne_of_gt hr, ne_of_gt hu0]
    _ = (-c / (2 * r) + c * blockSigma c u / r ^ 2) * Real.log u := by
      rw [hsq, hcub]
      ring

/-- The cubic MGF correction is eventually absorbed by half of the strict gap `r < c`.
Consequently the optimized exponent has coefficient `-(c+r)/(4r)` in front of `log u`. -/
theorem eventually_kubiliusOptimizedExponent_le
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (hrc : r < c) :
    ∀ᶠ u : ℝ in atTop, 1 ≤ u ∧
      -(u * blockSigma c u) ^ 2 / (2 * (r * u)) +
          (u * blockSigma c u) ^ 3 / (r * u) ^ 2 ≤
        (-(c + r) / (4 * r)) * Real.log u := by
  have hgap : 0 < (c - r) * r / (4 * c) := by positivity
  have hsigma : ∀ᶠ u : ℝ in atTop,
      blockSigma c u < (c - r) * r / (4 * c) :=
    (tendsto_blockSigma_atTop_zero c).eventually_lt_const hgap
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsigma] with u hu hsigma
  refine ⟨hu, ?_⟩
  have hcorrection : c * blockSigma c u / r ^ 2 ≤ (c - r) / (4 * r) := by
    apply le_of_lt
    calc
      c * blockSigma c u / r ^ 2 <
          c * ((c - r) * r / (4 * c)) / r ^ 2 := by gcongr
      _ = (c - r) / (4 * r) := by
        field_simp [ne_of_gt hc, ne_of_gt hr]
  rw [kubiliusOptimizedExponent_eq c r u hc.le hr hu]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hu)
  calc
    -c / (2 * r) + c * blockSigma c u / r ^ 2 ≤
        -c / (2 * r) + (c - r) / (4 * r) := by gcongr
    _ = -(c + r) / (4 * r) := by
      field_simp [ne_of_gt hr]
      ring

/-- The geometric-block majorant is summable for every `c > 1`; this is the exact place where
choosing a ratio strictly below `c` reaches the heuristic threshold. -/
theorem summable_kubiliusGeometricDecay {c : ℝ} (hc : 1 < c) :
    Summable (fun k : ℕ ↦ Real.rpow (kubiliusBlockRatio c)
      (kubiliusGeometricDecayExponent c * (k : ℝ))) := by
  have hr : 1 < kubiliusBlockRatio c := one_lt_kubiliusBlockRatio hc
  have he : kubiliusGeometricDecayExponent c < 0 :=
    kubiliusGeometricDecayExponent_neg hc
  have hqpos : 0 < Real.rpow (kubiliusBlockRatio c)
      (kubiliusGeometricDecayExponent c) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hr) _
  have hqnorm : ‖Real.rpow (kubiliusBlockRatio c)
      (kubiliusGeometricDecayExponent c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hr he
  have hsum := summable_geometric_of_norm_lt_one hqnorm
  have hfun : (fun k : ℕ ↦ Real.rpow (kubiliusBlockRatio c)
      (kubiliusGeometricDecayExponent c * (k : ℝ))) =
      fun k : ℕ ↦ Real.rpow (kubiliusBlockRatio c)
        (kubiliusGeometricDecayExponent c) ^ k := by
    funext k
    exact Real.rpow_mul_natCast (zero_lt_one.trans hr).le _ k
  rw [hfun]
  exact hsum

/-- **Target: non-normal below the sub-power weight for every `c > 1`, given `KubiliusTV`.**  This
reaches the heuristic threshold of `EBLogWindow`'s non-normal half.  The proof replaces the c > 3
block-union step of `ebRandom_ae_not_normal_subpower` by Doob's exponential maximal inequality on
geometric level-blocks of ratio `r ∈ (1, c)`, in the Kubilius model.  It transfers through
`KubiliusTV` at `y₀ = T^{1/log L_T}`, truncated at `4L_T` thresholds.  Draft: "Non-normal for c > 1
given KubiliusTV".  Confidence 80%. -/
theorem ebRandom_ae_not_normal_subpower_of_kubilius (hK : KubiliusTV)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c C : ℝ) (hc : 1 < c)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinSubpowerKub
