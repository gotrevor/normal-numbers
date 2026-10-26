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
