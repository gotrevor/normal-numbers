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
/-- For nested prime cutoffs, the smaller cutoff is literally the initial segment of the larger
cutoff's increasing prime list.  This supplies the time index needed to map an arithmetic cutoff
into the ordered Kubilius walk. -/
theorem primesUpTo_sort_take_card {a y : ℕ} (hay : a ≤ y) :
    (((primesUpTo y).sort (· ≤ ·)).take (primesUpTo a).card).toFinset = primesUpTo a := by
  let A := primesUpTo a
  let Y := primesUpTo y
  let D := Y \ A
  have hAY : A ⊆ Y := by
    intro p hp
    simp only [A, Y, primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hnodup : (A.sort (· ≤ ·) ++ D.sort (· ≤ ·)).Nodup := by
    rw [List.nodup_append]
    refine ⟨A.sort_nodup (· ≤ ·), D.sort_nodup (· ≤ ·), ?_⟩
    intro p hp q hq hpq
    have hpA : p ∈ A := (Finset.mem_sort (· ≤ ·)).mp hp
    have hqD : q ∈ D := (Finset.mem_sort (· ≤ ·)).mp hq
    subst q
    exact (Finset.mem_sdiff.mp hqD).2 hpA
  have hpairwise : (A.sort (· ≤ ·) ++ D.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨A.pairwise_sort (· ≤ ·), D.pairwise_sort (· ≤ ·), ?_⟩
    intro p hp q hq
    have hpA : p ∈ A := (Finset.mem_sort (· ≤ ·)).mp hp
    have hqD : q ∈ D := (Finset.mem_sort (· ≤ ·)).mp hq
    have hpa : p ≤ a := by
      have hpA' := hpA
      simp only [A, primesUpTo, Finset.mem_filter, Finset.mem_range,
        Nat.lt_add_one_iff] at hpA'
      exact hpA'.1
    have hqa : a < q := by
      have hqY : q ∈ Y := (Finset.mem_sdiff.mp hqD).1
      have hqprime : q.Prime := by
        have hqY' := hqY
        simp only [Y, primesUpTo, Finset.mem_filter, Finset.mem_range,
          Nat.lt_add_one_iff] at hqY'
        exact hqY'.2
      have hqnotA : q ∉ A := (Finset.mem_sdiff.mp hqD).2
      simp only [A, primesUpTo, Finset.mem_filter, Finset.mem_range,
        Nat.lt_add_one_iff, hqprime, and_true] at hqnotA
      omega
    omega
  have hsort : Y.sort (· ≤ ·) = A.sort (· ≤ ·) ++ D.sort (· ≤ ·) := by
    have h := (List.toFinset_sort (· ≤ ·) hnodup).2 hpairwise
    have hunion : A ∪ D = Y := by
      simpa only [D] using Finset.union_sdiff_of_subset hAY
    simpa only [List.toFinset_append, Finset.sort_toFinset, hunion] using h
  change ((Y.sort (· ≤ ·)).take A.card).toFinset = A
  rw [hsort, show A.card = (A.sort (· ≤ ·)).length by simp]
  simp

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
/-- The finite Kubilius mass is monotone in its event. -/
theorem kubiliusMass_mono (y : ℕ) {A B : Set (Finset ℕ)} (hAB : A ⊆ B) :
    kubiliusMass y A ≤ kubiliusMass y B := by
  unfold kubiliusMass
  apply Finset.sum_le_sum
  intro S hS
  by_cases hSA : S ∈ A
  · simp only [hSA, hAB hSA, if_true]
    exact le_rfl
  · simp only [hSA, if_false]
    by_cases hSB : S ∈ B
    · simp only [hSB, if_true]
      apply Finset.prod_nonneg
      intro p hp
      by_cases hpS : p ∈ S
      · simp only [hpS, if_true]
        exact kubiliusParameter_nonneg y p hp
      · simp only [hpS, if_false]
        exact sub_nonneg.mpr (kubiliusParameter_le_one y p hp)
    · simp only [hSB, if_false]
      exact le_rfl

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

open Classical in
/-- A larger, lowered threshold inherits the optimized block estimate from any smaller ideal
threshold.  This isolates the deterministic barrier comparison from the probabilistic maximal
inequality. -/
theorem sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_of_le
    (y : ℕ) (hy : 2 ≤ y) (h₀ h U : ℝ) (hh₀ : 0 < h₀) (hU : 0 < U)
    (hh₀U : 2 * h₀ ≤ U)
    (hvar : Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤ U)
    (h₀h : h₀ ≤ h) (J : ℕ) :
    (∑ j ∈ Finset.range J, kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h + j ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k}) ≤
      Real.exp (-h₀ ^ 2 / (2 * U) + h₀ ^ 3 / U ^ 2) * (2 * U / h₀) := by
  refine le_trans (Finset.sum_le_sum fun j _ ↦ kubiliusMass_mono y ?_)
    (sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_optimized
      y hy h₀ U hh₀ hU hh₀U hvar J)
  intro S hS
  rcases hS with ⟨k, hk, hcross⟩
  refine ⟨k, hk, ?_⟩
  exact le_trans (by linarith) hcross

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

/-! ### Lowered barriers -/

/-- The barrier left after paying logarithmic and bounded deterministic losses.  In the
application, `A * log u` absorbs the squarefull/divisor and block-location costs, while `B`
absorbs fixed constants. -/
noncomputable def kubiliusLoweredBarrier (c A B u : ℝ) : ℝ :=
  u * blockSigma c u - A * Real.log u - B

/-- Changing the coefficient inside the ideal square-root barrier only changes `blockSigma` by
the corresponding constant square-root factor. -/
theorem blockSigma_eq_sqrt_ratio_mul (c₀ c u : ℝ) (hc₀ : 0 ≤ c₀) (hc : 0 < c) :
    blockSigma c₀ u = Real.sqrt (c₀ / c) * blockSigma c u := by
  unfold blockSigma
  rw [← Real.sqrt_mul (div_nonneg hc₀ hc.le)]
  congr 1
  field_simp [ne_of_gt hc]

/-- Every fixed logarithmic-plus-constant loss is eventually smaller than the gap between the
ideal barriers with coefficients `c₀ < c`.  This is the deterministic comparison needed to
replace the actual lowered barrier by an ideal barrier before applying the optimized maximal
inequality. -/
theorem eventually_idealBarrier_le_kubiliusLoweredBarrier
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : 0 < c) (hc₀c : c₀ < c)
    (A B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ u : ℝ in atTop,
      u * blockSigma c₀ u ≤ kubiliusLoweredBarrier c A B u := by
  let q : ℝ := Real.sqrt (c₀ / c)
  have hratio1 : c₀ / c < 1 := (div_lt_one hc).2 hc₀c
  have hq1 : q < 1 := (Real.sqrt_lt' zero_lt_one).2 (by simpa using hratio1)
  have hgap : 0 < 1 - q := sub_pos.mpr hq1
  have hsmall : ∀ᶠ u : ℝ in atTop,
      (A + B) / c * blockSigma c u < 1 - q := by
    have ht : Tendsto (fun u : ℝ ↦ (A + B) / c * blockSigma c u) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_blockSigma_atTop_zero c)
    exact ht.eventually_lt_const hgap
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1)] with u hsmall hlog hu
  have hu1 : 1 ≤ u := by linarith [Real.exp_one_gt_two]
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hσ0 : 0 ≤ blockSigma c u := Real.sqrt_nonneg _
  have hloss : A * Real.log u + B ≤ (1 - q) * (u * blockSigma c u) := by
    have hBlog : B ≤ B * Real.log u := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hB]
    have hAB : A * Real.log u + B ≤ (A + B) * Real.log u := by
      nlinarith
    have hcoef :
        u * blockSigma c u * ((A + B) / c * blockSigma c u) ≤
          u * blockSigma c u * (1 - q) :=
      mul_le_mul_of_nonneg_left hsmall.le (mul_nonneg hu0.le hσ0)
    have hrewrite :
        u * blockSigma c u * ((A + B) / c * blockSigma c u) =
          (A + B) * Real.log u := by
      rw [show u * blockSigma c u * ((A + B) / c * blockSigma c u) =
          (A + B) / c * (u * blockSigma c u ^ 2) by ring,
        blockSigma_sq c u hc.le hu1]
      field_simp [ne_of_gt hc]
    rw [hrewrite] at hcoef
    exact hAB.trans (by simpa [mul_comm] using hcoef)
  rw [kubiliusLoweredBarrier, blockSigma_eq_sqrt_ratio_mul c₀ c u hc₀.le hc]
  change u * (q * blockSigma c u) ≤
    u * blockSigma c u - A * Real.log u - B
  nlinarith

/-- Eventual side conditions for the lowered-barrier maximal estimate.  Besides comparison with
an inner ideal barrier, the lowered barrier is positive and is at most half of the variance cap
`r*u`; the latter supplies both `h ≤ U` and the geometric-threshold summation hypothesis. -/
theorem eventually_kubiliusLoweredBarrier_conditions
    {c₀ c r : ℝ} (hc₀ : 0 < c₀) (hc : 0 < c) (hc₀c : c₀ < c) (hr : 0 < r)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ u : ℝ in atTop,
      u * blockSigma c₀ u ≤ kubiliusLoweredBarrier c A B u ∧
      0 < kubiliusLoweredBarrier c A B u ∧
      2 * kubiliusLoweredBarrier c A B u ≤ r * u ∧
      kubiliusLoweredBarrier c A B u ≤ u * blockSigma c u := by
  have hinner := eventually_idealBarrier_le_kubiliusLoweredBarrier
    hc₀ hc hc₀c A B hB
  have hsmall : ∀ᶠ u : ℝ in atTop, 2 * blockSigma c u < r := by
    have ht : Tendsto (fun u : ℝ ↦ 2 * blockSigma c u) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_blockSigma_atTop_zero c)
    exact ht.eventually_lt_const hr
  filter_upwards [hinner, hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 0,
    eventually_ge_atTop (Real.exp 1)] with u hinner hsmall hlog hu
  have hu1 : 1 ≤ u := by linarith [Real.exp_one_gt_two]
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hu_gt : 1 < u :=
    (by norm_num : (1 : ℝ) < 2).trans (Real.exp_one_gt_two.trans_le hu)
  have hinnerpos : 0 < u * blockSigma c₀ u := by
    apply mul_pos hu0
    unfold blockSigma
    exact Real.sqrt_pos.mpr (div_pos (mul_pos hc₀ (Real.log_pos hu_gt)) hu0)
  have hlower : kubiliusLoweredBarrier c A B u ≤ u * blockSigma c u := by
    unfold kubiliusLoweredBarrier
    have hAlog : 0 ≤ A * Real.log u := mul_nonneg hA hlog
    linarith
  refine ⟨hinner, hinnerpos.trans_le hinner, ?_, hlower⟩
  calc
    2 * kubiliusLoweredBarrier c A B u ≤ 2 * (u * blockSigma c u) := by gcongr
    _ = u * (2 * blockSigma c u) := by ring
    _ ≤ u * r := mul_le_mul_of_nonneg_left hsmall.le hu0.le
    _ = r * u := by ring

/-! ### Integrated geometric-block majorant -/

/-- Coefficient retained inside the lowered barrier, strictly between the geometric variance
ratio and the packet coefficient. -/
noncomputable def kubiliusInnerCoefficient (c : ℝ) : ℝ :=
  (kubiliusBlockRatio c + c) / 2

/-- Power left after the optimized exponential estimate and its reciprocal-barrier prefactor. -/
noncomputable def kubiliusIntegratedDecayExponent (c : ℝ) : ℝ :=
  (kubiliusBlockRatio c - kubiliusInnerCoefficient c) /
    (4 * kubiliusBlockRatio c)

/-- Constant in the integrated one-block Kubilius majorant. -/
noncomputable def kubiliusIntegratedMajorantConstant (c : ℝ) : ℝ :=
  2 * kubiliusBlockRatio c / Real.sqrt (kubiliusInnerCoefficient c)

theorem kubiliusBlockRatio_lt_innerCoefficient {c : ℝ} (hc : 1 < c) :
    kubiliusBlockRatio c < kubiliusInnerCoefficient c := by
  unfold kubiliusInnerCoefficient
  linarith [kubiliusBlockRatio_lt hc]

theorem kubiliusInnerCoefficient_lt {c : ℝ} (hc : 1 < c) :
    kubiliusInnerCoefficient c < c := by
  unfold kubiliusInnerCoefficient
  linarith [kubiliusBlockRatio_lt hc]

theorem kubiliusInnerCoefficient_pos {c : ℝ} (hc : 1 < c) :
    0 < kubiliusInnerCoefficient c :=
  zero_lt_one.trans (one_lt_kubiliusBlockRatio hc) |>.trans
    (kubiliusBlockRatio_lt_innerCoefficient hc)

theorem kubiliusIntegratedDecayExponent_neg {c : ℝ} (hc : 1 < c) :
    kubiliusIntegratedDecayExponent c < 0 := by
  unfold kubiliusIntegratedDecayExponent
  exact div_neg_of_neg_of_pos
    (sub_neg.mpr (kubiliusBlockRatio_lt_innerCoefficient hc))
    (mul_pos (by norm_num) (zero_lt_one.trans (one_lt_kubiliusBlockRatio hc)))

/-- The negative-power majorant is summable along the geometric block schedule. -/
theorem summable_kubiliusIntegratedDecay {c : ℝ} (hc : 1 < c) :
    Summable (fun k : ℕ ↦ Real.rpow (kubiliusBlockRatio c)
      (kubiliusIntegratedDecayExponent c * (k : ℝ))) := by
  have hr : 1 < kubiliusBlockRatio c := one_lt_kubiliusBlockRatio hc
  have he : kubiliusIntegratedDecayExponent c < 0 :=
    kubiliusIntegratedDecayExponent_neg hc
  have hqpos : 0 < Real.rpow (kubiliusBlockRatio c)
      (kubiliusIntegratedDecayExponent c) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hr) _
  have hqnorm : ‖Real.rpow (kubiliusBlockRatio c)
      (kubiliusIntegratedDecayExponent c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hr he
  have hsum := summable_geometric_of_norm_lt_one hqnorm
  have hfun : (fun k : ℕ ↦ Real.rpow (kubiliusBlockRatio c)
      (kubiliusIntegratedDecayExponent c * (k : ℝ))) =
      fun k : ℕ ↦ Real.rpow (kubiliusBlockRatio c)
        (kubiliusIntegratedDecayExponent c) ^ k := by
    funext k
    exact Real.rpow_mul_natCast (zero_lt_one.trans hr).le _ k
  rw [hfun]
  exact hsum

/-- Substituting the geometric coordinate `u = r^k` puts the integrated one-block majorant in
the exact form used by `summable_kubiliusIntegratedDecay`. -/
theorem kubiliusIntegratedMajorant_geometric (c : ℝ) (k : ℕ)
    (hr : 0 ≤ kubiliusBlockRatio c) :
    kubiliusIntegratedMajorantConstant c *
        Real.rpow (Real.rpow (kubiliusBlockRatio c) (k : ℝ))
          (kubiliusIntegratedDecayExponent c) =
      kubiliusIntegratedMajorantConstant c *
        Real.rpow (kubiliusBlockRatio c)
          (kubiliusIntegratedDecayExponent c * (k : ℝ)) := by
  congr 1
  calc
    Real.rpow (Real.rpow (kubiliusBlockRatio c) (k : ℝ))
        (kubiliusIntegratedDecayExponent c) =
      Real.rpow (kubiliusBlockRatio c)
        ((k : ℝ) * kubiliusIntegratedDecayExponent c) :=
      (Real.rpow_mul hr (k : ℝ) (kubiliusIntegratedDecayExponent c)).symm
    _ = Real.rpow (kubiliusBlockRatio c)
        (kubiliusIntegratedDecayExponent c * (k : ℝ)) := by
      congr 1
      ring

theorem summable_kubiliusIntegratedMajorant {c : ℝ} (hc : 1 < c) :
    Summable (fun k : ℕ ↦ kubiliusIntegratedMajorantConstant c *
      Real.rpow (kubiliusBlockRatio c)
        (kubiliusIntegratedDecayExponent c * (k : ℝ))) :=
  (summable_kubiliusIntegratedDecay hc).mul_left _

/-- The integrated negative-power majorant is summable along any genuinely geometric schedule.
The schedule ratio need not equal the variance ratio used inside the one-block estimate.  This
separation leaves the strict slack needed later to absorb the additive Mertens and endpoint losses
at an arithmetic prime cutoff. -/
theorem summable_kubiliusIntegratedDecay_of_ratio {c q : ℝ}
    (hc : 1 < c) (hq : 1 < q) :
    Summable (fun k : ℕ ↦ Real.rpow q
      (kubiliusIntegratedDecayExponent c * (k : ℝ))) := by
  have he : kubiliusIntegratedDecayExponent c < 0 :=
    kubiliusIntegratedDecayExponent_neg hc
  have hqpos : 0 < Real.rpow q (kubiliusIntegratedDecayExponent c) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hq) _
  have hqnorm : ‖Real.rpow q (kubiliusIntegratedDecayExponent c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq he
  have hsum := summable_geometric_of_norm_lt_one hqnorm
  have hfun : (fun k : ℕ ↦ Real.rpow q
      (kubiliusIntegratedDecayExponent c * (k : ℝ))) =
      fun k : ℕ ↦ Real.rpow q (kubiliusIntegratedDecayExponent c) ^ k := by
    funext k
    exact Real.rpow_mul_natCast (zero_lt_one.trans hq).le _ k
  rw [hfun]
  exact hsum

/-- Substitution of an arbitrary positive geometric schedule into the integrated majorant. -/
theorem kubiliusIntegratedMajorant_geometric_of_ratio (c q : ℝ) (k : ℕ)
    (hq : 0 ≤ q) :
    kubiliusIntegratedMajorantConstant c *
        Real.rpow (Real.rpow q (k : ℝ)) (kubiliusIntegratedDecayExponent c) =
      kubiliusIntegratedMajorantConstant c *
        Real.rpow q (kubiliusIntegratedDecayExponent c * (k : ℝ)) := by
  congr 1
  calc
    Real.rpow (Real.rpow q (k : ℝ)) (kubiliusIntegratedDecayExponent c) =
        Real.rpow q ((k : ℝ) * kubiliusIntegratedDecayExponent c) :=
      (Real.rpow_mul hq (k : ℝ) (kubiliusIntegratedDecayExponent c)).symm
    _ = Real.rpow q (kubiliusIntegratedDecayExponent c * (k : ℝ)) := by
      congr 1
      exact mul_comm _ _

theorem summable_kubiliusIntegratedMajorant_of_ratio {c q : ℝ}
    (hc : 1 < c) (hq : 1 < q) :
    Summable (fun k : ℕ ↦ kubiliusIntegratedMajorantConstant c *
      Real.rpow q (kubiliusIntegratedDecayExponent c * (k : ℝ))) :=
  (summable_kubiliusIntegratedDecay_of_ratio hc hq).mul_left _

open Classical in
/-- The selected-prime walk up to the first `k` primes at terminal cutoff `y`, written as an
unordered finite-coordinate sum.  This is the form to which arithmetic prime cutoffs are mapped. -/
noncomputable def kubiliusSelectedPrimeWalk (y : ℕ) (S : Finset ℕ) (k : ℕ) : ℝ :=
  centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S
    (((primesUpTo y).sort (· ≤ ·)).take k).toFinset

open Classical in
/-- The finite-coordinate selected-prime walk is exactly the ordered prefix used by the maximal
inequality. -/
theorem kubiliusSelectedPrimeWalk_eq_centeredPrefixSum (y : ℕ) (S : Finset ℕ) (k : ℕ) :
    kubiliusSelectedPrimeWalk y S k =
      centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
        ((primesUpTo y).sort (· ≤ ·)) k := by
  rw [kubiliusSelectedPrimeWalk,
    centeredBernoulliPrefixSum_eq_finsetSum_take _ _ _
      ((primesUpTo y).sort_nodup (· ≤ ·))]

open Classical in
/-- At the time indexed by the number of primes up to `a`, the selected-prime walk at terminal
cutoff `y` is exactly the centered sum over primes up to `a`. -/
theorem kubiliusSelectedPrimeWalk_at_cutoff {a y : ℕ} (hay : a ≤ y) (S : Finset ℕ) :
    kubiliusSelectedPrimeWalk y S (primesUpTo a).card =
      centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S (primesUpTo a) := by
  unfold kubiliusSelectedPrimeWalk
  rw [primesUpTo_sort_take_card hay]

open Classical in
/-- Any crossing at an arithmetic prime cutoff `a ≤ y` is a crossing of the ordered walk before
the terminal cutoff.  This is the deterministic event inclusion needed before applying
`kubiliusMass_mono`. -/
theorem primeCutoffCrossing_subset_centeredPrefixCrossing (y : ℕ) (h : ℝ) :
    {S | ∃ a ≤ y, h ≤
        centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S (primesUpTo a)} ⊆
      {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
        h ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
          ((primesUpTo y).sort (· ≤ ·)) k} := by
  intro S hS
  obtain ⟨a, hay, hcross⟩ := hS
  refine ⟨(primesUpTo a).card, ?_, ?_⟩
  · rw [Finset.length_sort]
    apply Finset.card_le_card
    intro p hp
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · rw [← kubiliusSelectedPrimeWalk_eq_centeredPrefixSum,
      kubiliusSelectedPrimeWalk_at_cutoff hay]
    exact hcross

open Classical in
/-- The model mass of any arithmetic-cutoff crossing is bounded by the ordered-prefix crossing
mass controlled by the maximal inequality. -/
theorem kubiliusMass_primeCutoffCrossing_le_centeredPrefixCrossing
    (y : ℕ) (h : ℝ) :
    kubiliusMass y
        {S | ∃ a ≤ y, h ≤
          centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S (primesUpTo a)} ≤
      kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          h ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
            ((primesUpTo y).sort (· ≤ ·)) k} :=
  kubiliusMass_mono y (primeCutoffCrossing_subset_centeredPrefixCrossing y h)

open Classical in
/-- Crossing the selected-prime walk is definitionally the ordered-prefix event controlled by the
finite Doob inequality. -/
theorem exists_kubiliusSelectedPrimeWalk_ge_iff (y : ℕ) (S : Finset ℕ) (h : ℝ) :
    (∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
        h ≤ kubiliusSelectedPrimeWalk y S k) ↔
      ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
        h ≤ centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
          ((primesUpTo y).sort (· ≤ ·)) k := by
  simp_rw [kubiliusSelectedPrimeWalk_eq_centeredPrefixSum]

open Classical in
/-- Model mass of crossings above one lowered barrier, summed over auxiliary integer
thresholds. -/
noncomputable def kubiliusLoweredCrossingMass
    (y : ℕ) (c A B u : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, kubiliusMass y
    {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
      kubiliusLoweredBarrier c A B u + j ≤
        centeredBernoulliPrefixSum (fun p : ℕ ↦ (1 / p : ℝ)) S
          ((primesUpTo y).sort (· ≤ ·)) k}

open Classical in
/-- The lowered crossing mass is the total mass of actual selected-prime-walk crossings.  This
packages the deterministic event interface separately from the probabilistic estimate. -/
theorem kubiliusLoweredCrossingMass_eq_selectedPrimeWalk
    (y : ℕ) (c A B u : ℝ) (J : ℕ) :
    kubiliusLoweredCrossingMass y c A B u J =
      ∑ j ∈ Finset.range J, kubiliusMass y
        {S | ∃ k ≤ ((primesUpTo y).sort (· ≤ ·)).length,
          kubiliusLoweredBarrier c A B u + j ≤ kubiliusSelectedPrimeWalk y S k} := by
  unfold kubiliusLoweredCrossingMass
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext S
  exact (exists_kubiliusSelectedPrimeWalk_ge_iff y S
    (kubiliusLoweredBarrier c A B u + j)).symm

open Classical in
/-- The lowered-barrier crossing mass on one log-log block is eventually bounded by a fixed
negative power of the block coordinate, uniformly in the prime cutoff and number of auxiliary
thresholds. -/
theorem eventually_kubiliusLoweredCrossingMass_le
    {c : ℝ} (hc : 1 < c) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ u : ℝ in atTop, ∀ y J : ℕ, 2 ≤ y →
      Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
        kubiliusBlockRatio c * u →
      kubiliusLoweredCrossingMass y c A B u J ≤
        kubiliusIntegratedMajorantConstant c *
          Real.rpow u (kubiliusIntegratedDecayExponent c) := by
  let r : ℝ := kubiliusBlockRatio c
  let c₀ : ℝ := kubiliusInnerCoefficient c
  have hr : 0 < r := zero_lt_one.trans (one_lt_kubiliusBlockRatio hc)
  have hc₀ : 0 < c₀ := kubiliusInnerCoefficient_pos hc
  have hrc₀ : r < c₀ := kubiliusBlockRatio_lt_innerCoefficient hc
  have hc₀c : c₀ < c := kubiliusInnerCoefficient_lt hc
  have hconditions := eventually_kubiliusLoweredBarrier_conditions
    hc₀ (by linarith : 0 < c) hc₀c hr A B hA hB
  have hexponent := eventually_kubiliusOptimizedExponent_le hc₀ hr hrc₀
  filter_upwards [hconditions, hexponent,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1)] with u hconditions hexponent hlog hu
  intro y J hy hvar
  have hu1 : 1 ≤ u := by linarith [Real.exp_one_gt_two]
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hσ0 : 0 < blockSigma c₀ u := by
    unfold blockSigma
    exact Real.sqrt_pos.mpr (div_pos (mul_pos hc₀ (zero_lt_one.trans_le hlog)) hu0)
  have hh₀ : 0 < u * blockSigma c₀ u := mul_pos hu0 hσ0
  have hU : 0 < r * u := mul_pos hr hu0
  have hh₀U : 2 * (u * blockSigma c₀ u) ≤ r * u := by
    exact (mul_le_mul_of_nonneg_left hconditions.1 (by norm_num : (0 : ℝ) ≤ 2)).trans
      hconditions.2.2.1
  have hraw := sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_of_le
    y hy (u * blockSigma c₀ u) (kubiliusLoweredBarrier c A B u) (r * u)
    hh₀ hU hh₀U hvar hconditions.1 J
  have hexp :
      Real.exp (-(u * blockSigma c₀ u) ^ 2 / (2 * (r * u)) +
          (u * blockSigma c₀ u) ^ 3 / (r * u) ^ 2) ≤
        Real.rpow u (-(c₀ + r) / (4 * r)) := by
    calc
      Real.exp (-(u * blockSigma c₀ u) ^ 2 / (2 * (r * u)) +
          (u * blockSigma c₀ u) ^ 3 / (r * u) ^ 2) ≤
          Real.exp (-(c₀ + r) / (4 * r) * Real.log u) :=
        Real.exp_le_exp.mpr hexponent.2
      _ = Real.rpow u (-(c₀ + r) / (4 * r)) := by
        calc
          Real.exp (-(c₀ + r) / (4 * r) * Real.log u) =
              Real.exp (Real.log u * (-(c₀ + r) / (4 * r))) := by ring
          _ = Real.rpow u (-(c₀ + r) / (4 * r)) :=
            (Real.rpow_def_of_pos hu0 (-(c₀ + r) / (4 * r))).symm
  have hinv := blockSigma_inv_le_sqrt_div_sqrt c₀ u hc₀ hu1 hlog
  have hpref :
      2 * (r * u) / (u * blockSigma c₀ u) ≤
        (2 * r / Real.sqrt c₀) * Real.rpow u (1 / 2) := by
    have hsqrt : Real.rpow u (1 / 2) = Real.sqrt u := by
      exact Real.sqrt_eq_rpow u |>.symm
    rw [hsqrt]
    calc
      2 * (r * u) / (u * blockSigma c₀ u) =
          2 * r * (blockSigma c₀ u)⁻¹ := by
            field_simp [ne_of_gt hu0, ne_of_gt hσ0]
      _ ≤ 2 * r * (Real.sqrt u / Real.sqrt c₀) := by gcongr
      _ = (2 * r / Real.sqrt c₀) * Real.sqrt u := by ring
  have hpref0 : 0 ≤ 2 * (r * u) / (u * blockSigma c₀ u) := by positivity
  have hupper0 : 0 ≤ Real.rpow u (-(c₀ + r) / (4 * r)) :=
    Real.rpow_nonneg hu0.le _
  calc
    kubiliusLoweredCrossingMass y c A B u J ≤
        Real.exp (-(u * blockSigma c₀ u) ^ 2 / (2 * (r * u)) +
          (u * blockSigma c₀ u) ^ 3 / (r * u) ^ 2) *
            (2 * (r * u) / (u * blockSigma c₀ u)) := by
      simpa [kubiliusLoweredCrossingMass, r, c₀] using hraw
    _ ≤ Real.rpow u (-(c₀ + r) / (4 * r)) *
          ((2 * r / Real.sqrt c₀) * Real.rpow u (1 / 2)) :=
      mul_le_mul hexp hpref hpref0 hupper0
    _ = kubiliusIntegratedMajorantConstant c *
          Real.rpow u (kubiliusIntegratedDecayExponent c) := by
      have hrpow :
          Real.rpow u (-(c₀ + r) / (4 * r)) * Real.rpow u (1 / 2) =
            Real.rpow u ((r - c₀) / (4 * r)) := by
        calc
          Real.rpow u (-(c₀ + r) / (4 * r)) * Real.rpow u (1 / 2) =
              Real.rpow u (-(c₀ + r) / (4 * r) + 1 / 2) :=
            (Real.rpow_add hu0 (-(c₀ + r) / (4 * r)) (1 / 2)).symm
          _ = Real.rpow u ((r - c₀) / (4 * r)) := by
            congr 1
            field_simp [ne_of_gt hr]
            ring
      rw [show Real.rpow u (-(c₀ + r) / (4 * r)) *
          ((2 * r / Real.sqrt c₀) * Real.rpow u (1 / 2)) =
            (2 * r / Real.sqrt c₀) *
              (Real.rpow u (-(c₀ + r) / (4 * r)) * Real.rpow u (1 / 2)) by ring,
        hrpow]
      rfl

open Classical in
/-- Model mass of crossings at actual arithmetic prime cutoffs, summed over the auxiliary
integer thresholds. -/
noncomputable def kubiliusPrimeCutoffLoweredCrossingMass
    (y : ℕ) (c A B u : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, kubiliusMass y
    {S | ∃ a ≤ y, kubiliusLoweredBarrier c A B u + j ≤
      centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S (primesUpTo a)}

open Classical in
/-- Arithmetic-cutoff crossings are bounded by the ordered-prefix crossing quantity. -/
theorem kubiliusPrimeCutoffLoweredCrossingMass_le
    (y : ℕ) (c A B u : ℝ) (J : ℕ) :
    kubiliusPrimeCutoffLoweredCrossingMass y c A B u J ≤
      kubiliusLoweredCrossingMass y c A B u J := by
  unfold kubiliusPrimeCutoffLoweredCrossingMass kubiliusLoweredCrossingMass
  apply Finset.sum_le_sum
  intro j hj
  exact kubiliusMass_primeCutoffCrossing_le_centeredPrefixCrossing y
    (kubiliusLoweredBarrier c A B u + j)

open Classical in
/-- Uniform summable tail of actual prime-cutoff crossing masses over geometric log-log blocks.
The terminal cutoff and number of auxiliary thresholds may vary arbitrarily from block to block;
only the Mertens variance cap is required. -/
theorem exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt
    {c : ℝ} (hc : 1 < c) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ K : ℕ, ∀ H : ℕ, ∀ y J : ℕ → ℕ,
      (∀ k ∈ Finset.range H, 2 ≤ y (k + K) ∧
        Real.log (Real.log (y (k + K) : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio c * (kubiliusBlockRatio c : ℝ) ^ (k + K)) →
      (∑ k ∈ Finset.range H,
        kubiliusPrimeCutoffLoweredCrossingMass (y (k + K)) c A B
          ((kubiliusBlockRatio c : ℝ) ^ (k + K)) (J (k + K))) < ζ := by
  let r : ℝ := kubiliusBlockRatio c
  let f : ℕ → ℝ := fun k ↦ kubiliusIntegratedMajorantConstant c *
    Real.rpow r (kubiliusIntegratedDecayExponent c * (k : ℝ))
  have hr : 1 < r := one_lt_kubiliusBlockRatio hc
  have hsum : Summable f := by
    simpa [f, r] using summable_kubiliusIntegratedMajorant hc
  have hmodel := eventually_kubiliusLoweredCrossingMass_le hc A B hA hB
  have hrpow : Tendsto (fun k : ℕ ↦ (r : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  have hmodelNat : ∀ᶠ k : ℕ in atTop, ∀ y J : ℕ, 2 ≤ y →
      Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
        r * (r : ℝ) ^ k →
      kubiliusLoweredCrossingMass y c A B ((r : ℝ) ^ k) J ≤ f k := by
    filter_upwards [hrpow.eventually hmodel] with k hk
    intro y J hy hvar
    have h := hk y J hy hvar
    calc
      kubiliusLoweredCrossingMass y c A B (r ^ k) J ≤
          kubiliusIntegratedMajorantConstant c *
            Real.rpow (r ^ k) (kubiliusIntegratedDecayExponent c) := h
      _ = f k := by
        have hpow : (r : ℝ) ^ k = Real.rpow r (k : ℝ) :=
          (Real.rpow_natCast r k).symm
        rw [hpow]
        simpa only [f, r] using
          kubiliusIntegratedMajorant_geometric c k
            (by linarith : 0 ≤ kubiliusBlockRatio c)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hmodelNat
  have htailEv : ∀ᶠ K : ℕ in atTop, (∑' i : ℕ, f (i + K)) < ζ :=
    (tendsto_sum_nat_add f).eventually_lt_const hζ
  obtain ⟨K, hK⟩ := eventually_atTop.1 (htailEv.and (eventually_ge_atTop K₀))
  have hdata := hK K le_rfl
  refine ⟨K, ?_⟩
  intro H y J hvar
  have hfinite : (∑ k ∈ Finset.range H, f (k + K)) ≤ ∑' i : ℕ, f (i + K) := by
    have hconst : 0 ≤ kubiliusIntegratedMajorantConstant c := by
      unfold kubiliusIntegratedMajorantConstant
      positivity [kubiliusInnerCoefficient_pos hc, one_lt_kubiliusBlockRatio hc]
    have hf0 : ∀ i, 0 ≤ f (i + K) := by
      intro i
      exact mul_nonneg hconst (Real.rpow_nonneg (by linarith : 0 ≤ r) _)
    exact (hsum.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)).sum_le_tsum
      (Finset.range H) (fun i _ ↦ hf0 i)
  calc
    (∑ k ∈ Finset.range H,
        kubiliusPrimeCutoffLoweredCrossingMass (y (k + K)) c A B
          ((kubiliusBlockRatio c : ℝ) ^ (k + K)) (J (k + K))) ≤
        ∑ k ∈ Finset.range H, f (k + K) := by
      apply Finset.sum_le_sum
      intro k hk
      have hblock := hK₀ (k + K) (by omega)
      have hv := hvar k hk
      exact (kubiliusPrimeCutoffLoweredCrossingMass_le
        (y (k + K)) c A B (kubiliusBlockRatio c ^ (k + K)) (J (k + K))).trans
          (by simpa only [r] using hblock (y (k + K)) (J (k + K)) hv.1 hv.2)
    _ ≤ ∑' i : ℕ, f (i + K) := hfinite
    _ < ζ := hdata.1

open Classical in
/-- Uniform summable tail of arithmetic-cutoff crossing masses along an arbitrary geometric
schedule `q^k`, with the one-block variance cap still using `kubiliusBlockRatio c`.  In the global
arithmetic grouping we will take `q` strictly below that variance ratio, so the resulting gap can
absorb the additive `log 2 + mertensBound` endpoint loss. -/
theorem exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt_of_ratio
    {c q : ℝ} (hc : 1 < c) (hq : 1 < q) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ K : ℕ, ∀ H : ℕ, ∀ y J : ℕ → ℕ,
      (∀ k ∈ Finset.range H, 2 ≤ y (k + K) ∧
        Real.log (Real.log (y (k + K) : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio c * (q : ℝ) ^ (k + K)) →
      (∑ k ∈ Finset.range H,
        kubiliusPrimeCutoffLoweredCrossingMass (y (k + K)) c A B
          ((q : ℝ) ^ (k + K)) (J (k + K))) < ζ := by
  let f : ℕ → ℝ := fun k ↦ kubiliusIntegratedMajorantConstant c *
    Real.rpow q (kubiliusIntegratedDecayExponent c * (k : ℝ))
  have hsum : Summable f := by
    simpa only [f] using summable_kubiliusIntegratedMajorant_of_ratio hc hq
  have hmodel := eventually_kubiliusLoweredCrossingMass_le hc A B hA hB
  have hqpow : Tendsto (fun k : ℕ ↦ (q : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq
  have hmodelNat : ∀ᶠ k : ℕ in atTop, ∀ y J : ℕ, 2 ≤ y →
      Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
        kubiliusBlockRatio c * (q : ℝ) ^ k →
      kubiliusLoweredCrossingMass y c A B ((q : ℝ) ^ k) J ≤ f k := by
    filter_upwards [hqpow.eventually hmodel] with k hk
    intro y J hy hvar
    have h := hk y J hy hvar
    calc
      kubiliusLoweredCrossingMass y c A B (q ^ k) J ≤
          kubiliusIntegratedMajorantConstant c *
            Real.rpow (q ^ k) (kubiliusIntegratedDecayExponent c) := h
      _ = f k := by
        have hpow : (q : ℝ) ^ k = Real.rpow q (k : ℝ) :=
          (Real.rpow_natCast q k).symm
        rw [hpow]
        simpa only [f] using
          kubiliusIntegratedMajorant_geometric_of_ratio c q k (by linarith)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hmodelNat
  have htailEv : ∀ᶠ K : ℕ in atTop, (∑' i : ℕ, f (i + K)) < ζ :=
    (tendsto_sum_nat_add f).eventually_lt_const hζ
  obtain ⟨K, hK⟩ := eventually_atTop.1 (htailEv.and (eventually_ge_atTop K₀))
  have hdata := hK K le_rfl
  refine ⟨K, ?_⟩
  intro H y J hvar
  have hfinite : (∑ k ∈ Finset.range H, f (k + K)) ≤ ∑' i : ℕ, f (i + K) := by
    have hconst : 0 ≤ kubiliusIntegratedMajorantConstant c := by
      unfold kubiliusIntegratedMajorantConstant
      positivity [kubiliusInnerCoefficient_pos hc, one_lt_kubiliusBlockRatio hc]
    have hf0 : ∀ i, 0 ≤ f (i + K) := by
      intro i
      exact mul_nonneg hconst (Real.rpow_nonneg (by linarith : 0 ≤ q) _)
    exact (hsum.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)).sum_le_tsum
      (Finset.range H) (fun i _ ↦ hf0 i)
  calc
    (∑ k ∈ Finset.range H,
        kubiliusPrimeCutoffLoweredCrossingMass (y (k + K)) c A B
          ((q : ℝ) ^ (k + K)) (J (k + K))) ≤
        ∑ k ∈ Finset.range H, f (k + K) := by
      apply Finset.sum_le_sum
      intro k hk
      have hblock := hK₀ (k + K) (by omega)
      have hv := hvar k hk
      exact (kubiliusPrimeCutoffLoweredCrossingMass_le
        (y (k + K)) c A B (q ^ (k + K)) (J (k + K))).trans
          (hblock (y (k + K)) (J (k + K)) hv.1 hv.2)
    _ ≤ ∑' i : ℕ, f (i + K) := hfinite
    _ < ζ := hdata.1

open Classical in
/-- Uniform model-tail bound for an arbitrary finite family whose geometric schedule indices are
distinct.  This is the sparse-index form needed by the canonical arithmetic level partition:
missing geometric blocks cost nothing, and injectivity prevents any block majorant from being
charged twice. -/
theorem exists_kubiliusPrimeCutoffLoweredCrossingMass_injective_sum_lt_of_ratio
    {c q : ℝ} (hc : 1 < c) (hq : 1 < q) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ K : ℕ, ∀ {ι : Type*} (S : Finset ι) (key : ι → ℕ) (y J : ι → ℕ),
      Set.InjOn key (S : Set ι) →
      (∀ a ∈ S, K ≤ key a) →
      (∀ a ∈ S, 2 ≤ y a ∧
        Real.log (Real.log (y a : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio c * (q : ℝ) ^ key a) →
      (∑ a ∈ S, kubiliusPrimeCutoffLoweredCrossingMass (y a) c A B
        ((q : ℝ) ^ key a) (J a)) < ζ := by
  let f : ℕ → ℝ := fun k ↦ kubiliusIntegratedMajorantConstant c *
    Real.rpow q (kubiliusIntegratedDecayExponent c * (k : ℝ))
  have hsum : Summable f := by
    simpa only [f] using summable_kubiliusIntegratedMajorant_of_ratio hc hq
  have hmodel := eventually_kubiliusLoweredCrossingMass_le hc A B hA hB
  have hqpow : Tendsto (fun k : ℕ ↦ (q : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq
  have hmodelNat : ∀ᶠ k : ℕ in atTop, ∀ y J : ℕ, 2 ≤ y →
      Real.log (Real.log (y : ℝ)) + Erdos67.PrimeEstimates.mertensBound ≤
        kubiliusBlockRatio c * (q : ℝ) ^ k →
      kubiliusLoweredCrossingMass y c A B ((q : ℝ) ^ k) J ≤ f k := by
    filter_upwards [hqpow.eventually hmodel] with k hk
    intro y J hy hvar
    have h := hk y J hy hvar
    calc
      kubiliusLoweredCrossingMass y c A B (q ^ k) J ≤
          kubiliusIntegratedMajorantConstant c *
            Real.rpow (q ^ k) (kubiliusIntegratedDecayExponent c) := h
      _ = f k := by
        have hpow : (q : ℝ) ^ k = Real.rpow q (k : ℝ) :=
          (Real.rpow_natCast q k).symm
        rw [hpow]
        simpa only [f] using
          kubiliusIntegratedMajorant_geometric_of_ratio c q k (by linarith)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hmodelNat
  have htailEv : ∀ᶠ K : ℕ in atTop, (∑' i : ℕ, f (i + K)) < ζ :=
    (tendsto_sum_nat_add f).eventually_lt_const hζ
  obtain ⟨K, hK⟩ := eventually_atTop.1 (htailEv.and (eventually_ge_atTop K₀))
  have hdata := hK K le_rfl
  refine ⟨K, ?_⟩
  intro ι S key y J hinj hkey hvar
  have hoffsetInj : Set.InjOn (fun a ↦ key a - K) (S : Set ι) := by
    intro a ha b hb hab
    apply hinj ha hb
    have hka := hkey a ha
    have hkb := hkey b hb
    calc
      key a = (key a - K) + K := (Nat.sub_add_cancel hka).symm
      _ = (key b - K) + K := congrArg (fun n ↦ n + K) hab
      _ = key b := Nat.sub_add_cancel hkb
  have hrewrite :
      (∑ a ∈ S, f (key a)) =
        ∑ i ∈ S.image (fun a ↦ key a - K), f (i + K) := by
    calc
      (∑ a ∈ S, f (key a)) =
          ∑ a ∈ S, f ((key a - K) + K) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Nat.sub_add_cancel (hkey a ha)]
      _ = ∑ i ∈ S.image (fun a ↦ key a - K), f (i + K) :=
        (Finset.sum_image (f := fun i ↦ f (i + K)) hoffsetInj).symm
  have hconst : 0 ≤ kubiliusIntegratedMajorantConstant c := by
    unfold kubiliusIntegratedMajorantConstant
    positivity [kubiliusInnerCoefficient_pos hc, one_lt_kubiliusBlockRatio hc]
  have hf0 : ∀ i, 0 ≤ f (i + K) := by
    intro i
    exact mul_nonneg hconst (Real.rpow_nonneg (by linarith : 0 ≤ q) _)
  have hfinite :
      (∑ i ∈ S.image (fun a ↦ key a - K), f (i + K)) ≤
        ∑' i : ℕ, f (i + K) :=
    (hsum.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)).sum_le_tsum
      (S.image (fun a ↦ key a - K)) (fun i _ ↦ hf0 i)
  calc
    (∑ a ∈ S, kubiliusPrimeCutoffLoweredCrossingMass (y a) c A B
        ((q : ℝ) ^ key a) (J a)) ≤ ∑ a ∈ S, f (key a) := by
      apply Finset.sum_le_sum
      intro a ha
      have hblock := hK₀ (key a) ((hdata.2).trans (hkey a ha))
      have hv := hvar a ha
      exact (kubiliusPrimeCutoffLoweredCrossingMass_le
        (y a) c A B (q ^ key a) (J a)).trans
          (hblock (y a) (J a) hv.1 hv.2)
    _ = ∑ i ∈ S.image (fun a ↦ key a - K), f (i + K) := hrewrite
    _ ≤ ∑' i : ℕ, f (i + K) := hfinite
    _ < ζ := hdata.1

open Classical in
/-- `KubiliusTV` transferred termwise to a finite family of arithmetic events.  This form records
the accumulated total-variation error needed when the auxiliary divisor-mass thresholds are
truncated. -/
theorem kubiliusTV_sum_card_div_le (hK : KubiliusTV) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y J : ℕ, 2 ≤ y → y ≤ N → ∀ A : ℕ → Set (Finset ℕ),
      (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 N).filter
          (fun n => n.primeFactors.filter (fun p => p ≤ y) ∈ A j)).card : ℝ) / N) ≤
        (∑ j ∈ Finset.range J, kubiliusMass y (A j)) +
          J * C * (Real.rpow (Real.log N / Real.log y)
            (-(Real.log N / Real.log y)) + Real.rpow N (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC, hTV⟩ := hK
  refine ⟨C, hC, ?_⟩
  intro N y J hy hyN A
  let E := Real.rpow (Real.log N / Real.log y) (-(Real.log N / Real.log y)) +
    Real.rpow N (-(1 / 2 : ℝ))
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 N).filter
          (fun n => n.primeFactors.filter (fun p => p ≤ y) ∈ A j)).card : ℝ) / N) ≤
        ∑ j ∈ Finset.range J, (kubiliusMass y (A j) + C * E) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (abs_le.mp (hTV N y hy hyN (A j))).2
      dsimp only [E]
      linarith
    _ = (∑ j ∈ Finset.range J, kubiliusMass y (A j)) + J * C * E := by
      rw [Finset.sum_add_distrib]
      simp
      ring

open Classical in
lemma centeredBernoulliFinsetSum_eq_card_inter_sub_sum {α : Type*} [DecidableEq α]
    (q : α → ℝ) (S U : Finset α) :
    centeredBernoulliFinsetSum q S U =
      ((S ∩ U).card : ℝ) - ∑ p ∈ U, q p := by
  unfold centeredBernoulliFinsetSum
  calc
    (∑ p ∈ U, if p ∈ S then 1 - q p else -q p) =
        ∑ p ∈ U, ((if p ∈ S then 1 else 0) - q p) := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    _ = (∑ p ∈ U, if p ∈ S then 1 else 0) - ∑ p ∈ U, q p := by
      rw [Finset.sum_sub_distrib]
    _ = ((S ∩ U).card : ℝ) - ∑ p ∈ U, q p := by
      congr 1
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.cast_inj]
      rw [Finset.inter_comm]

/-- Largest divisor whose square divides `n`, written prime by prime. -/
def squareDivisorRoot (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

lemma squareDivisorRoot_ne_zero (n : ℕ) : squareDivisorRoot n ≠ 0 := by
  unfold squareDivisorRoot
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma squareDivisorRoot_factorization (n p : ℕ) :
    (squareDivisorRoot n).factorization p = n.factorization p / 2 := by
  let P := n.primeFactors
  change (∏ q ∈ P, q ^ (n.factorization q / 2)).factorization p = n.factorization p / 2
  rw [Nat.factorization_prod_apply]
  · by_cases hp : p ∈ P
    · calc
        (∑ q ∈ P, (q ^ (n.factorization q / 2)).factorization p) =
            (p ^ (n.factorization p / 2)).factorization p := by
          apply Finset.sum_eq_single p
          · intro q hq hqp
            rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow]
            simp [hqp]
          · simp [hp]
        _ = n.factorization p / 2 := by
          rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow]
          simp
    · have hfac : n.factorization p = 0 := by
        have : p ∉ n.factorization.support := by
          simpa only [Nat.support_factorization] using hp
        exact Finsupp.notMem_support_iff.mp this
      rw [hfac]
      simp only [Nat.zero_div]
      apply Finset.sum_eq_zero
      intro q hq
      have hqp : q ≠ p := by
        intro hqp
        subst q
        exact hp hq
      rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow]
      simp [hqp]
  · intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero

lemma sq_dvd_iff_dvd_squareDivisorRoot {n q : ℕ} (hn : n ≠ 0) :
    q ^ 2 ∣ n ↔ q ∣ squareDivisorRoot n := by
  by_cases hq : q = 0
  · subst q
    simp [hn, squareDivisorRoot_ne_zero]
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hq) hn,
    ← Nat.factorization_le_iff_dvd hq (squareDivisorRoot_ne_zero n)]
  simp only [Finsupp.le_def]
  constructor
  · intro h p
    rw [squareDivisorRoot_factorization]
    have hp : 2 * q.factorization p ≤ n.factorization p := by
      simpa [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul] using h p
    omega
  · intro h p
    have hp : q.factorization p ≤ n.factorization p / 2 := by
      simpa only [squareDivisorRoot_factorization] using h p
    have hp' : 2 * q.factorization p ≤ n.factorization p := by omega
    simpa [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul] using hp'

lemma squareDivisorRoot_primeFactors_subset (n : ℕ) :
    (squareDivisorRoot n).primeFactors ⊆ n.primeFactors := by
  intro p hp
  have hpSupport : p ∈ (squareDivisorRoot n).factorization.support := by
    simpa only [Nat.support_factorization] using hp
  have hpFac : (squareDivisorRoot n).factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp hpSupport
  rw [squareDivisorRoot_factorization] at hpFac
  have hnFac : n.factorization p ≠ 0 := by omega
  have : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hnFac
  simpa only [Nat.support_factorization] using this

/-- The number of available square-divisor choices in `n`. -/
def squareDivisorCount (n : ℕ) : ℕ := (squareDivisorRoot n).divisors.card

lemma squareDivisorCount_eq_prod (n : ℕ) :
    squareDivisorCount n =
      ∏ p ∈ n.primeFactors, (n.factorization p / 2 + 1) := by
  rw [squareDivisorCount, Nat.card_divisors (squareDivisorRoot_ne_zero n)]
  calc
    (∏ p ∈ (squareDivisorRoot n).primeFactors,
        ((squareDivisorRoot n).factorization p + 1)) =
        ∏ p ∈ (squareDivisorRoot n).primeFactors,
          (n.factorization p / 2 + 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [squareDivisorRoot_factorization]
    _ = ∏ p ∈ n.primeFactors, (n.factorization p / 2 + 1) := by
      apply Finset.prod_subset (squareDivisorRoot_primeFactors_subset n)
      intro p hp hproot
      have hpNot : p ∉ (squareDivisorRoot n).factorization.support := by
        simpa only [Nat.support_factorization] using hproot
      have hpZero := Finsupp.notMem_support_iff.mp hpNot
      rw [squareDivisorRoot_factorization] at hpZero
      simp [hpZero]

lemma smoothDivisorCount_le_two_pow_mul_squareDivisorCount (y n : ℕ) :
    smoothDivisorCount y n ≤
      2 ^ (n.primeFactors.filter (fun p => p ≤ y)).card * squareDivisorCount n := by
  let S := n.primeFactors.filter (fun p => p ≤ y)
  rw [smoothDivisorCount, squareDivisorCount_eq_prod]
  calc
    (∏ p ∈ S, (n.factorization p + 1)) ≤
        ∏ p ∈ S, (2 * (n.factorization p / 2 + 1)) := by
      gcongr with p hp
      omega
    _ = 2 ^ S.card * ∏ p ∈ S, (n.factorization p / 2 + 1) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ 2 ^ S.card * ∏ p ∈ n.primeFactors, (n.factorization p / 2 + 1) := by
      apply Nat.mul_le_mul_left
      exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
        (fun _ _ ↦ Nat.zero_le _) (fun _ _ _ ↦ by omega)

lemma squareDivisorRoot_divisors_eq_filter_sq_dvd {n T : ℕ}
    (hn : n ∈ Finset.Icc 1 T) :
    (squareDivisorRoot n).divisors =
      (Finset.Icc 1 T).filter (fun q => q ^ 2 ∣ n) := by
  have hnIcc : 1 ≤ n ∧ n ≤ T := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  ext q
  constructor
  · intro hq
    have hqroot : q ∣ squareDivisorRoot n := Nat.dvd_of_mem_divisors hq
    have hsq : q ^ 2 ∣ n := (sq_dvd_iff_dvd_squareDivisorRoot hn0).2 hqroot
    have hq0 : q ≠ 0 := by
      intro hq0
      subst q
      exact squareDivisorRoot_ne_zero n (by simpa using hqroot)
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hsqle : q ^ 2 ≤ n := Nat.le_of_dvd (by omega) hsq
    have hqle : q ≤ q ^ 2 := by
      calc
        q = q * 1 := by omega
        _ ≤ q * q := Nat.mul_le_mul_left q hq1
        _ = q ^ 2 := by ring
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hq1, hqle.trans (hsqle.trans hnIcc.2)⟩, hsq⟩
  · intro hq
    rw [Finset.mem_filter] at hq
    exact Nat.mem_divisors.mpr
      ⟨(sq_dvd_iff_dvd_squareDivisorRoot hn0).1 hq.2, squareDivisorRoot_ne_zero n⟩

lemma sum_squareDivisorCount_eq_sum_div (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, squareDivisorCount n =
      ∑ q ∈ Finset.Icc 1 T, T / q ^ 2 := by
  calc
    ∑ n ∈ Finset.Icc 1 T, squareDivisorCount n =
        ∑ n ∈ Finset.Icc 1 T,
          ((Finset.Icc 1 T).filter (fun q => q ^ 2 ∣ n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [squareDivisorCount, squareDivisorRoot_divisors_eq_filter_sq_dvd hn]
    _ = ∑ n ∈ Finset.Icc 1 T, ∑ q ∈ Finset.Icc 1 T,
          if q ^ 2 ∣ n then 1 else 0 := by
      simp only [Finset.card_filter]
    _ = ∑ q ∈ Finset.Icc 1 T, ∑ n ∈ Finset.Icc 1 T,
          if q ^ 2 ∣ n then 1 else 0 := Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 T,
          ((Finset.Icc 1 T).filter (fun n => q ^ 2 ∣ n)).card := by
      simp only [Finset.card_filter]
    _ = ∑ q ∈ Finset.Icc 1 T, T / q ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hIcc : Finset.Icc 1 T = Finset.Ioc 0 T := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- The convergent reciprocal-square mass controlling square-divisor excess on average. -/
noncomputable def squareDivisorMomentConstant : ℝ :=
  ∑' q : ℕ, (1 : ℝ) / (q : ℝ) ^ 2

lemma squareDivisorMomentConstant_nonneg : 0 ≤ squareDivisorMomentConstant := by
  unfold squareDivisorMomentConstant
  exact tsum_nonneg fun q => by positivity

lemma sum_squareDivisorCount_le (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (squareDivisorCount n : ℝ)) ≤
      T * squareDivisorMomentConstant := by
  have hsum : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
    hasSum_zeta_two.summable
  calc
    (∑ n ∈ Finset.Icc 1 T, (squareDivisorCount n : ℝ)) =
        ((∑ n ∈ Finset.Icc 1 T, squareDivisorCount n : ℕ) : ℝ) := by norm_num
    _ = ∑ q ∈ Finset.Icc 1 T, ((T / q ^ 2 : ℕ) : ℝ) := by
      rw [sum_squareDivisorCount_eq_sum_div]
      norm_num
    _ ≤ ∑ q ∈ Finset.Icc 1 T, (T : ℝ) / (q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        ((T / q ^ 2 : ℕ) : ℝ) ≤ (T : ℝ) / ((q ^ 2 : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = (T : ℝ) / (q : ℝ) ^ 2 := by norm_num
    _ = (T : ℝ) * ∑ q ∈ Finset.Icc 1 T, (1 : ℝ) / (q : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ T * squareDivisorMomentConstant := by
      gcongr
      exact hsum.sum_le_tsum (Finset.Icc 1 T) (fun q hq => by positivity)

lemma squareDivisorCount_large_card_mul_le (T : ℕ) (U : ℝ) :
    (((Finset.Icc 1 T).filter (fun n => U < squareDivisorCount n)).card : ℝ) * U ≤
      T * squareDivisorMomentConstant := by
  let B := (Finset.Icc 1 T).filter (fun n => U < squareDivisorCount n)
  calc
    (B.card : ℝ) * U = ∑ _n ∈ B, U := by simp
    _ ≤ ∑ n ∈ B, (squareDivisorCount n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Finset.mem_filter.mp hn).2.le
    _ ≤ ∑ n ∈ Finset.Icc 1 T, (squareDivisorCount n : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ by positivity)
    _ ≤ T * squareDivisorMomentConstant := sum_squareDivisorCount_le T

lemma squareDivisorCount_large_card_le (T : ℕ) (U : ℝ) (hU : 0 < U) :
    (((Finset.Icc 1 T).filter (fun n => U < squareDivisorCount n)).card : ℝ) ≤
      T * squareDivisorMomentConstant / U := by
  rw [le_div_iff₀ hU]
  exact squareDivisorCount_large_card_mul_le T U

lemma weightedDivisorBlockMass_le_two_pow_mul_squareDivisorCount
    (weight : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W) (ℓ n : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) →
      weight d ≤ W) :
    weightedDivisorBlockMass weight ℓ n ≤
      ((2 : ℝ) ^ (n.primeFactors.filter
        (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card) * squareDivisorCount n * W := by
  calc
    weightedDivisorBlockMass weight ℓ n ≤
        (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W :=
      weightedDivisorBlockMass_le_smoothDivisorCount weight W hW ℓ n hweight
    _ ≤ ((2 : ℝ) ^ (n.primeFactors.filter
          (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card) * squareDivisorCount n * W := by
      gcongr
      exact_mod_cast smoothDivisorCount_le_two_pow_mul_squareDivisorCount
        (dyadicExpCutoff (ℓ + 1)) n

lemma subpowerWeightedDivisorBlockMass_le_two_pow_mul_squareDivisorCount
    (c : ℝ) (hc : 0 ≤ c) (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (n : ℕ) :
    weightedDivisorBlockMass (subpowerWeight c) ℓ n ≤
      ((2 : ℝ) ^ (n.primeFactors.filter
        (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card) * squareDivisorCount n *
          subpowerWeight c (dyadicExpCutoff ℓ) := by
  exact weightedDivisorBlockMass_le_two_pow_mul_squareDivisorCount
    (subpowerWeight c) (subpowerWeight c (dyadicExpCutoff ℓ))
    (subpowerWeight_nonneg c _) ℓ n
    (fun d hdlo _ ↦ subpowerWeight_block_le c hc ℓ hℓ d hdlo)

lemma subpowerWeightedDivisorBlockMass_large_imp
    (c : ℝ) (hc : 0 ≤ c) (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (n : ℕ) (R U : ℝ)
    (hmass : R < weightedDivisorBlockMass (subpowerWeight c) ℓ n) :
    U < squareDivisorCount n ∨
      R < ((2 : ℝ) ^ (n.primeFactors.filter
        (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card) * U *
          subpowerWeight c (dyadicExpCutoff ℓ) := by
  by_cases hQ : U < squareDivisorCount n
  · exact Or.inl hQ
  · right
    have hQle : (squareDivisorCount n : ℝ) ≤ U := le_of_not_gt hQ
    refine hmass.trans_le ((subpowerWeightedDivisorBlockMass_le_two_pow_mul_squareDivisorCount
      c hc ℓ hℓ n).trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQle (by positivity)) (subpowerWeight_nonneg c _)

lemma log_ratio_lt_card_of_lt_two_pow_mul
    (k : ℕ) (R U W : ℝ) (hR : 0 < R) (hU : 0 < U) (hW : 0 < W)
    (hlt : R < (2 : ℝ) ^ k * U * W) :
    (Real.log R - Real.log U - Real.log W) / Real.log 2 < k := by
  have hlog := Real.log_lt_log hR hlt
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt hU))
      (ne_of_gt hW),
    Real.log_mul (pow_ne_zero _ (by norm_num)) (ne_of_gt hU), Real.log_pow] at hlog
  rw [div_lt_iff₀ (Real.log_pos one_lt_two)]
  linarith

lemma subpowerWeight_dyadicExpCutoff_pos (c : ℝ) (ℓ : ℕ) :
    0 < subpowerWeight c (dyadicExpCutoff ℓ) := by
  have hlogcut : 0 < Real.log (dyadicExpCutoff ℓ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < dyadicExpCutoff ℓ by
      exact lt_of_lt_of_le (by omega) (dyadicExpCutoff_two_le ℓ)))
  unfold subpowerWeight
  exact mul_pos (Real.rpow_pos_of_pos hlogcut _) (Real.exp_pos _)

lemma log_subpowerWeight_dyadicExpCutoff (c : ℝ) (ℓ : ℕ) :
    Real.log (subpowerWeight c (dyadicExpCutoff ℓ)) =
      -(Real.log 2) * blockLogLog ℓ -
        Real.log 2 * Real.sqrt
          (c * blockLogLog ℓ * Real.log (blockLogLog ℓ)) := by
  have hlogcut : 0 < Real.log (dyadicExpCutoff ℓ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < dyadicExpCutoff ℓ by
      exact lt_of_lt_of_le (by omega) (dyadicExpCutoff_two_le ℓ)))
  unfold subpowerWeight
  change Real.log (((Real.log (dyadicExpCutoff ℓ : ℝ)) ^ (-Real.log 2)) *
      Real.exp (-(Real.log 2) *
        Real.sqrt (c * Real.log (Real.log (dyadicExpCutoff ℓ : ℝ)) *
          Real.log (Real.log (Real.log (dyadicExpCutoff ℓ : ℝ)))))) = _
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hlogcut (-Real.log 2)))
    (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_rpow hlogcut, Real.log_exp]
  rw [show Real.log (Real.log (dyadicExpCutoff ℓ : ℝ)) = blockLogLog ℓ by rfl]
  ring

lemma sqrt_mul_eq_mul_blockSigma (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    Real.sqrt (c * u * Real.log u) = u * blockSigma c u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have harg : 0 ≤ c * u * Real.log u :=
    mul_nonneg (mul_nonneg hc hu0.le) (Real.log_nonneg hu)
  have hright0 : 0 ≤ u * blockSigma c u :=
    mul_nonneg hu0.le (Real.sqrt_nonneg _)
  rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) hright0, Real.sq_sqrt harg]
  calc
    c * u * Real.log u = u * (c * Real.log u) := by ring
    _ = u * (u * blockSigma c u ^ 2) := by rw [blockSigma_sq c u hc hu]
    _ = (u * blockSigma c u) ^ 2 := by ring

lemma log_subpowerWeight_dyadicExpCutoff_eq_blockSigma
    (c : ℝ) (hc : 0 ≤ c) (ℓ : ℕ) (hℓ : 1 ≤ blockLogLog ℓ) :
    Real.log (subpowerWeight c (dyadicExpCutoff ℓ)) =
      -(Real.log 2) * blockLogLog ℓ -
        Real.log 2 * (blockLogLog ℓ * blockSigma c (blockLogLog ℓ)) := by
  rw [log_subpowerWeight_dyadicExpCutoff,
    sqrt_mul_eq_mul_blockSigma c (blockLogLog ℓ) hc hℓ]

lemma subpowerBlock_two_pow_large_imp_primeFactor_card_gt
    (c : ℝ) (hc : 0 ≤ c) (ℓ n : ℕ) (hℓ : 1 ≤ blockLogLog ℓ)
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (hlt : R < ((2 : ℝ) ^ (n.primeFactors.filter
      (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card) * U *
        subpowerWeight c (dyadicExpCutoff ℓ)) :
    blockLogLog ℓ * blockSigma c (blockLogLog ℓ) + blockLogLog ℓ +
        (Real.log R - Real.log U) / Real.log 2 <
      (n.primeFactors.filter (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card := by
  have h := log_ratio_lt_card_of_lt_two_pow_mul
    (n.primeFactors.filter (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card
    R U (subpowerWeight c (dyadicExpCutoff ℓ)) hR hU
    (subpowerWeight_dyadicExpCutoff_pos c ℓ) hlt
  rw [log_subpowerWeight_dyadicExpCutoff_eq_blockSigma c hc ℓ hℓ] at h
  calc
    blockLogLog ℓ * blockSigma c (blockLogLog ℓ) + blockLogLog ℓ +
        (Real.log R - Real.log U) / Real.log 2 =
      (Real.log R - Real.log U -
        (-(Real.log 2) * blockLogLog ℓ -
          Real.log 2 * (blockLogLog ℓ * blockSigma c (blockLogLog ℓ)))) /
            Real.log 2 := by
      field_simp [ne_of_gt (Real.log_pos one_lt_two)]
      ring
    _ < (n.primeFactors.filter
        (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card := h

open Classical in
lemma primeFactors_filter_inter_primesUpTo {n a y : ℕ} (hay : a ≤ y) :
    n.primeFactors.filter (fun p => p ≤ y) ∩ primesUpTo a =
      n.primeFactors.filter (fun p => p ≤ a) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, primesUpTo, Finset.mem_range,
    Nat.lt_add_one_iff]
  constructor
  · rintro ⟨⟨hpn, _⟩, hpa, _⟩
    exact ⟨hpn, hpa⟩
  · rintro ⟨hpn, hpa⟩
    exact ⟨⟨hpn, hpa.trans hay⟩, hpa, Nat.prime_of_mem_primeFactors hpn⟩

open Classical in
lemma centeredBernoulliFinsetSum_primeFactors_filter_primesUpTo
    {n a y : ℕ} (hay : a ≤ y) :
    centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ))
        (n.primeFactors.filter (fun p => p ≤ y)) (primesUpTo a) =
      ((n.primeFactors.filter (fun p => p ≤ a)).card : ℝ) -
        ∑ p ∈ primesUpTo a, (1 / p : ℝ) := by
  rw [centeredBernoulliFinsetSum_eq_card_inter_sub_sum,
    primeFactors_filter_inter_primesUpTo hay]

open Classical in
lemma subpowerBlock_two_pow_large_imp_centered_sum_gt
    (c : ℝ) (hc : 0 ≤ c) (ℓ n y : ℕ) (hℓ : 1 ≤ blockLogLog ℓ)
    (hy : dyadicExpCutoff (ℓ + 1) ≤ y) (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (hlt : R < ((2 : ℝ) ^ (n.primeFactors.filter
      (fun p => p ≤ dyadicExpCutoff (ℓ + 1))).card) * U *
        subpowerWeight c (dyadicExpCutoff ℓ)) :
    blockLogLog ℓ * blockSigma c (blockLogLog ℓ) +
        (Real.log R - Real.log U) / Real.log 2 - Real.log 2 -
          Erdos67.PrimeEstimates.mertensBound <
      centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ))
        (n.primeFactors.filter (fun p => p ≤ y))
          (primesUpTo (dyadicExpCutoff (ℓ + 1))) := by
  have hcard := subpowerBlock_two_pow_large_imp_primeFactor_card_gt
    c hc ℓ n hℓ R U hR hU hlt
  have hmean :
      (∑ p ∈ primesUpTo (dyadicExpCutoff (ℓ + 1)), (1 / p : ℝ)) ≤
        blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound := by
    simpa only [primesUpTo_eq_primesLE, blockLogLog] using
      (primeReciprocalMass_le_log_log_add (dyadicExpCutoff (ℓ + 1))
        (dyadicExpCutoff_two_le (ℓ + 1)))
  rw [centeredBernoulliFinsetSum_primeFactors_filter_primesUpTo hy]
  rw [blockLogLog_succ] at hmean
  linarith

open Classical in
/-- A large divisor block is covered by the square-divisor exceptional event or by an explicit
crossing of the centered small-prime walk.  This is the arithmetic event inclusion needed before
applying `KubiliusTV`. -/
lemma subpowerWeightedDivisorBlockMass_large_imp_square_or_centered_sum_gt
    (c : ℝ) (hc : 0 ≤ c) (ℓ n y : ℕ) (hℓ : 3 ≤ ℓ)
    (hlog : 1 ≤ blockLogLog ℓ) (hy : dyadicExpCutoff (ℓ + 1) ≤ y)
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (hmass : R < weightedDivisorBlockMass (subpowerWeight c) ℓ n) :
    U < squareDivisorCount n ∨
      blockLogLog ℓ * blockSigma c (blockLogLog ℓ) +
          (Real.log R - Real.log U) / Real.log 2 - Real.log 2 -
            Erdos67.PrimeEstimates.mertensBound <
        centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ))
          (n.primeFactors.filter (fun p => p ≤ y))
            (primesUpTo (dyadicExpCutoff (ℓ + 1))) := by
  rcases subpowerWeightedDivisorBlockMass_large_imp c hc ℓ hℓ n R U hmass with
    hQ | hwalk
  · exact Or.inl hQ
  · exact Or.inr (subpowerBlock_two_pow_large_imp_centered_sum_gt
      c hc ℓ n y hlog hy R U hR hU hwalk)

lemma log_blockAllocation_ge (ℓ : ℕ) (hℓ : 6 ≤ ℓ) :
    -(2 * Real.log (blockLogLog ℓ) + 2 * Real.log 4) ≤
      Real.log (blockAllocation ℓ) := by
  let u : ℝ := blockLogLog ℓ
  have hu4 : ((ℓ : ℝ) + 2) / 4 ≤ u := by
    simpa only [u] using blockLogLog_ge_quarter_add ℓ hℓ
  have hu : 0 < u := by
    have : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4 := by positivity
    linarith
  have hle : (ℓ : ℝ) + 2 ≤ 4 * u := by linarith
  have hprod : ((ℓ : ℝ) + 1) * ((ℓ : ℝ) + 2) ≤ (4 * u) ^ 2 := by
    calc
      ((ℓ : ℝ) + 1) * ((ℓ : ℝ) + 2) ≤ ((ℓ : ℝ) + 2) * ((ℓ : ℝ) + 2) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ (4 * u) * (4 * u) := by gcongr
      _ = (4 * u) ^ 2 := by ring
  have hrecip : 1 / (4 * u) ^ 2 ≤ blockAllocation ℓ := by
    unfold blockAllocation
    exact one_div_le_one_div_of_le (by positivity) hprod
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (4 * u) ^ 2) hrecip
  calc
    -(2 * Real.log u + 2 * Real.log 4) = Real.log (1 / (4 * u) ^ 2) := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
          (pow_ne_zero 2 (mul_ne_zero (by norm_num) (ne_of_gt hu))),
        Real.log_one, zero_sub, Real.log_pow, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (ne_of_gt hu)]
      ring
    _ ≤ Real.log (blockAllocation ℓ) := hlog

lemma log_subpowerBlockThreshold (A : ℝ) (hA : 0 < A) (ℓ j : ℕ) :
    Real.log (subpowerBlockThreshold A ℓ j) =
      Real.log A + Real.log (blockAllocation ℓ) + (j : ℝ) / 2 * Real.log 2 := by
  unfold subpowerBlockThreshold
  change Real.log (A * blockAllocation ℓ * (2 ^ ((j : ℝ) / 2))) = _
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hA) (ne_of_gt (blockAllocation_pos ℓ)))
      (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)),
    Real.log_mul (ne_of_gt hA) (ne_of_gt (blockAllocation_pos ℓ)),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

noncomputable def subpowerKubiliusSquareCutoff (D u : ℝ) (j : ℕ) : ℝ :=
  Real.rpow u D * Real.rpow 2 ((j : ℝ) / 4)

lemma subpowerKubiliusSquareCutoff_pos (D u : ℝ) (j : ℕ) (hu : 0 < u) :
    0 < subpowerKubiliusSquareCutoff D u j := by
  unfold subpowerKubiliusSquareCutoff
  exact mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos (by norm_num) _)

lemma log_subpowerKubiliusSquareCutoff (D u : ℝ) (j : ℕ) (hu : 0 < u) :
    Real.log (subpowerKubiliusSquareCutoff D u j) =
      D * Real.log u + (j : ℝ) / 4 * Real.log 2 := by
  unfold subpowerKubiliusSquareCutoff
  change Real.log (u ^ D * 2 ^ ((j : ℝ) / 4)) = _
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hu _))
      (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)),
    Real.log_rpow hu, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

noncomputable def subpowerKubiliusLossA (D : ℝ) : ℝ :=
  (D + 2) / Real.log 2

noncomputable def subpowerKubiliusLossB (A : ℝ) : ℝ :=
  max 0 ((-Real.log A + 2 * Real.log 4) / Real.log 2 + Real.log 2 +
    Erdos67.PrimeEstimates.mertensBound)

lemma subpowerKubiliusLossA_nonneg (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ subpowerKubiliusLossA D := by
  unfold subpowerKubiliusLossA
  positivity

lemma subpowerKubiliusLossB_nonneg (A : ℝ) :
    0 ≤ subpowerKubiliusLossB A := by
  exact le_max_left _ _

lemma subpowerBlockThreshold_after_squareCutoff_ge_lowered
    (c A D : ℝ) (hA : 0 < A) (ℓ j : ℕ) (hℓ : 6 ≤ ℓ) :
    kubiliusLoweredBarrier c (subpowerKubiliusLossA D) (subpowerKubiliusLossB A)
          (blockLogLog ℓ) + (j / 4 : ℕ) ≤
      blockLogLog ℓ * blockSigma c (blockLogLog ℓ) +
          (Real.log (subpowerBlockThreshold A ℓ j) -
              Real.log (subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j)) /
            Real.log 2 - Real.log 2 - Erdos67.PrimeEstimates.mertensBound := by
  let u : ℝ := blockLogLog ℓ
  have hu4 : ((ℓ : ℝ) + 2) / 4 ≤ u := by
    simpa only [u] using blockLogLog_ge_quarter_add ℓ hℓ
  have hu : 0 < u := by
    have : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4 := by positivity
    linarith
  have halloc : -(2 * Real.log u + 2 * Real.log 4) ≤
      Real.log (blockAllocation ℓ) := by
    simpa only [u] using log_blockAllocation_ge ℓ hℓ
  have hshift : ((j / 4 : ℕ) : ℝ) ≤ (j : ℝ) / 4 := Nat.cast_div_le
  have hB :
      (-Real.log A + 2 * Real.log 4) / Real.log 2 + Real.log 2 +
          Erdos67.PrimeEstimates.mertensBound ≤ subpowerKubiliusLossB A :=
    le_max_right _ _
  rw [log_subpowerBlockThreshold A hA,
    log_subpowerKubiliusSquareCutoff D u j hu]
  change kubiliusLoweredBarrier c (subpowerKubiliusLossA D)
      (subpowerKubiliusLossB A) u + (j / 4 : ℕ) ≤
    u * blockSigma c u +
          (Real.log A + Real.log (blockAllocation ℓ) + (j : ℝ) / 2 * Real.log 2 -
              (D * Real.log u + (j : ℝ) / 4 * Real.log 2)) /
            Real.log 2 - Real.log 2 - Erdos67.PrimeEstimates.mertensBound
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hactual :
      u * blockSigma c u +
          (Real.log A + Real.log (blockAllocation ℓ) + (j : ℝ) / 2 * Real.log 2 -
              (D * Real.log u + (j : ℝ) / 4 * Real.log 2)) /
            Real.log 2 - Real.log 2 - Erdos67.PrimeEstimates.mertensBound =
        u * blockSigma c u +
          (Real.log A + Real.log (blockAllocation ℓ) - D * Real.log u) /
            Real.log 2 + (j : ℝ) / 4 - Real.log 2 -
              Erdos67.PrimeEstimates.mertensBound := by
    field_simp [ne_of_gt hlog2]
    ring
  rw [hactual]
  unfold kubiliusLoweredBarrier subpowerKubiliusLossA
  rw [div_eq_mul_inv]
  rw [div_eq_mul_inv] at hB
  have hinv : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlog2
  have halloc' := mul_le_mul_of_nonneg_right halloc hinv.le
  ring_nf at halloc' hB ⊢
  linarith

open Classical in
/-- A large weighted divisor block, with the square-divisor cutoff allocated polynomially in the
log-log coordinate and geometrically in the shift, forces either the corresponding square-divisor
exception or a crossing of the lowered Kubilius barrier.  A quarter of the original half-power
shift survives, rounded down to an integer threshold. -/
lemma subpowerWeightedDivisorBlockMass_large_imp_square_or_kubiliusLowered
    (c A D : ℝ) (hc : 0 ≤ c) (hA : 0 < A) (ℓ n y j : ℕ) (hℓ : 6 ≤ ℓ)
    (hlog : 1 ≤ blockLogLog ℓ) (hy : dyadicExpCutoff (ℓ + 1) ≤ y)
    (hmass : subpowerBlockThreshold A ℓ j <
      weightedDivisorBlockMass (subpowerWeight c) ℓ n) :
    subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j < squareDivisorCount n ∨
      kubiliusLoweredBarrier c (subpowerKubiliusLossA D) (subpowerKubiliusLossB A)
            (blockLogLog ℓ) + (j / 4 : ℕ) <
        centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ))
          (n.primeFactors.filter (fun p => p ≤ y))
            (primesUpTo (dyadicExpCutoff (ℓ + 1))) := by
  have hu4 : ((ℓ : ℝ) + 2) / 4 ≤ blockLogLog ℓ :=
    blockLogLog_ge_quarter_add ℓ hℓ
  have hu : 0 < blockLogLog ℓ := by
    have : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4 := by positivity
    linarith
  have hR := subpowerBlockThreshold_pos A hA ℓ j
  have hU := subpowerKubiliusSquareCutoff_pos D (blockLogLog ℓ) j hu
  rcases subpowerWeightedDivisorBlockMass_large_imp_square_or_centered_sum_gt
      c hc ℓ n y (by omega) hlog hy
        (subpowerBlockThreshold A ℓ j)
        (subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j) hR hU hmass with
    hsq | hwalk
  · exact Or.inl hsq
  · exact Or.inr ((subpowerBlockThreshold_after_squareCutoff_ge_lowered
      c A D hA ℓ j hℓ).trans_lt hwalk)

noncomputable def subpowerSquareShiftConstant : ℝ :=
  (1 - Real.rpow 2 (-(1 : ℝ) / 4))⁻¹

lemma subpowerSquareShiftConstant_pos : 0 < subpowerSquareShiftConstant := by
  unfold subpowerSquareShiftConstant
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

lemma one_div_subpowerKubiliusSquareCutoff
    (D u : ℝ) (j : ℕ) (hu : 0 < u) :
    1 / subpowerKubiliusSquareCutoff D u j =
      Real.rpow u (-D) * (Real.rpow 2 (-(1 : ℝ) / 4)) ^ j := by
  unfold subpowerKubiliusSquareCutoff
  rw [one_div, mul_inv]
  change (u ^ D)⁻¹ * (2 ^ ((j : ℝ) / 4))⁻¹ = _
  rw [← Real.rpow_neg hu.le, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [show -((j : ℝ) / 4) = (-(1 : ℝ) / 4) * j by ring]
  exact Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) _ j

lemma sum_one_div_subpowerKubiliusSquareCutoff_le
    (D u : ℝ) (hu : 0 < u) (J : ℕ) :
    (∑ j ∈ Finset.range J, 1 / subpowerKubiliusSquareCutoff D u j) ≤
      Real.rpow u (-D) * subpowerSquareShiftConstant := by
  let q : ℝ := Real.rpow 2 (-(1 : ℝ) / 4)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgeom : (∑ j ∈ Finset.range J, q ^ j) ≤ ∑' j : ℕ, q ^ j :=
    (hasSum_geometric_of_lt_one hq0 hq1).summable.sum_le_tsum
      (Finset.range J) (fun j _ ↦ pow_nonneg hq0 j)
  calc
    (∑ j ∈ Finset.range J, 1 / subpowerKubiliusSquareCutoff D u j) =
        Real.rpow u (-D) * ∑ j ∈ Finset.range J, q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [q] using one_div_subpowerKubiliusSquareCutoff D u j hu
    _ ≤ Real.rpow u (-D) * ∑' j : ℕ, q ^ j := by
      exact mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hu.le _)
    _ = Real.rpow u (-D) * subpowerSquareShiftConstant := by
      rw [tsum_geometric_of_lt_one hq0 hq1]
      rfl

lemma sum_squareDivisorCount_large_card_subpowerCutoff_le
    (D u : ℝ) (hu : 0 < u) (T J : ℕ) :
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n =>
          subpowerKubiliusSquareCutoff D u j < squareDivisorCount n)).card : ℝ)) ≤
      T * squareDivisorMomentConstant * Real.rpow u (-D) *
        subpowerSquareShiftConstant := by
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n =>
          subpowerKubiliusSquareCutoff D u j < squareDivisorCount n)).card : ℝ)) ≤
        ∑ j ∈ Finset.range J,
          (T * squareDivisorMomentConstant /
            subpowerKubiliusSquareCutoff D u j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact squareDivisorCount_large_card_le T _
        (subpowerKubiliusSquareCutoff_pos D u j hu)
    _ = (T * squareDivisorMomentConstant) *
          ∑ j ∈ Finset.range J, 1 / subpowerKubiliusSquareCutoff D u j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (T * squareDivisorMomentConstant) *
          (Real.rpow u (-D) * subpowerSquareShiftConstant) := by
      exact mul_le_mul_of_nonneg_left
        (sum_one_div_subpowerKubiliusSquareCutoff_le D u hu J)
        (mul_nonneg (by positivity) squareDivisorMomentConstant_nonneg)
    _ = _ := by ring

/-! ### Geometric level grouping and arithmetic transfer -/

/-- Grouping the surviving integer shifts by `j / 4` costs at most four copies of each
threshold. -/
lemma sum_comp_nat_div_four_le (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (J : ℕ) :
    (∑ j ∈ Finset.range J, f (j / 4)) ≤
      4 * ∑ q ∈ Finset.range ((J + 3) / 4), f q := by
  let Q := (J + 3) / 4
  have hJ : J ≤ 4 * Q := by
    dsimp [Q]
    omega
  have hmap : ∀ j ∈ Finset.range J, j / 4 ∈ Finset.range Q := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f]
  calc
    (∑ q ∈ Finset.range Q, ∑ j ∈ Finset.range J with j / 4 = q, f q) ≤
        ∑ q ∈ Finset.range Q, 4 * f q := by
      apply Finset.sum_le_sum
      intro q hq
      have hsubset : (Finset.range J).filter (fun j => j / 4 = q) ⊆
          Finset.Ico (4 * q) (4 * q + 4) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_Ico]
        omega
      have hcard : ((Finset.range J).filter (fun j => j / 4 = q)).card ≤ 4 := by
        calc
          _ ≤ (Finset.Ico (4 * q) (4 * q + 4)).card := Finset.card_le_card hsubset
          _ = 4 := by simp
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf q)
    _ = 4 * ∑ q ∈ Finset.range Q, f q := by rw [Finset.mul_sum]

/-- The ideal square-root barrier is increasing once the log-log coordinate is at least one. -/
lemma idealBarrier_mono {c u v : ℝ} (hc : 0 ≤ c) (hu : 1 ≤ u) (huv : u ≤ v) :
    u * blockSigma c u ≤ v * blockSigma c v := by
  have hv : 1 ≤ v := hu.trans huv
  rw [← sqrt_mul_eq_mul_blockSigma c u hc hu,
    ← sqrt_mul_eq_mul_blockSigma c v hc hv]
  apply Real.sqrt_le_sqrt
  have hlog : Real.log u ≤ Real.log v := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (zero_lt_one.trans_le hu))
    (Set.mem_Ioi.mpr (zero_lt_one.trans_le hv)) huv
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu
  gcongr

/-- A coefficient strictly between `1` and the packet coefficient, reserved for the model
estimate after grouping arithmetic levels. -/
noncomputable def subpowerKubiliusModelCoefficient (c : ℝ) : ℝ :=
  kubiliusBlockRatio c

/-- Ratio used to group arithmetic levels.  It is chosen strictly below the variance ratio in the
model estimate, leaving room for the fixed Mertens and right-endpoint losses. -/
noncomputable def subpowerKubiliusGroupingRatio (c : ℝ) : ℝ :=
  kubiliusBlockRatio (kubiliusBlockRatio (subpowerKubiliusModelCoefficient c))

lemma one_lt_subpowerKubiliusModelCoefficient {c : ℝ} (hc : 1 < c) :
    1 < subpowerKubiliusModelCoefficient c :=
  one_lt_kubiliusBlockRatio hc

lemma subpowerKubiliusModelCoefficient_lt {c : ℝ} (hc : 1 < c) :
    subpowerKubiliusModelCoefficient c < c :=
  kubiliusBlockRatio_lt hc

lemma one_lt_subpowerKubiliusGroupingRatio {c : ℝ} (hc : 1 < c) :
    1 < subpowerKubiliusGroupingRatio c := by
  unfold subpowerKubiliusGroupingRatio
  exact one_lt_kubiliusBlockRatio
    (one_lt_kubiliusBlockRatio (one_lt_subpowerKubiliusModelCoefficient hc))

lemma subpowerKubiliusGroupingRatio_lt_varianceRatio {c : ℝ} (hc : 1 < c) :
    subpowerKubiliusGroupingRatio c <
      kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) := by
  unfold subpowerKubiliusGroupingRatio
  exact kubiliusBlockRatio_lt
    (one_lt_kubiliusBlockRatio (one_lt_subpowerKubiliusModelCoefficient hc))

/-- Eventually the gap between the arithmetic grouping ratio and the model variance ratio absorbs
any fixed additive endpoint loss.  This is the quantitative reason for using two distinct ratios
in the global partition. -/
theorem eventually_grouping_pow_succ_add_le_varianceRatio_mul_pow
    {c : ℝ} (hc : 1 < c) (E : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      (subpowerKubiliusGroupingRatio c : ℝ) ^ (k + 1) + E ≤
        kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
          (subpowerKubiliusGroupingRatio c : ℝ) ^ k := by
  let q : ℝ := subpowerKubiliusGroupingRatio c
  let r : ℝ := kubiliusBlockRatio (subpowerKubiliusModelCoefficient c)
  have hq : 1 < q := one_lt_subpowerKubiliusGroupingRatio hc
  have hqr : q < r := subpowerKubiliusGroupingRatio_lt_varianceRatio hc
  have hgap : 0 < r - q := sub_pos.mpr hqr
  have hpow : Tendsto (fun k : ℕ ↦ (q : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq
  filter_upwards [hpow.eventually_ge_atTop (E / (r - q))] with k hk
  have hE : E ≤ (r - q) * q ^ k := by
    calc
      E = (r - q) * (E / (r - q)) := by field_simp
      _ ≤ (r - q) * q ^ k := mul_le_mul_of_nonneg_left hk hgap.le
  dsimp only [q, r] at hE ⊢
  rw [pow_succ]
  linarith

/-- Every sufficiently large log-log coordinate lies in a grouping interval whose left endpoint
is a valid model anchor and whose right endpoint, including any prescribed fixed loss, fits under
the model variance cap. -/
theorem eventually_exists_grouping_pow_le_and_add_le_varianceRatio_mul_pow
    {c : ℝ} (hc : 1 < c) (E : ℝ) :
    ∀ᶠ u : ℝ in atTop, ∃ k : ℕ,
      (subpowerKubiliusGroupingRatio c : ℝ) ^ k ≤ u ∧
        u + E ≤ kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
          (subpowerKubiliusGroupingRatio c : ℝ) ^ k := by
  let q : ℝ := subpowerKubiliusGroupingRatio c
  have hq : 1 < q := one_lt_subpowerKubiliusGroupingRatio hc
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (eventually_grouping_pow_succ_add_le_varianceRatio_mul_pow hc E)
  filter_upwards [eventually_ge_atTop (q ^ K)] with u hu
  have hu1 : 1 ≤ u := (one_le_pow₀ hq.le).trans hu
  obtain ⟨k, hku, huk⟩ := exists_nat_pow_near hu1 hq
  have hKk : K ≤ k := by
    by_contra hnot
    have hkK : k + 1 ≤ K := by omega
    have hp : q ^ (k + 1) ≤ q ^ K := pow_le_pow_right₀ hq.le hkK
    linarith
  refine ⟨k, hku, ?_⟩
  have hendpoint := hK k hKk
  have huend : u + E ≤
      (subpowerKubiliusGroupingRatio c : ℝ) ^ (k + 1) + E := by
    linarith
  exact huend.trans hendpoint

/-- Arithmetic-level specialization of the slack partition: the next dyadic endpoint and the
Mertens constant both fit below the model variance cap of the chosen geometric anchor. -/
theorem eventually_exists_subpowerKubiliusGroupingIndex
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ ℓ : ℕ in atTop, ∃ k : ℕ,
      (subpowerKubiliusGroupingRatio c : ℝ) ^ k ≤ blockLogLog ℓ ∧
        blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            (subpowerKubiliusGroupingRatio c : ℝ) ^ k := by
  have h := tendsto_blockLogLog_atTop.eventually
    (eventually_exists_grouping_pow_le_and_add_le_varianceRatio_mul_pow hc
      (Real.log 2 + Erdos67.PrimeEstimates.mertensBound))
  filter_upwards [h] with ℓ hℓ
  obtain ⟨k, hkleft, hkright⟩ := hℓ
  refine ⟨k, hkleft, ?_⟩
  rw [blockLogLog_succ]
  linarith

/-- Eventually, every arithmetic level above a geometric anchor has its actual lowered barrier
above the model barrier at that anchor. -/
theorem eventually_kubiliusLevelBarrier_ge_anchor
    {c : ℝ} (hc : 1 < c) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ u : ℝ in atTop, ∀ u₀ : ℝ, 1 ≤ u₀ → u₀ ≤ u →
      kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c) A B u₀ ≤
        kubiliusLoweredBarrier c A B u := by
  have hc₀ : 0 < subpowerKubiliusModelCoefficient c :=
    zero_lt_one.trans (one_lt_subpowerKubiliusModelCoefficient hc)
  have hcompare := eventually_idealBarrier_le_kubiliusLoweredBarrier
    hc₀ (by linarith : 0 < c) (subpowerKubiliusModelCoefficient_lt hc) A B hB
  filter_upwards [hcompare] with u hu
  intro u₀ hu₀ hu₀u
  calc
    kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c) A B u₀ ≤
        u₀ * blockSigma (subpowerKubiliusModelCoefficient c) u₀ := by
      unfold kubiliusLoweredBarrier
      have hlog : 0 ≤ Real.log u₀ := Real.log_nonneg hu₀
      nlinarith [mul_nonneg hA hlog]
    _ ≤ u * blockSigma (subpowerKubiliusModelCoefficient c) u :=
      idealBarrier_mono hc₀.le hu₀ hu₀u
    _ ≤ kubiliusLoweredBarrier c A B u := hu

/-- The barrier comparison specialized to the arithmetic log-log coordinates. -/
theorem eventually_kubiliusLevelBarrier_ge_anchor_blockLogLog
    {c : ℝ} (hc : 1 < c) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ ℓ : ℕ in atTop, ∀ u₀ : ℝ, 1 ≤ u₀ → u₀ ≤ blockLogLog ℓ →
      kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c) A B u₀ ≤
        kubiliusLoweredBarrier c A B (blockLogLog ℓ) :=
  tendsto_blockLogLog_atTop.eventually
    (eventually_kubiliusLevelBarrier_ge_anchor hc A B hA hB)

/-! ### The finite slack-aware level partition -/

/-- Canonical choice of the geometric schedule index attached to an arithmetic level.  The junk
value `0` is used before the eventual range; `subpowerKubiliusGroupingIndex_spec` is the only
interface used once a witness exists. -/
noncomputable def subpowerKubiliusGroupingIndex (c : ℝ) (ℓ : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ,
        (subpowerKubiliusGroupingRatio c : ℝ) ^ k ≤ blockLogLog ℓ ∧
          blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
            kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
              (subpowerKubiliusGroupingRatio c : ℝ) ^ k then
      Classical.choose h
    else 0

theorem subpowerKubiliusGroupingIndex_spec {c : ℝ} {ℓ : ℕ}
    (h : ∃ k : ℕ,
      (subpowerKubiliusGroupingRatio c : ℝ) ^ k ≤ blockLogLog ℓ ∧
        blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            (subpowerKubiliusGroupingRatio c : ℝ) ^ k) :
    (subpowerKubiliusGroupingRatio c : ℝ) ^
          subpowerKubiliusGroupingIndex c ℓ ≤ blockLogLog ℓ ∧
      blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
        kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
          (subpowerKubiliusGroupingRatio c : ℝ) ^
            subpowerKubiliusGroupingIndex c ℓ := by
  rw [subpowerKubiliusGroupingIndex, dif_pos h]
  exact Classical.choose_spec h

theorem eventually_subpowerKubiliusGroupingIndex_spec
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ ℓ : ℕ in atTop,
      (subpowerKubiliusGroupingRatio c : ℝ) ^
            subpowerKubiliusGroupingIndex c ℓ ≤ blockLogLog ℓ ∧
        blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            (subpowerKubiliusGroupingRatio c : ℝ) ^
              subpowerKubiliusGroupingIndex c ℓ := by
  filter_upwards [eventually_exists_subpowerKubiliusGroupingIndex hc] with ℓ hℓ
  exact subpowerKubiliusGroupingIndex_spec hℓ

/-- The canonical grouping indices tend to infinity.  This is the bridge from a late arithmetic
level interval to the tail index supplied by the summable geometric model estimate. -/
theorem eventually_le_subpowerKubiliusGroupingIndex
    {c : ℝ} (hc : 1 < c) (K : ℕ) :
    ∀ᶠ ℓ : ℕ in atTop, K ≤ subpowerKubiliusGroupingIndex c ℓ := by
  let q : ℝ := subpowerKubiliusGroupingRatio c
  let r : ℝ := kubiliusBlockRatio (subpowerKubiliusModelCoefficient c)
  have hq : 1 < q := one_lt_subpowerKubiliusGroupingRatio hc
  have hr : 0 ≤ r := by
    dsimp only [r]
    exact zero_le_one.trans (one_lt_kubiliusBlockRatio
      (one_lt_subpowerKubiliusModelCoefficient hc)).le
  have hbig := tendsto_blockLogLog_atTop.eventually_gt_atTop
    (r * q ^ K - Erdos67.PrimeEstimates.mertensBound)
  filter_upwards [eventually_subpowerKubiliusGroupingIndex_spec hc, hbig] with ℓ hi hlarge
  by_contra hnot
  have hindexK : subpowerKubiliusGroupingIndex c ℓ ≤ K := by omega
  have hpow : q ^ subpowerKubiliusGroupingIndex c ℓ ≤ q ^ K :=
    pow_le_pow_right₀ hq.le hindexK
  have hrpow : r * q ^ subpowerKubiliusGroupingIndex c ℓ ≤ r * q ^ K :=
    mul_le_mul_of_nonneg_left hpow hr
  dsimp only [q, r] at hi hlarge hrpow
  rw [blockLogLog_succ] at hi
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The finite interval of levels that can arise from the allocated divisor-tail cover. -/
def subpowerKubiliusLevelInterval (L T : ℕ) : Finset ℕ :=
  Finset.Ico L (L + T)

/-- Levels whose next dyadic endpoint lies below the common usable prime cutoff `Y`. -/
def subpowerKubiliusOrdinaryLevels (L T Y : ℕ) : Finset ℕ :=
  (subpowerKubiliusLevelInterval L T).filter
    (fun ℓ => dyadicExpCutoff (ℓ + 1) ≤ Y)

/-- The complementary top band, to be controlled by the one-level estimate rather than by
`KubiliusTV`. -/
def subpowerKubiliusExceptionalLevels (L T Y : ℕ) : Finset ℕ :=
  (subpowerKubiliusLevelInterval L T).filter
    (fun ℓ => Y < dyadicExpCutoff (ℓ + 1))

/-- Fibers of the ordinary levels under the canonical geometric grouping index. -/
noncomputable def subpowerKubiliusLevelGroups
    (c : ℝ) (L T Y : ℕ) : Finset (Finset ℕ) :=
  let levels := subpowerKubiliusOrdinaryLevels L T Y
  (levels.image (subpowerKubiliusGroupingIndex c)).image
    (fun k => levels.filter (fun ℓ => subpowerKubiliusGroupingIndex c ℓ = k))

/-- Terminal arithmetic prime cutoff of a level group.  Groups produced above are nonempty, while
the definition remains total by using the `sup` junk value on the empty finset. -/
def subpowerKubiliusGroupCutoff (s : Finset ℕ) : ℕ :=
  dyadicExpCutoff (s.sup id + 1)

/-- Geometric model anchor of a level group. -/
noncomputable def subpowerKubiliusGroupAnchor (c : ℝ) (s : Finset ℕ) : ℝ :=
  (subpowerKubiliusGroupingRatio c : ℝ) ^
    subpowerKubiliusGroupingIndex c (s.sup id)

@[simp] lemma mem_subpowerKubiliusLevelInterval {L T ℓ : ℕ} :
    ℓ ∈ subpowerKubiliusLevelInterval L T ↔ L ≤ ℓ ∧ ℓ < L + T := by
  simp [subpowerKubiliusLevelInterval]

@[simp] lemma mem_subpowerKubiliusOrdinaryLevels {L T Y ℓ : ℕ} :
    ℓ ∈ subpowerKubiliusOrdinaryLevels L T Y ↔
      L ≤ ℓ ∧ ℓ < L + T ∧ dyadicExpCutoff (ℓ + 1) ≤ Y := by
  simp [subpowerKubiliusOrdinaryLevels, and_assoc]

@[simp] lemma mem_subpowerKubiliusExceptionalLevels {L T Y ℓ : ℕ} :
    ℓ ∈ subpowerKubiliusExceptionalLevels L T Y ↔
      L ≤ ℓ ∧ ℓ < L + T ∧ Y < dyadicExpCutoff (ℓ + 1) := by
  simp [subpowerKubiliusExceptionalLevels, and_assoc]

lemma dyadicExpCutoff_mono {a b : ℕ} (hab : a ≤ b) :
    dyadicExpCutoff a ≤ dyadicExpCutoff b := by
  unfold dyadicExpCutoff
  exact Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by omega) hab)

open Classical in
lemma subpowerKubiliusLevelGroup_nonempty {c : ℝ} {L T Y : ℕ} {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y) : s.Nonempty := by
  rw [subpowerKubiliusLevelGroups] at hs
  rcases Finset.mem_image.mp hs with ⟨k, hk, rfl⟩
  rcases Finset.mem_image.mp hk with ⟨ℓ, hℓ, rfl⟩
  exact ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, rfl⟩⟩

open Classical in
lemma subpowerKubiliusLevelGroup_subset {c : ℝ} {L T Y : ℕ} {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y) :
    s ⊆ subpowerKubiliusOrdinaryLevels L T Y := by
  rw [subpowerKubiliusLevelGroups] at hs
  rcases Finset.mem_image.mp hs with ⟨k, _hk, rfl⟩
  intro ℓ hℓ
  exact (Finset.mem_filter.mp hℓ).1

open Classical in
lemma subpowerKubiliusLevelGroup_index_eq {c : ℝ} {L T Y : ℕ} {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y) {ℓ : ℕ} (hℓ : ℓ ∈ s) :
    subpowerKubiliusGroupingIndex c ℓ =
      subpowerKubiliusGroupingIndex c (s.sup id) := by
  rw [subpowerKubiliusLevelGroups] at hs
  rcases Finset.mem_image.mp hs with ⟨k, _hk, rfl⟩
  have hℓk := (Finset.mem_filter.mp hℓ).2
  have hne :
      (subpowerKubiliusOrdinaryLevels L T Y).filter
          (fun m => subpowerKubiliusGroupingIndex c m = k) |>.Nonempty :=
    ⟨ℓ, hℓ⟩
  have hsupmem :
      ((subpowerKubiliusOrdinaryLevels L T Y).filter
          (fun m => subpowerKubiliusGroupingIndex c m = k)).sup id ∈
        (subpowerKubiliusOrdinaryLevels L T Y).filter
          (fun m => subpowerKubiliusGroupingIndex c m = k) := by
    have hsup :
        ((subpowerKubiliusOrdinaryLevels L T Y).filter
            (fun m => subpowerKubiliusGroupingIndex c m = k)).sup id =
          ((subpowerKubiliusOrdinaryLevels L T Y).filter
            (fun m => subpowerKubiliusGroupingIndex c m = k)).max' hne := by
      rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
    rw [hsup]
    exact Finset.max'_mem _ hne
  exact hℓk.trans (Finset.mem_filter.mp hsupmem).2.symm

open Classical in
/-- A produced group is exactly the full fiber of its terminal level's grouping index. -/
lemma mem_subpowerKubiliusLevelGroup_iff
    {c : ℝ} {L T Y : ℕ} {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y) {ℓ : ℕ} :
    ℓ ∈ s ↔ ℓ ∈ subpowerKubiliusOrdinaryLevels L T Y ∧
      subpowerKubiliusGroupingIndex c ℓ =
        subpowerKubiliusGroupingIndex c (s.sup id) := by
  constructor
  · intro hℓ
    exact ⟨subpowerKubiliusLevelGroup_subset hs hℓ,
      subpowerKubiliusLevelGroup_index_eq hs hℓ⟩
  · rintro ⟨hord, hindex⟩
    have hs₀ := hs
    rw [subpowerKubiliusLevelGroups] at hs
    rcases Finset.mem_image.mp hs with ⟨k, hk, hks⟩
    rcases Finset.mem_image.mp hk with ⟨m, hm, hmk⟩
    have hms : m ∈ s := by
      rw [← hks]
      exact Finset.mem_filter.mpr ⟨hm, hmk⟩
    have hmsup := subpowerKubiliusLevelGroup_index_eq hs₀ hms
    have hksup : k = subpowerKubiliusGroupingIndex c (s.sup id) :=
      hmk.symm.trans hmsup
    rw [← hks]
    exact Finset.mem_filter.mpr ⟨hord, hindex.trans hksup.symm⟩

open Classical in
/-- Distinct nonempty fibers have distinct geometric schedule indices. -/
lemma subpowerKubiliusLevelGroup_eq_of_index_eq
    {c : ℝ} {L T Y : ℕ} {s t : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y)
    (ht : t ∈ subpowerKubiliusLevelGroups c L T Y)
    (hindex : subpowerKubiliusGroupingIndex c (s.sup id) =
      subpowerKubiliusGroupingIndex c (t.sup id)) : s = t := by
  ext ℓ
  rw [mem_subpowerKubiliusLevelGroup_iff hs,
    mem_subpowerKubiliusLevelGroup_iff ht, hindex]

open Classical in
theorem subpowerKubiliusLevelGroup_index_injOn
    (c : ℝ) (L T Y : ℕ) :
    Set.InjOn (fun s : Finset ℕ =>
      subpowerKubiliusGroupingIndex c (s.sup id))
        (subpowerKubiliusLevelGroups c L T Y : Set (Finset ℕ)) := by
  intro s hs t ht hindex
  exact subpowerKubiliusLevelGroup_eq_of_index_eq hs ht hindex

open Classical in
/-- The canonical level groups are pairwise disjoint.  This is the bookkeeping fact that lets the
square-divisor contribution be summed over arithmetic levels rather than over geometric fibers. -/
theorem subpowerKubiliusLevelGroups_pairwiseDisjoint
    (c : ℝ) (L T Y : ℕ) :
    Set.PairwiseDisjoint (subpowerKubiliusLevelGroups c L T Y : Set (Finset ℕ))
      (fun s ↦ s) := by
  intro s hs t ht hst
  change Disjoint s t
  rw [Finset.disjoint_left]
  intro ℓ hℓs hℓt
  apply hst
  apply subpowerKubiliusLevelGroup_eq_of_index_eq hs ht
  exact (subpowerKubiliusLevelGroup_index_eq hs hℓs).symm.trans
    (subpowerKubiliusLevelGroup_index_eq ht hℓt)

open Classical in
/-- The union of the canonical fibers is exactly the set of ordinary arithmetic levels.  In
particular this records the empty and truncated cases without an auxiliary nonemptiness
hypothesis. -/
theorem subpowerKubiliusLevelGroups_biUnion
    (c : ℝ) (L T Y : ℕ) :
    (subpowerKubiliusLevelGroups c L T Y).biUnion (fun s ↦ s) =
      subpowerKubiliusOrdinaryLevels L T Y := by
  ext ℓ
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hℓs⟩
    exact subpowerKubiliusLevelGroup_subset hs hℓs
  · intro hℓ
    let s := (subpowerKubiliusOrdinaryLevels L T Y).filter
      (fun m ↦ subpowerKubiliusGroupingIndex c m =
        subpowerKubiliusGroupingIndex c ℓ)
    refine ⟨s, ?_, ?_⟩
    · unfold subpowerKubiliusLevelGroups
      apply Finset.mem_image.mpr
      refine ⟨subpowerKubiliusGroupingIndex c ℓ, ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hℓ, rfl⟩

open Classical in
lemma subpowerKubiliusLevelGroup_sup_mem {c : ℝ} {L T Y : ℕ} {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y) : s.sup id ∈ s := by
  have hne := subpowerKubiliusLevelGroup_nonempty hs
  have hsup : s.sup id = s.max' hne := by
    rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
  rw [hsup]
  exact Finset.max'_mem s hne

open Classical in
lemma subpowerKubiliusLevel_le_group_sup {s : Finset ℕ} {ℓ : ℕ} (hℓ : ℓ ∈ s) :
    ℓ ≤ s.sup id := by
  exact Finset.le_sup (f := id) hℓ

open Classical in
lemma subpowerKubiliusLevel_cutoff_le_groupCutoff
    {s : Finset ℕ} {ℓ : ℕ} (hℓ : ℓ ∈ s) :
    dyadicExpCutoff (ℓ + 1) ≤ subpowerKubiliusGroupCutoff s := by
  unfold subpowerKubiliusGroupCutoff
  exact dyadicExpCutoff_mono (Nat.add_le_add_right
    (subpowerKubiliusLevel_le_group_sup hℓ) 1)

open Classical in
lemma subpowerKubiliusGroupCutoff_le {c : ℝ} {L T Y : ℕ} {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T Y) :
    subpowerKubiliusGroupCutoff s ≤ Y := by
  have hsupmem := subpowerKubiliusLevelGroup_sup_mem hs
  have hord := subpowerKubiliusLevelGroup_subset hs hsupmem
  exact (mem_subpowerKubiliusOrdinaryLevels.mp hord).2.2

open Classical in
/-- The ordinary fibers together with the explicit top band cover every level in the allocated
finite interval. -/
theorem subpowerKubiliusLevelGroups_cover
    (c : ℝ) (L T Y : ℕ) {i : ℕ} (hi : i ∈ Finset.range T) :
    L + i ∈ subpowerKubiliusExceptionalLevels L T Y ∨
      ∃ s ∈ subpowerKubiliusLevelGroups c L T Y, L + i ∈ s := by
  have hiT : i < T := Finset.mem_range.mp hi
  by_cases hcut : dyadicExpCutoff (L + i + 1) ≤ Y
  · right
    have hord : L + i ∈ subpowerKubiliusOrdinaryLevels L T Y := by
      apply mem_subpowerKubiliusOrdinaryLevels.mpr
      exact ⟨by omega, by omega, hcut⟩
    let s := (subpowerKubiliusOrdinaryLevels L T Y).filter
      (fun ℓ => subpowerKubiliusGroupingIndex c ℓ =
        subpowerKubiliusGroupingIndex c (L + i))
    refine ⟨s, ?_, ?_⟩
    · unfold subpowerKubiliusLevelGroups
      apply Finset.mem_image.mpr
      refine ⟨subpowerKubiliusGroupingIndex c (L + i), ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨L + i, hord, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hord, rfl⟩
  · left
    apply mem_subpowerKubiliusExceptionalLevels.mpr
    exact ⟨by omega, by omega, by omega⟩

open Classical in
/-- For all sufficiently late starting levels, the canonical finite fibers satisfy every
levelwise hypothesis of the grouped Kubilius transfer.  Each group is charged at its largest
arithmetic cutoff, while its model walk starts at the common geometric anchor.  The final clause
is exactly the variance-cap hypothesis required by the uniform model tail theorem. -/
theorem exists_subpowerKubiliusLevelGroups_data
    {c : ℝ} (hc : 1 < c) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (K : ℕ) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T Y : ℕ, Y ≤ T →
      (∀ i ∈ Finset.range T,
        L + i ∈ subpowerKubiliusExceptionalLevels L T Y ∨
          ∃ s ∈ subpowerKubiliusLevelGroups c L T Y, L + i ∈ s) ∧
      (∀ s ∈ subpowerKubiliusLevelGroups c L T Y, ∀ ℓ ∈ s,
        6 ≤ ℓ ∧ 1 ≤ blockLogLog ℓ ∧
          dyadicExpCutoff (ℓ + 1) ≤ subpowerKubiliusGroupCutoff s ∧
          kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c) A B
              (subpowerKubiliusGroupAnchor c s) ≤
            kubiliusLoweredBarrier c A B (blockLogLog ℓ)) ∧
      (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
        2 ≤ subpowerKubiliusGroupCutoff s ∧
          subpowerKubiliusGroupCutoff s ≤ T) ∧
      (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
        Real.log (Real.log (subpowerKubiliusGroupCutoff s : ℝ)) +
            Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            subpowerKubiliusGroupAnchor c s) ∧
      (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
        K ≤ subpowerKubiliusGroupingIndex c (s.sup id)) := by
  have hindex := eventually_subpowerKubiliusGroupingIndex_spec hc
  have hkey := eventually_le_subpowerKubiliusGroupingIndex hc K
  have hbarrier := eventually_kubiliusLevelBarrier_ge_anchor_blockLogLog
    hc A B hA hB
  have hlog : ∀ᶠ ℓ : ℕ in atTop, 1 ≤ blockLogLog ℓ :=
    tendsto_blockLogLog_atTop.eventually_ge_atTop 1
  have hall : ∀ᶠ ℓ : ℕ in atTop,
      ((subpowerKubiliusGroupingRatio c : ℝ) ^
            subpowerKubiliusGroupingIndex c ℓ ≤ blockLogLog ℓ ∧
        blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            (subpowerKubiliusGroupingRatio c : ℝ) ^
              subpowerKubiliusGroupingIndex c ℓ) ∧
      (∀ u₀ : ℝ, 1 ≤ u₀ → u₀ ≤ blockLogLog ℓ →
        kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c) A B u₀ ≤
          kubiliusLoweredBarrier c A B (blockLogLog ℓ)) ∧
      1 ≤ blockLogLog ℓ ∧ 6 ≤ ℓ ∧
        K ≤ subpowerKubiliusGroupingIndex c ℓ := by
    filter_upwards [hindex, hbarrier, hlog, eventually_ge_atTop 6, hkey]
      with ℓ hi hb hl h6 hk
    exact ⟨hi, hb, hl, h6, hk⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hall
  have hL₀data := hL₀ L₀ le_rfl
  refine ⟨L₀, hL₀data.2.2.2.1, ?_⟩
  intro L hL T Y hYT
  have hlate : ∀ ℓ : ℕ, L ≤ ℓ →
      ((subpowerKubiliusGroupingRatio c : ℝ) ^
            subpowerKubiliusGroupingIndex c ℓ ≤ blockLogLog ℓ ∧
        blockLogLog (ℓ + 1) + Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            (subpowerKubiliusGroupingRatio c : ℝ) ^
              subpowerKubiliusGroupingIndex c ℓ) ∧
      (∀ u₀ : ℝ, 1 ≤ u₀ → u₀ ≤ blockLogLog ℓ →
        kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c) A B u₀ ≤
          kubiliusLoweredBarrier c A B (blockLogLog ℓ)) ∧
      1 ≤ blockLogLog ℓ ∧ 6 ≤ ℓ ∧
        K ≤ subpowerKubiliusGroupingIndex c ℓ := by
    intro ℓ hLℓ
    exact hL₀ ℓ (hL.trans hLℓ)
  refine ⟨fun i hi => subpowerKubiliusLevelGroups_cover c L T Y hi, ?_, ?_, ?_, ?_⟩
  · intro s hs ℓ hℓ
    have hord := subpowerKubiliusLevelGroup_subset hs hℓ
    have hLℓ := (mem_subpowerKubiliusOrdinaryLevels.mp hord).1
    have hd := hlate ℓ hLℓ
    have hindexEq := subpowerKubiliusLevelGroup_index_eq hs hℓ
    have hanchorOne : 1 ≤ subpowerKubiliusGroupAnchor c s := by
      unfold subpowerKubiliusGroupAnchor
      exact one_le_pow₀ (one_lt_subpowerKubiliusGroupingRatio hc).le
    have hanchorLe : subpowerKubiliusGroupAnchor c s ≤ blockLogLog ℓ := by
      unfold subpowerKubiliusGroupAnchor
      rw [← hindexEq]
      exact hd.1.1
    exact ⟨hd.2.2.2.1, hd.2.2.1,
      subpowerKubiliusLevel_cutoff_le_groupCutoff hℓ,
      hd.2.1 _ hanchorOne hanchorLe⟩
  · intro s hs
    exact ⟨dyadicExpCutoff_two_le _,
      (subpowerKubiliusGroupCutoff_le hs).trans hYT⟩
  · intro s hs
    have hsupmem := subpowerKubiliusLevelGroup_sup_mem hs
    have hord := subpowerKubiliusLevelGroup_subset hs hsupmem
    have hLsup := (mem_subpowerKubiliusOrdinaryLevels.mp hord).1
    have hspec := (hlate (s.sup id) hLsup).1
    simpa only [subpowerKubiliusGroupCutoff, subpowerKubiliusGroupAnchor,
      blockLogLog] using hspec.2
  · intro s hs
    have hsupmem := subpowerKubiliusLevelGroup_sup_mem hs
    have hord := subpowerKubiliusLevelGroup_subset hs hsupmem
    have hLsup := (mem_subpowerKubiliusOrdinaryLevels.mp hord).1
    exact (hlate (s.sup id) hLsup).2.2.2.2

open Classical in
/-- Every event has nonnegative mass in the finite Kubilius model. -/
lemma kubiliusMass_nonneg (y : ℕ) (E : Set (Finset ℕ)) :
    0 ≤ kubiliusMass y E := by
  have hmono := kubiliusMass_mono y (Set.empty_subset E)
  simpa [kubiliusMass] using hmono

open Classical in
/-- Integers in the averaging interval whose truncated prime-factor set belongs to `E`. -/
noncomputable def kubiliusArithmeticEventFinset
    (N y : ℕ) (E : Set (Finset ℕ)) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n =>
    n.primeFactors.filter (fun p => p ≤ y) ∈ E)

open Classical in
@[simp] lemma mem_kubiliusArithmeticEventFinset
    {N y n : ℕ} {E : Set (Finset ℕ)} :
    n ∈ kubiliusArithmeticEventFinset N y E ↔
      n ∈ Finset.Icc 1 N ∧ n.primeFactors.filter (fun p => p ≤ y) ∈ E := by
  unfold kubiliusArithmeticEventFinset
  exact Finset.mem_filter

/-- Cardinality wrapper that pins the decidability data of the arithmetic event. -/
noncomputable def kubiliusArithmeticEventCard
    (N y : ℕ) (E : Set (Finset ℕ)) : ℕ :=
  (kubiliusArithmeticEventFinset N y E).card

open Classical in
/-- `KubiliusTV` in terms of the named arithmetic-event cardinality. -/
theorem kubiliusTV_sum_arithmeticEventCard_div_le (hK : KubiliusTV) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y J : ℕ, 2 ≤ y → y ≤ N → ∀ E : ℕ → Set (Finset ℕ),
      (∑ j ∈ Finset.range J, (kubiliusArithmeticEventCard N y (E j) : ℝ) / N) ≤
        (∑ j ∈ Finset.range J, kubiliusMass y (E j)) +
          J * C * (Real.rpow (Real.log N / Real.log y)
            (-(Real.log N / Real.log y)) + Real.rpow N (-(1 / 2 : ℝ))) := by
  simpa only [kubiliusArithmeticEventCard, kubiliusArithmeticEventFinset] using
    kubiliusTV_sum_card_div_le hK

open Classical in
/-- Fixed-level arithmetic transfer.  After summing all original shifts, a large weighted
divisor block is bounded by the allocated square-divisor exception, four copies of the model
crossing mass at the geometric anchor, and the explicitly accumulated total-variation error. -/
theorem exists_subpowerBlock_large_cards_div_le_square_add_kubilius
    (hK : KubiliusTV) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c A D : ℝ) (ℓ y T J : ℕ) (u₀ : ℝ),
      0 ≤ c → 0 < A → 0 < T → 6 ≤ ℓ → 1 ≤ blockLogLog ℓ →
      dyadicExpCutoff (ℓ + 1) ≤ y → 2 ≤ y → y ≤ T →
      kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
          (subpowerKubiliusLossA D) (subpowerKubiliusLossB A) u₀ ≤
        kubiliusLoweredBarrier c (subpowerKubiliusLossA D)
          (subpowerKubiliusLossB A) (blockLogLog ℓ) →
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            subpowerBlockThreshold A ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
        squareDivisorMomentConstant * Real.rpow (blockLogLog ℓ) (-D) *
            subpowerSquareShiftConstant +
          4 * kubiliusPrimeCutoffLoweredCrossingMass y
            (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) +
          J * C * (Real.rpow (Real.log T / Real.log y)
            (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC, hTV⟩ := kubiliusTV_sum_arithmeticEventCard_div_le hK
  refine ⟨C, hC, ?_⟩
  intro c A D ℓ y T J u₀ hc hA hT hℓ hlog hycut hy hyT hbarrier
  let E : ℕ → Set (Finset ℕ) := fun q =>
    {S | ∃ a ≤ y,
      kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
          (subpowerKubiliusLossA D) (subpowerKubiliusLossB A) u₀ + q ≤
        centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S (primesUpTo a)}
  let E4 : ℕ → Set (Finset ℕ) := fun j => E (j / 4)
  let squareCard : ℕ → ℝ := fun j =>
    (((Finset.Icc 1 T).filter (fun n =>
      subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j <
        squareDivisorCount n)).card : ℝ)
  let walkCard : ℕ → ℝ := fun j =>
    (kubiliusArithmeticEventCard T y (E4 j) : ℝ)
  have hpoint : ∀ j : ℕ,
      (((Finset.Icc 1 T).filter (fun n =>
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
        squareCard j + walkCard j := by
    intro j
    have hsubset : (Finset.Icc 1 T).filter (fun n =>
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n) ⊆
      (Finset.Icc 1 T).filter (fun n =>
        subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j < squareDivisorCount n) ∪
      kubiliusArithmeticEventFinset T y (E4 j) := by
      intro n hn
      have hnmem := (Finset.mem_filter.mp hn).1
      have hmass := (Finset.mem_filter.mp hn).2
      rcases subpowerWeightedDivisorBlockMass_large_imp_square_or_kubiliusLowered
          c A D hc hA ℓ n y j hℓ hlog hycut hmass with hsq | hwalk
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnmem, hsq⟩)
      · apply Finset.mem_union_right
        apply mem_kubiliusArithmeticEventFinset.mpr
        refine ⟨hnmem, ?_⟩
        dsimp only [E4, E]
        change ∃ a ≤ y,
          kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
              (subpowerKubiliusLossA D) (subpowerKubiliusLossB A) u₀ +
                ((j / 4 : ℕ) : ℝ) ≤
            centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ))
              (n.primeFactors.filter (fun p => p ≤ y)) (primesUpTo a)
        refine ⟨dyadicExpCutoff (ℓ + 1), hycut, ?_⟩
        exact (add_le_add hbarrier (le_refl ((j / 4 : ℕ) : ℝ))).trans hwalk.le
    calc
      (((Finset.Icc 1 T).filter (fun n =>
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
          (((Finset.Icc 1 T).filter (fun n =>
            subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j < squareDivisorCount n) ∪
          kubiliusArithmeticEventFinset T y (E4 j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ squareCard j + walkCard j := by
        dsimp only [squareCard, walkCard, kubiliusArithmeticEventCard]
        exact_mod_cast Finset.card_union_le _ _
  have hsumCover :
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            subpowerBlockThreshold A ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) ≤
        (∑ j ∈ Finset.range J, squareCard j) +
          ∑ j ∈ Finset.range J, walkCard j := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (squareCard j + walkCard j) :=
        Finset.sum_le_sum fun j _ ↦ hpoint j
      _ = _ := by rw [Finset.sum_add_distrib]
  have hsquare : (∑ j ∈ Finset.range J, squareCard j) ≤
      T * squareDivisorMomentConstant * Real.rpow (blockLogLog ℓ) (-D) *
        subpowerSquareShiftConstant := by
    simpa only [squareCard] using
      sum_squareDivisorCount_large_card_subpowerCutoff_le D (blockLogLog ℓ)
        (zero_lt_one.trans_le hlog) T J
  have hTVsum : (∑ j ∈ Finset.range J, walkCard j / T) ≤
      (∑ j ∈ Finset.range J, kubiliusMass y (E4 j)) +
        J * C * (Real.rpow (Real.log T / Real.log y)
          (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))) := by
    simpa only [walkCard] using hTV T y J hy hyT E4
  have hmodel : (∑ j ∈ Finset.range J, kubiliusMass y (E4 j)) ≤
      4 * kubiliusPrimeCutoffLoweredCrossingMass y
        (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
          (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) := by
    have hgroup := sum_comp_nat_div_four_le (fun q ↦ kubiliusMass y (E q))
      (fun q ↦ kubiliusMass_nonneg y (E q)) J
    simpa only [E4, E, kubiliusPrimeCutoffLoweredCrossingMass] using hgroup
  have hwalk : (∑ j ∈ Finset.range J, walkCard j) / T ≤
      4 * kubiliusPrimeCutoffLoweredCrossingMass y
          (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
            (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) +
        J * C * (Real.rpow (Real.log T / Real.log y)
          (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))) := by
    rw [Finset.sum_div]
    exact hTVsum.trans (add_le_add hmodel (le_refl
      (J * C * (Real.rpow (Real.log T / Real.log y)
        (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))))))
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n =>
          subpowerBlockThreshold A ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
        ((∑ j ∈ Finset.range J, squareCard j) +
          ∑ j ∈ Finset.range J, walkCard j) / T :=
      div_le_div_of_nonneg_right hsumCover (by positivity)
    _ = (∑ j ∈ Finset.range J, squareCard j) / T +
        (∑ j ∈ Finset.range J, walkCard j) / T := by ring
    _ ≤ (T * squareDivisorMomentConstant * Real.rpow (blockLogLog ℓ) (-D) *
          subpowerSquareShiftConstant) / T +
        (4 * kubiliusPrimeCutoffLoweredCrossingMass y
            (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) +
          J * C * (Real.rpow (Real.log T / Real.log y)
            (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ)))) := by
      exact add_le_add (div_le_div_of_nonneg_right hsquare (by positivity)) hwalk
    _ = _ := by
      field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hT)]
      ring

open Classical in
/-- Geometric-block arithmetic transfer with the union over arithmetic levels taken before
cardinality.  This is the form compatible with the maximal inequality: the square-divisor
exceptions are summed over levels, while the selected-prime crossing and its `KubiliusTV` error
are charged only once for the entire level block. -/
theorem exists_subpowerBlock_union_large_cards_div_le_square_add_kubilius
    (hK : KubiliusTV) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c A D : ℝ) (s : Finset ℕ) (y T J : ℕ) (u₀ : ℝ),
        0 ≤ c → 0 < A → 0 < T →
        (∀ ℓ ∈ s, 6 ≤ ℓ ∧ 1 ≤ blockLogLog ℓ ∧
          dyadicExpCutoff (ℓ + 1) ≤ y ∧
          kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
              (subpowerKubiliusLossA D) (subpowerKubiliusLossB A) u₀ ≤
            kubiliusLoweredBarrier c (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB A) (blockLogLog ℓ)) →
        2 ≤ y → y ≤ T →
        (∑ j ∈ Finset.range J,
            (((Finset.Icc 1 T).filter (fun n => ∃ ℓ ∈ s,
              subpowerBlockThreshold A ℓ j <
                weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
          (∑ ℓ ∈ s, squareDivisorMomentConstant *
              Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) +
            4 * kubiliusPrimeCutoffLoweredCrossingMass y
              (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
                (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) +
            J * C * (Real.rpow (Real.log T / Real.log y)
              (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC, hTV⟩ := kubiliusTV_sum_arithmeticEventCard_div_le hK
  refine ⟨C, hC, ?_⟩
  intro c A D s y T J u₀ hc hA hT hlevels hy hyT
  let E : ℕ → Set (Finset ℕ) := fun q =>
    {S | ∃ a ≤ y,
      kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
          (subpowerKubiliusLossA D) (subpowerKubiliusLossB A) u₀ + q ≤
        centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ)) S (primesUpTo a)}
  let E4 : ℕ → Set (Finset ℕ) := fun j => E (j / 4)
  let squareEvent : ℕ → ℕ → Finset ℕ := fun ℓ j =>
    (Finset.Icc 1 T).filter (fun n =>
      subpowerKubiliusSquareCutoff D (blockLogLog ℓ) j < squareDivisorCount n)
  let squareUnion : ℕ → Finset ℕ := fun j =>
    s.biUnion (fun ℓ => squareEvent ℓ j)
  let squareCard : ℕ → ℕ → ℝ := fun ℓ j => ((squareEvent ℓ j).card : ℝ)
  let walkCard : ℕ → ℝ := fun j =>
    (kubiliusArithmeticEventCard T y (E4 j) : ℝ)
  have hpoint : ∀ j : ℕ,
      (((Finset.Icc 1 T).filter (fun n => ∃ ℓ ∈ s,
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
        (∑ ℓ ∈ s, squareCard ℓ j) + walkCard j := by
    intro j
    have hsubset : (Finset.Icc 1 T).filter (fun n => ∃ ℓ ∈ s,
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n) ⊆
        squareUnion j ∪ kubiliusArithmeticEventFinset T y (E4 j) := by
      intro n hn
      have hnmem := (Finset.mem_filter.mp hn).1
      obtain ⟨ℓ, hℓs, hmass⟩ := (Finset.mem_filter.mp hn).2
      obtain ⟨hℓ, hlog, hycut, hbarrier⟩ := hlevels ℓ hℓs
      rcases subpowerWeightedDivisorBlockMass_large_imp_square_or_kubiliusLowered
          c A D hc hA ℓ n y j hℓ hlog hycut hmass with hsq | hwalk
      · apply Finset.mem_union_left
        dsimp only [squareUnion]
        exact Finset.mem_biUnion.mpr ⟨ℓ, hℓs, by
          dsimp only [squareEvent]
          exact Finset.mem_filter.mpr ⟨hnmem, hsq⟩⟩
      · apply Finset.mem_union_right
        apply mem_kubiliusArithmeticEventFinset.mpr
        refine ⟨hnmem, ?_⟩
        dsimp only [E4, E]
        change ∃ a ≤ y,
          kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
              (subpowerKubiliusLossA D) (subpowerKubiliusLossB A) u₀ +
                ((j / 4 : ℕ) : ℝ) ≤
            centeredBernoulliFinsetSum (fun p : ℕ ↦ (1 / p : ℝ))
              (n.primeFactors.filter (fun p => p ≤ y)) (primesUpTo a)
        refine ⟨dyadicExpCutoff (ℓ + 1), hycut, ?_⟩
        exact (add_le_add hbarrier (le_refl ((j / 4 : ℕ) : ℝ))).trans hwalk.le
    calc
      (((Finset.Icc 1 T).filter (fun n => ∃ ℓ ∈ s,
          subpowerBlockThreshold A ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
          ((squareUnion j ∪ kubiliusArithmeticEventFinset T y (E4 j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ ((squareUnion j).card : ℝ) + walkCard j := by
        dsimp only [walkCard, kubiliusArithmeticEventCard]
        exact_mod_cast Finset.card_union_le (squareUnion j)
          (kubiliusArithmeticEventFinset T y (E4 j))
      _ ≤ (∑ ℓ ∈ s, squareCard ℓ j) + walkCard j := by
        gcongr
        dsimp only [squareUnion, squareCard]
        exact_mod_cast (Finset.card_biUnion_le (s := s)
          (t := fun ℓ => squareEvent ℓ j))
  have hsumCover :
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n => ∃ ℓ ∈ s,
            subpowerBlockThreshold A ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) ≤
        (∑ j ∈ Finset.range J, ∑ ℓ ∈ s, squareCard ℓ j) +
          ∑ j ∈ Finset.range J, walkCard j := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, ((∑ ℓ ∈ s, squareCard ℓ j) + walkCard j) :=
        Finset.sum_le_sum fun j _ ↦ hpoint j
      _ = _ := by rw [Finset.sum_add_distrib]
  have hsquare : (∑ j ∈ Finset.range J, ∑ ℓ ∈ s, squareCard ℓ j) ≤
      T * ∑ ℓ ∈ s, squareDivisorMomentConstant *
        Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant := by
    rw [Finset.sum_comm]
    calc
      (∑ ℓ ∈ s, ∑ j ∈ Finset.range J, squareCard ℓ j) ≤
          ∑ ℓ ∈ s, T * squareDivisorMomentConstant *
            Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant := by
        apply Finset.sum_le_sum
        intro ℓ hℓs
        obtain ⟨_hℓ, hlog, _hycut, _hbarrier⟩ := hlevels ℓ hℓs
        simpa only [squareCard, squareEvent] using
          sum_squareDivisorCount_large_card_subpowerCutoff_le D (blockLogLog ℓ)
            (zero_lt_one.trans_le hlog) T J
      _ = T * ∑ ℓ ∈ s, squareDivisorMomentConstant *
          Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ hℓs
        ring
  have hTVsum : (∑ j ∈ Finset.range J, walkCard j / T) ≤
      (∑ j ∈ Finset.range J, kubiliusMass y (E4 j)) +
        J * C * (Real.rpow (Real.log T / Real.log y)
          (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))) := by
    simpa only [walkCard] using hTV T y J hy hyT E4
  have hmodel : (∑ j ∈ Finset.range J, kubiliusMass y (E4 j)) ≤
      4 * kubiliusPrimeCutoffLoweredCrossingMass y
        (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
          (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) := by
    have hgroup := sum_comp_nat_div_four_le (fun q ↦ kubiliusMass y (E q))
      (fun q ↦ kubiliusMass_nonneg y (E q)) J
    simpa only [E4, E, kubiliusPrimeCutoffLoweredCrossingMass] using hgroup
  have hwalk : (∑ j ∈ Finset.range J, walkCard j) / T ≤
      4 * kubiliusPrimeCutoffLoweredCrossingMass y
          (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
            (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) +
        J * C * (Real.rpow (Real.log T / Real.log y)
          (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))) := by
    rw [Finset.sum_div]
    exact hTVsum.trans (add_le_add hmodel (le_refl
      (J * C * (Real.rpow (Real.log T / Real.log y)
        (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ))))))
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n => ∃ ℓ ∈ s,
          subpowerBlockThreshold A ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
        ((∑ j ∈ Finset.range J, ∑ ℓ ∈ s, squareCard ℓ j) +
          ∑ j ∈ Finset.range J, walkCard j) / T :=
      div_le_div_of_nonneg_right hsumCover (by positivity)
    _ = (∑ j ∈ Finset.range J, ∑ ℓ ∈ s, squareCard ℓ j) / T +
        (∑ j ∈ Finset.range J, walkCard j) / T := by ring
    _ ≤ (T * ∑ ℓ ∈ s, squareDivisorMomentConstant *
          Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) / T +
        (4 * kubiliusPrimeCutoffLoweredCrossingMass y
            (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB A) u₀ ((J + 3) / 4) +
          J * C * (Real.rpow (Real.log T / Real.log y)
            (-(Real.log T / Real.log y)) + Real.rpow T (-(1 / 2 : ℝ)))) := by
      exact add_le_add (div_le_div_of_nonneg_right hsquare (by positivity)) hwalk
    _ = _ := by
      rw [mul_div_cancel_left₀ _ (show (T : ℝ) ≠ 0 by
        exact_mod_cast (ne_of_gt hT))]
      ring

open Classical in
/-- The marginal-divisor cover in the form needed by the Kubilius argument: arithmetic levels may
be grouped arbitrarily, and each group's levels are unioned before cardinality.  This avoids the
factor equal to the number of arithmetic levels that would be introduced by the older
`marginalDivisorMass_large_card_le_sum_block_cards` estimate. -/
lemma sum_marginalDivisorMass_large_cards_le_grouped_block_unions
    (c C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (delta : ℕ → ℝ)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m)
    (L T J : ℕ) (exceptional : Finset ℕ) (groups : Finset (Finset ℕ))
    (hcover : ∀ i ∈ Finset.range T,
      L + i ∈ exceptional ∨ ∃ s ∈ groups, L + i ∈ s) :
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) ≤
      (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ exceptional,
          subpowerBlockThreshold (ε / C) ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) +
      ∑ s ∈ groups, ∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ s,
          subpowerBlockThreshold (ε / C) ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) := by
  have hdom : ∀ m : ℕ, dyadicExpCutoff L < m →
      delta m ≤ C * subpowerWeight c m := by
    intro m hm
    exact hdelta m ((dyadicExpCutoff_two_le L).trans (Nat.le_of_lt hm))
  let S : Finset ℕ := Finset.Icc 1 T
  let B : Finset ℕ → ℕ → Finset ℕ := fun s j ↦
    S.filter (fun n ↦ ∃ ℓ ∈ s,
      subpowerBlockThreshold (ε / C) ℓ j <
        weightedDivisorBlockMass (subpowerWeight c) ℓ n)
  let E : ℕ → Finset ℕ := fun j ↦
    S.filter (fun n ↦ ∃ ℓ ∈ exceptional,
      subpowerBlockThreshold (ε / C) ℓ j <
        weightedDivisorBlockMass (subpowerWeight c) ℓ n)
  have hpoint : ∀ j : ℕ,
      ((S.filter (fun n ↦
        ε * Real.rpow 2 ((j : ℝ) / 2) <
          marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ) ≤
        ((E j).card : ℝ) + ∑ s ∈ groups, ((B s j).card : ℝ) := by
    intro j
    have hthreshold : ∀ ℓ : ℕ,
        ((ε * Real.rpow 2 ((j : ℝ) / 2)) / C) * blockAllocation ℓ =
          subpowerBlockThreshold (ε / C) ℓ j := by
      intro ℓ
      unfold subpowerBlockThreshold
      ring_nf
    have hsub : S.filter (fun n ↦
        ε * Real.rpow 2 ((j : ℝ) / 2) <
          marginalDivisorMass delta (dyadicExpCutoff L) n) ⊆
        E j ∪ groups.biUnion (fun s ↦ B s j) := by
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      have hnI := Finset.mem_Icc.mp hnS
      obtain ⟨i, hi, hibad⟩ := exists_weightedDivisorBlockMass_gt_of_marginal
        delta (subpowerWeight c) C hC L n hdom hnI.1
          (ε * Real.rpow 2 ((j : ℝ) / 2))
          (mul_nonneg hε (Real.rpow_nonneg (by norm_num) _))
          (Finset.mem_filter.mp hn).2
      have hiT : i ∈ Finset.range T := by
        rw [Finset.mem_range] at hi ⊢
        exact hi.trans_le hnI.2
      rcases hcover i hiT with hLi | ⟨s, hsgroups, hLis⟩
      · apply Finset.mem_union_left
        dsimp only [E]
        exact Finset.mem_filter.mpr ⟨hnS, ⟨L + i, hLi, by
          simpa only [hthreshold] using hibad⟩⟩
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨s, hsgroups, by
          dsimp only [B]
          exact Finset.mem_filter.mpr ⟨hnS, ⟨L + i, hLis, by
            simpa only [hthreshold] using hibad⟩⟩⟩
    calc
      ((S.filter (fun n ↦
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ) ≤
          ((E j ∪ groups.biUnion (fun s ↦ B s j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((E j).card : ℝ) + ∑ s ∈ groups, ((B s j).card : ℝ) := by
        calc
          (((E j ∪ groups.biUnion (fun s ↦ B s j)).card : ℕ) : ℝ) ≤
              ((E j).card : ℝ) + ((groups.biUnion (fun s ↦ B s j)).card : ℝ) := by
            exact_mod_cast Finset.card_union_le (E j) (groups.biUnion (fun s ↦ B s j))
          _ ≤ ((E j).card : ℝ) + ∑ s ∈ groups, ((B s j).card : ℝ) := by
            gcongr
            exact_mod_cast Finset.card_biUnion_le
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) =
        ∑ j ∈ Finset.range J,
          ((S.filter (fun n ↦
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ) := by rfl
    _ ≤ ∑ j ∈ Finset.range J,
        (((E j).card : ℝ) + ∑ s ∈ groups, ((B s j).card : ℝ)) :=
      Finset.sum_le_sum fun j _ ↦ hpoint j
    _ = (∑ j ∈ Finset.range J, ((E j).card : ℝ)) +
        ∑ s ∈ groups, ∑ j ∈ Finset.range J, ((B s j).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ exceptional,
          subpowerBlockThreshold (ε / C) ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) +
        ∑ s ∈ groups, ∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ s,
          subpowerBlockThreshold (ε / C) ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) := by rfl

open Classical in
/-- The grouped marginal cover composed with `KubiliusTV`.  All analytic choices are exposed as
side conditions on the finite family of level groups; in particular, each group pays for one
prime-walk crossing event and one total-variation error, rather than one of each per arithmetic
level. -/
theorem exists_sum_marginalDivisorMass_large_cards_div_le_grouped_kubilius
    (hK : KubiliusTV) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (c C ε D : ℝ) (delta : ℕ → ℝ) (L T J : ℕ)
        (exceptional : Finset ℕ) (groups : Finset (Finset ℕ))
        (y : Finset ℕ → ℕ) (u₀ : Finset ℕ → ℝ),
        0 ≤ c → 0 < C → 0 < ε → 0 < T →
        (∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) →
        (∀ i ∈ Finset.range T,
          L + i ∈ exceptional ∨ ∃ s ∈ groups, L + i ∈ s) →
        (∀ s ∈ groups, ∀ ℓ ∈ s,
          6 ≤ ℓ ∧ 1 ≤ blockLogLog ℓ ∧ dyadicExpCutoff (ℓ + 1) ≤ y s ∧
          kubiliusLoweredBarrier (subpowerKubiliusModelCoefficient c)
              (subpowerKubiliusLossA D) (subpowerKubiliusLossB (ε / C)) (u₀ s) ≤
            kubiliusLoweredBarrier c (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB (ε / C)) (blockLogLog ℓ)) →
        (∀ s ∈ groups, 2 ≤ y s ∧ y s ≤ T) →
        (∑ j ∈ Finset.range J,
            (((Finset.Icc 1 T).filter (fun n ↦
              ε * Real.rpow 2 ((j : ℝ) / 2) <
                marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T ≤
          (∑ j ∈ Finset.range J,
            (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ exceptional,
              subpowerBlockThreshold (ε / C) ℓ j <
                weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T +
          ∑ s ∈ groups,
            ((∑ ℓ ∈ s, squareDivisorMomentConstant *
                Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) +
              4 * kubiliusPrimeCutoffLoweredCrossingMass (y s)
                (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
                  (subpowerKubiliusLossB (ε / C)) (u₀ s) ((J + 3) / 4) +
              J * K * (Real.rpow (Real.log T / Real.log (y s))
                (-(Real.log T / Real.log (y s))) + Real.rpow T (-(1 / 2 : ℝ)))) := by
  obtain ⟨K, hKpos, hunion⟩ :=
    exists_subpowerBlock_union_large_cards_div_le_square_add_kubilius hK
  refine ⟨K, hKpos, ?_⟩
  intro c C ε D delta L T J exceptional groups y u₀ hc hC hε hT hdelta hcover hlevels hy
  have hgrouped := sum_marginalDivisorMass_large_cards_le_grouped_block_unions
    c C ε hC hε.le delta hdelta L T J exceptional groups hcover
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T ≤
        ((∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ exceptional,
            subpowerBlockThreshold (ε / C) ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) +
          ∑ s ∈ groups, ∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ s,
            subpowerBlockThreshold (ε / C) ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T :=
      div_le_div_of_nonneg_right hgrouped (by positivity)
    _ = (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ exceptional,
            subpowerBlockThreshold (ε / C) ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T +
        ∑ s ∈ groups, (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ s,
            subpowerBlockThreshold (ε / C) ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T := by
      rw [add_div]
      congr 1
      rw [Finset.sum_div]
    _ ≤ (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦ ∃ ℓ ∈ exceptional,
            subpowerBlockThreshold (ε / C) ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T +
        ∑ s ∈ groups,
        ((∑ ℓ ∈ s, squareDivisorMomentConstant *
            Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) +
          4 * kubiliusPrimeCutoffLoweredCrossingMass (y s)
            (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB (ε / C)) (u₀ s) ((J + 3) / 4) +
          J * K * (Real.rpow (Real.log T / Real.log (y s))
            (-(Real.log T / Real.log (y s))) + Real.rpow T (-(1 / 2 : ℝ)))) := by
      gcongr with s hs
      exact hunion c (ε / C) D s (y s) T J (u₀ s) hc (div_pos hε hC) hT
        (hlevels s hs) (hy s hs).1 (hy s hs).2

open Classical in
/-- The explicit right-hand side produced by applying the grouped arithmetic transfer to the
canonical slack-aware partition.  Keeping it named makes the remaining global estimates
(exceptional top band, square sum, model tail, and total-variation tail) independent lemmas. -/
noncomputable def subpowerKubiliusCanonicalGroupedBound
    (K c C ε D : ℝ) (L T J Y : ℕ) : ℝ :=
  (∑ j ∈ Finset.range J,
      (((Finset.Icc 1 T).filter (fun n ↦
        ∃ ℓ ∈ subpowerKubiliusExceptionalLevels L T Y,
          subpowerBlockThreshold (ε / C) ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T +
    ∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
      ((∑ ℓ ∈ s, squareDivisorMomentConstant *
          Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) +
        4 * kubiliusPrimeCutoffLoweredCrossingMass
          (subpowerKubiliusGroupCutoff s)
          (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
            (subpowerKubiliusLossB (ε / C)) (subpowerKubiliusGroupAnchor c s)
              ((J + 3) / 4) +
        J * K * (Real.rpow
          (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
          (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
            Real.rpow T (-(1 / 2 : ℝ))))

open Classical in
/-- The canonical finite partition wired into the grouped Kubilius transfer.  In addition to the
large-card bound, the conclusion retains the model variance caps and places every group beyond an
arbitrary requested geometric tail index `K₀`. -/
theorem exists_sum_marginalDivisorMass_large_cards_div_le_canonical_kubilius
    (hK : KubiliusTV) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (c C ε D : ℝ) (delta : ℕ → ℝ),
        1 < c → 0 < C → 0 < ε → 0 ≤ D →
        (∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) →
        ∀ K₀ : ℕ, ∃ L₀ : ℕ, 6 ≤ L₀ ∧
          ∀ L : ℕ, L₀ ≤ L → ∀ T Y J : ℕ, 0 < T → Y ≤ T →
            (∑ j ∈ Finset.range J,
                (((Finset.Icc 1 T).filter (fun n ↦
                  ε * Real.rpow 2 ((j : ℝ) / 2) <
                    marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T ≤
              subpowerKubiliusCanonicalGroupedBound K c C ε D L T J Y ∧
            (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
              Real.log (Real.log (subpowerKubiliusGroupCutoff s : ℝ)) +
                  Erdos67.PrimeEstimates.mertensBound ≤
                kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
                  subpowerKubiliusGroupAnchor c s) ∧
            (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
              K₀ ≤ subpowerKubiliusGroupingIndex c (s.sup id)) := by
  obtain ⟨K, hKpos, hgrouped⟩ :=
    exists_sum_marginalDivisorMass_large_cards_div_le_grouped_kubilius hK
  refine ⟨K, hKpos, ?_⟩
  intro c C ε D delta hc hC hε hD hdelta K₀
  obtain ⟨L₀, hL₀, hdata⟩ := exists_subpowerKubiliusLevelGroups_data hc
    (subpowerKubiliusLossA D) (subpowerKubiliusLossB (ε / C))
    (subpowerKubiliusLossA_nonneg D hD) (subpowerKubiliusLossB_nonneg (ε / C)) K₀
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL T Y J hT hYT
  have hd := hdata L hL T Y hYT
  have hbound := hgrouped c C ε D delta L T J
    (subpowerKubiliusExceptionalLevels L T Y)
    (subpowerKubiliusLevelGroups c L T Y)
    subpowerKubiliusGroupCutoff (subpowerKubiliusGroupAnchor c)
    (zero_le_one.trans hc.le) hC hε hT hdelta hd.1 hd.2.1 hd.2.2.1
  refine ⟨?_, hd.2.2.2.1, hd.2.2.2.2⟩
  simpa only [subpowerKubiliusCanonicalGroupedBound] using hbound

/-- The largest dyadic-exponential level that can occur below the averaging cutoff.  This exact
integer surrogate for `log₂ log₂ T` is used to count the canonical geometric fibers without
paying for all `T` nominal levels in `subpowerKubiliusLevelInterval`. -/
def subpowerKubiliusTopLevel (T : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 T)

/-- Number of top dyadic levels reserved for the deterministic exceptional band.  Its logarithmic
size makes the remaining cutoff ratio polynomially large in the top level. -/
def subpowerKubiliusTopGap (T : ℕ) : ℕ :=
  4 * (Nat.log 2 (subpowerKubiliusTopLevel T) + 1)

/-- Common prime cutoff used by all ordinary canonical groups. -/
def subpowerKubiliusCommonCutoff (T : ℕ) : ℕ :=
  dyadicExpCutoff (subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T)

lemma four_mul_succ_le_two_pow {k : ℕ} (hk : 5 ≤ k) :
    4 * (k + 1) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      omega

lemma subpowerKubiliusTopGap_le_topLevel {T : ℕ}
    (hT : 32 ≤ subpowerKubiliusTopLevel T) :
    subpowerKubiliusTopGap T ≤ subpowerKubiliusTopLevel T := by
  let H := subpowerKubiliusTopLevel T
  let k := Nat.log 2 H
  have hH0 : H ≠ 0 := by omega
  have hk : 5 ≤ k := by
    dsimp only [k]
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    exact hT
  have hpow : 2 ^ k ≤ H := by
    dsimp only [k]
    exact Nat.pow_log_le_self 2 hH0
  exact (four_mul_succ_le_two_pow hk).trans hpow

/-- The logarithmic top gap produces a fourth-power separation of dyadic logarithmic cutoffs. -/
lemma topLevel_pow_four_le_two_pow_topGap {T : ℕ} :
    (subpowerKubiliusTopLevel T) ^ 4 ≤ 2 ^ subpowerKubiliusTopGap T := by
  let H := subpowerKubiliusTopLevel T
  let k := Nat.log 2 H
  by_cases hH0 : H = 0
  · simp [H, hH0]
  · have hH : H ≤ 2 ^ (k + 1) :=
      (Nat.lt_pow_succ_log_self (by omega) H).le
    have hpow := Nat.pow_le_pow_left hH 4
    calc
      H ^ 4 ≤ (2 ^ (k + 1)) ^ 4 := hpow
      _ = 2 ^ (4 * (k + 1)) := by rw [← pow_mul]; congr 1; omega
      _ = 2 ^ subpowerKubiliusTopGap T := by
        simp only [subpowerKubiliusTopGap, H, k]

/-- A dyadic-exponential endpoint below `T` has level index at most the exact top level. -/
lemma level_succ_le_subpowerKubiliusTopLevel {T ℓ : ℕ}
    (hcut : dyadicExpCutoff (ℓ + 1) ≤ T) :
    ℓ + 1 ≤ subpowerKubiliusTopLevel T := by
  have hT0 : T ≠ 0 := by
    have hcutPos : 0 < dyadicExpCutoff (ℓ + 1) := by
      unfold dyadicExpCutoff
      positivity
    omega
  have hinner : 2 ^ (ℓ + 1) ≤ Nat.log 2 T := by
    rw [Nat.le_log_iff_pow_le (by omega) hT0]
    simpa only [dyadicExpCutoff] using hcut
  have hlogT0 : Nat.log 2 T ≠ 0 := by
    have hpowPos : 0 < 2 ^ (ℓ + 1) := by positivity
    omega
  rw [subpowerKubiliusTopLevel, Nat.le_log_iff_pow_le (by omega) hlogT0]
  exact hinner

/-- Once the exact top level is nontrivial, its dyadic-exponential endpoint lies below `T`. -/
lemma dyadicExpCutoff_topLevel_le {T : ℕ}
    (hH : 1 ≤ subpowerKubiliusTopLevel T) :
    dyadicExpCutoff (subpowerKubiliusTopLevel T) ≤ T := by
  let A := Nat.log 2 T
  let H := subpowerKubiliusTopLevel T
  have hA0 : A ≠ 0 := by
    intro hA
    have hHzero : subpowerKubiliusTopLevel T = 0 := by
      simp [subpowerKubiliusTopLevel, A, hA]
    omega
  have hT0 : T ≠ 0 := by
    intro hT
    subst T
    simp [A] at hA0
  have hinner : 2 ^ H ≤ A := by
    dsimp only [H, subpowerKubiliusTopLevel, A]
    exact Nat.pow_log_le_self 2 hA0
  calc
    dyadicExpCutoff H = 2 ^ (2 ^ H) := rfl
    _ ≤ 2 ^ A := Nat.pow_le_pow_right (by omega) hinner
    _ ≤ T := Nat.pow_log_le_self 2 hT0

lemma subpowerKubiliusCommonCutoff_le {T : ℕ}
    (hH : 1 ≤ subpowerKubiliusTopLevel T) :
    subpowerKubiliusCommonCutoff T ≤ T := by
  exact (dyadicExpCutoff_mono (Nat.sub_le _ _)).trans
    (dyadicExpCutoff_topLevel_le hH)

/-- Ordinary levels inject into the initial segment below the exact dyadic top level. -/
lemma subpowerKubiliusOrdinaryLevels_subset_topRange
    (L T Y : ℕ) (hYT : Y ≤ T) :
    subpowerKubiliusOrdinaryLevels L T Y ⊆
      Finset.range (subpowerKubiliusTopLevel T) := by
  intro ℓ hℓ
  rw [Finset.mem_range]
  have hcut := (mem_subpowerKubiliusOrdinaryLevels.mp hℓ).2.2
  have hsucc := level_succ_le_subpowerKubiliusTopLevel (hcut.trans hYT)
  omega

/-- The number of nonempty canonical fibers is at most the exact dyadic top level.  This is the
cardinality input needed to sum the termwise `KubiliusTV` error. -/
theorem subpowerKubiliusLevelGroups_card_le_topLevel
    (c : ℝ) (L T Y : ℕ) (hYT : Y ≤ T) :
    (subpowerKubiliusLevelGroups c L T Y).card ≤
      subpowerKubiliusTopLevel T := by
  let levels := subpowerKubiliusOrdinaryLevels L T Y
  let keys := levels.image (subpowerKubiliusGroupingIndex c)
  calc
    (subpowerKubiliusLevelGroups c L T Y).card ≤ keys.card := by
      unfold subpowerKubiliusLevelGroups
      exact Finset.card_image_le
    _ ≤ levels.card := Finset.card_image_le
    _ ≤ (Finset.range (subpowerKubiliusTopLevel T)).card :=
      Finset.card_le_card (subpowerKubiliusOrdinaryLevels_subset_topRange L T Y hYT)
    _ = subpowerKubiliusTopLevel T := Finset.card_range _

open Classical in
/-- At the common cutoff, every canonical group's Kubilius parameter
`log T / log(groupCutoff)` is at least the fourth power of the exact top level.  This is the
load-bearing coupling between the small total-variation error and the logarithmically thin
exceptional band. -/
theorem topLevel_pow_four_le_group_log_ratio
    (c : ℝ) (L T : ℕ)
    (hH : 32 ≤ subpowerKubiliusTopLevel T)
    {s : Finset ℕ}
    (hs : s ∈ subpowerKubiliusLevelGroups c L T
      (subpowerKubiliusCommonCutoff T)) :
    (subpowerKubiliusTopLevel T : ℝ) ^ 4 ≤
      Real.log T / Real.log (subpowerKubiliusGroupCutoff s) := by
  let H := subpowerKubiliusTopLevel T
  let g := subpowerKubiliusTopGap T
  let y := subpowerKubiliusGroupCutoff s
  have hgH : g ≤ H := subpowerKubiliusTopGap_le_topLevel hH
  have htopT : dyadicExpCutoff H ≤ T :=
    dyadicExpCutoff_topLevel_le (by omega)
  have hycut : y ≤ dyadicExpCutoff (H - g) := by
    simpa only [y, subpowerKubiliusCommonCutoff, H, g] using
      subpowerKubiliusGroupCutoff_le hs
  have hy2 : 2 ≤ y := by
    dsimp only [y, subpowerKubiliusGroupCutoff]
    exact dyadicExpCutoff_two_le _
  have hlogy0 : 0 < Real.log y :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : Real.log y ≤ (2 : ℝ) ^ (H - g) * Real.log 2 := by
    calc
      Real.log y ≤ Real.log (dyadicExpCutoff (H - g) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hycut)
      _ = (2 : ℝ) ^ (H - g) * Real.log 2 := log_dyadicExpCutoff _
  have hlogT : (2 : ℝ) ^ H * Real.log 2 ≤ Real.log T := by
    have hcutPos : (0 : ℝ) < dyadicExpCutoff H := by
      exact_mod_cast (show 0 < dyadicExpCutoff H by
        unfold dyadicExpCutoff
        positivity)
    calc
      (2 : ℝ) ^ H * Real.log 2 = Real.log (dyadicExpCutoff H : ℝ) :=
        (log_dyadicExpCutoff H).symm
      _ ≤ Real.log T :=
        Real.log_le_log hcutPos (by exact_mod_cast htopT)
  have hpowNat : H ^ 4 * 2 ^ (H - g) ≤ 2 ^ H := by
    calc
      H ^ 4 * 2 ^ (H - g) ≤ 2 ^ g * 2 ^ (H - g) :=
        Nat.mul_le_mul_right _ topLevel_pow_four_le_two_pow_topGap
      _ = 2 ^ (g + (H - g)) := (pow_add 2 g (H - g)).symm
      _ = 2 ^ H := by rw [Nat.add_sub_of_le hgH]
  have hpow : (H : ℝ) ^ 4 * (2 : ℝ) ^ (H - g) ≤ (2 : ℝ) ^ H := by
    exact_mod_cast hpowNat
  apply (le_div_iff₀ hlogy0).2
  calc
    (H : ℝ) ^ 4 * Real.log y ≤
        (H : ℝ) ^ 4 * ((2 : ℝ) ^ (H - g) * Real.log 2) := by
      gcongr
    _ = ((H : ℝ) ^ 4 * (2 : ℝ) ^ (H - g)) * Real.log 2 := by ring
    _ ≤ (2 : ℝ) ^ H * Real.log 2 := mul_le_mul_of_nonneg_right hpow hlog2.le
    _ ≤ Real.log T := hlogT

/-- For `u ≥ V ≥ 1`, the superexponential total-variation term `u⁻ᵘ` is bounded by
`1 / V`.  The deliberately coarse reciprocal form is enough once the common cutoff makes `V`
a high power of `log log T`. -/
lemma rpow_neg_self_le_one_div {V u : ℝ} (hV : 1 ≤ V) (hVu : V ≤ u) :
    Real.rpow u (-u) ≤ 1 / V := by
  have hu : 1 ≤ u := hV.trans hVu
  calc
    Real.rpow u (-u) ≤ Real.rpow u (-1) :=
      Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    _ = (Real.rpow u 1)⁻¹ := Real.rpow_neg (zero_le_one.trans hu) 1
    _ = u⁻¹ := congrArg Inv.inv (Real.rpow_one u)
    _ = 1 / u := by rw [one_div]
    _ ≤ 1 / V := one_div_le_one_div_of_le (by linarith) hVu

open Classical in
/-- Uniform finite-family estimate for the accumulated `KubiliusTV` error in the canonical bound.
It isolates the remaining cutoff construction into one transparent condition: every ordinary
group must have `log T / log y ≥ V`. -/
theorem subpowerKubiliusCanonical_tv_sum_le
    (K c : ℝ) (L T Y J : ℕ) (V : ℝ)
    (hK : 0 ≤ K) (hYT : Y ≤ T) (hV : 1 ≤ V)
    (hratio : ∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
      V ≤ Real.log T / Real.log (subpowerKubiliusGroupCutoff s)) :
    (∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
      J * K * (Real.rpow
        (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
        (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
          Real.rpow T (-(1 / 2 : ℝ)))) ≤
      subpowerKubiliusTopLevel T * (J * K *
        (1 / V + Real.rpow T (-(1 / 2 : ℝ)))) := by
  let groups := subpowerKubiliusLevelGroups c L T Y
  let E : ℝ := J * K * (1 / V + Real.rpow T (-(1 / 2 : ℝ)))
  have hJK : 0 ≤ (J : ℝ) * K := mul_nonneg (by positivity) hK
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg hJK (add_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
  have hterm : ∀ s ∈ groups,
      J * K * (Real.rpow
        (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
        (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
          Real.rpow T (-(1 / 2 : ℝ))) ≤ E := by
    intro s hs
    dsimp only [groups] at hs
    dsimp only [E]
    gcongr
    exact rpow_neg_self_le_one_div hV (hratio s hs)
  calc
    (∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
      J * K * (Real.rpow
        (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
        (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
          Real.rpow T (-(1 / 2 : ℝ)))) ≤ ∑ _s ∈ groups, E := by
      exact Finset.sum_le_sum hterm
    _ = groups.card * E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ subpowerKubiliusTopLevel T * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast subpowerKubiliusLevelGroups_card_le_topLevel c L T Y hYT
    _ = subpowerKubiliusTopLevel T * (J * K *
        (1 / V + Real.rpow T (-(1 / 2 : ℝ)))) := rfl

open Classical in
/-- Specialized accumulated `KubiliusTV` bound for the common cutoff.  With the intended threshold
truncation `J ≤ 4H`, where `H = log₂ log₂ T`, the error is reduced to an inverse-square
term plus `H² / √T`. -/
theorem subpowerKubiliusCanonical_tv_sum_commonCutoff_le
    (K c : ℝ) (L T J : ℕ) (hK : 0 ≤ K)
    (hH : 32 ≤ subpowerKubiliusTopLevel T)
    (hJ : J ≤ 4 * subpowerKubiliusTopLevel T) :
    (∑ s ∈ subpowerKubiliusLevelGroups c L T
        (subpowerKubiliusCommonCutoff T),
      J * K * (Real.rpow
        (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
        (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
          Real.rpow T (-(1 / 2 : ℝ)))) ≤
      4 * K / (subpowerKubiliusTopLevel T : ℝ) ^ 2 +
        4 * K * (subpowerKubiliusTopLevel T : ℝ) ^ 2 *
          Real.rpow T (-(1 / 2 : ℝ)) := by
  let H := subpowerKubiliusTopLevel T
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hcutT : subpowerKubiliusCommonCutoff T ≤ T :=
    subpowerKubiliusCommonCutoff_le (by omega)
  have hV : (1 : ℝ) ≤ (H : ℝ) ^ 4 := by
    have hHone : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
    exact one_le_pow₀ hHone
  have hraw := subpowerKubiliusCanonical_tv_sum_le K c L T
    (subpowerKubiliusCommonCutoff T) J ((H : ℝ) ^ 4) hK hcutT
    hV
    (fun s hs ↦ by
      simpa only [H] using topLevel_pow_four_le_group_log_ratio c L T hH hs)
  have hJreal : (J : ℝ) ≤ 4 * H := by exact_mod_cast hJ
  have htail0 : 0 ≤ 1 / (H : ℝ) ^ 4 + Real.rpow T (-(1 / 2 : ℝ)) :=
    add_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  calc
    (∑ s ∈ subpowerKubiliusLevelGroups c L T
        (subpowerKubiliusCommonCutoff T),
      J * K * (Real.rpow
        (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
        (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
          Real.rpow T (-(1 / 2 : ℝ)))) ≤
        H * (J * K *
          (1 / (H : ℝ) ^ 4 + Real.rpow T (-(1 / 2 : ℝ)))) := hraw
    _ ≤ H * ((4 * H) * K *
          (1 / (H : ℝ) ^ 4 + Real.rpow T (-(1 / 2 : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hHpos.le
      apply mul_le_mul_of_nonneg_right _ htail0
      exact mul_le_mul_of_nonneg_right hJreal hK
    _ = 4 * K / (H : ℝ) ^ 2 +
        4 * K * (H : ℝ) ^ 2 * Real.rpow T (-(1 / 2 : ℝ)) := by
      field_simp

/-! ### The exceptional top band

The common Kubilius cutoff deliberately leaves a logarithmically thin band of top arithmetic
levels.  On that band the original one-level fractional-moment estimate is strong enough for every
`c > 1`: we keep less slack than the globally summable `c > 3` argument and only ask for a
strictly negative power. -/

/-- Cubic-error allowance in the one-level Chernoff exponent for the exceptional top band. -/
noncomputable def subpowerTopBandRho (c : ℝ) : ℝ :=
  (c - 1) / (4 * c)

/-- Polynomial exponent retained from the one-level moment estimate. -/
noncomputable def subpowerTopBandAlpha (c : ℝ) : ℝ :=
  (c + 1) / 4

/-- Small polynomial allowance for the allocated threshold. -/
noncomputable def subpowerTopBandDelta (c : ℝ) : ℝ :=
  (c - 1) / 16

/-- Strict decay left after the moment, allocation, and geometric-shift factors. -/
noncomputable def subpowerTopBandDecay (c : ℝ) : ℝ :=
  3 * (c - 1) / 16

lemma subpowerTopBandRho_pos {c : ℝ} (hc : 1 < c) :
    0 < subpowerTopBandRho c := by
  unfold subpowerTopBandRho
  positivity

lemma subpowerTopBandRho_lt_half {c : ℝ} (hc : 1 < c) :
    subpowerTopBandRho c < 1 / 2 := by
  unfold subpowerTopBandRho
  rw [div_lt_iff₀ (by positivity : 0 < 4 * c)]
  linarith

lemma subpowerTopBandAlpha_pos {c : ℝ} (hc : 1 < c) :
    0 < subpowerTopBandAlpha c := by
  unfold subpowerTopBandAlpha
  linarith

lemma subpowerTopBandDelta_pos {c : ℝ} (hc : 1 < c) :
    0 < subpowerTopBandDelta c := by
  unfold subpowerTopBandDelta
  linarith

lemma subpowerTopBandDecay_pos {c : ℝ} (hc : 1 < c) :
    0 < subpowerTopBandDecay c := by
  unfold subpowerTopBandDecay
  linarith

lemma subpowerTopBand_slack_mul {c : ℝ} (hc : 1 < c) :
    (1 / 2 - subpowerTopBandRho c) * c = subpowerTopBandAlpha c := by
  have hc0 : c ≠ 0 := ne_of_gt (by linarith : 0 < c)
  unfold subpowerTopBandRho subpowerTopBandAlpha
  field_simp [hc0]
  ring

lemma subpowerTopBand_exponent (c : ℝ) :
    -subpowerTopBandAlpha c + subpowerTopBandDelta c + 1 / 2 =
      -subpowerTopBandDecay c := by
  unfold subpowerTopBandAlpha subpowerTopBandDelta subpowerTopBandDecay
  ring

/-- Threshold-factor estimate with an arbitrary positive polynomial allowance.  The older
`subpowerBlockThresholdFactor_le` hard-codes the `c > 3` allowance `subpowerDelta`; the thin top
band instead uses `subpowerTopBandDelta`. -/
lemma subpowerBlockThresholdFactor_le_of_two_mul_le
    (c A δ : ℝ) (hA : 0 < A) (ℓ : ℕ)
    (hs0 : 0 ≤ subpowerBlockS c ℓ) (hs1 : subpowerBlockS c ℓ ≤ 1)
    (hsδ : 2 * subpowerBlockS c ℓ ≤ δ) :
    Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) ≤
      max 1 A⁻¹ * Real.rpow ((ℓ : ℝ) + 2) δ := by
  have halloc0 : 0 ≤ blockAllocation ℓ := (blockAllocation_pos ℓ).le
  have hsplit :
      Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) =
        Real.rpow A (-subpowerBlockS c ℓ) *
          Real.rpow (blockAllocation ℓ) (-subpowerBlockS c ℓ) := by
    change (A * blockAllocation ℓ) ^ (-subpowerBlockS c ℓ) = _
    exact Real.mul_rpow hA.le halloc0
  rw [hsplit]
  exact mul_le_mul
    (rpow_neg_le_max_one_inv A (subpowerBlockS c ℓ) hA hs0 hs1)
    (blockAllocation_rpow_neg_le ℓ (subpowerBlockS c ℓ) δ hs0 hsδ)
    (Real.rpow_nonneg (by positivity) _)
    (le_trans zero_le_one (le_max_left _ _))

/-- For every `c > 1`, the exact one-block moment has decay exponent `(c+1)/4`.  Unlike
`eventually_subpowerBlockMomentFactor_le`, this spends only the slack needed by the thin top band
and therefore does not require `c > 3`. -/
lemma eventually_subpowerBlockMomentFactor_le_topBand {c : ℝ} (hc : 1 < c) :
    ∀ᶠ ℓ : ℕ in atTop,
      subpowerBlockMomentFactor c ℓ ≤
        subpowerMomentConstant *
          Real.rpow (blockLogLog ℓ) (-subpowerTopBandAlpha c) := by
  have hρ0 : 0 < subpowerTopBandRho c := subpowerTopBandRho_pos hc
  have hρhalf : subpowerTopBandRho c < 1 / 2 := subpowerTopBandRho_lt_half hc
  have hσ : ∀ᶠ ℓ : ℕ in atTop,
      blockSigma c (blockLogLog ℓ) < subpowerTopBandRho c :=
    (tendsto_blockSigma_blockLogLog_zero c).eventually_lt_const hρ0
  have hu : ∀ᶠ ℓ : ℕ in atTop, 1 ≤ blockLogLog ℓ :=
    tendsto_blockLogLog_atTop.eventually_ge_atTop 1
  filter_upwards [hσ, hu] with ℓ hσ hu
  have hc0 : 0 < c := by linarith
  have hσ0 : 0 ≤ blockSigma c (blockLogLog ℓ) := Real.sqrt_nonneg _
  have hσ1 : blockSigma c (blockLogLog ℓ) ≤ 1 := by linarith
  have hcore := chernoffExponent_blockSigma_le_slack c (blockLogLog ℓ)
    (subpowerTopBandRho c) hc0.le hu hρhalf hσ.le
  have hcore' :
      blockLogLog ℓ *
            (Real.exp (blockSigma c (blockLogLog ℓ)) - 1 -
              blockSigma c (blockLogLog ℓ)) -
          blockSigma c (blockLogLog ℓ) *
            Real.sqrt (c * blockLogLog ℓ * Real.log (blockLogLog ℓ)) ≤
        -subpowerTopBandAlpha c * Real.log (blockLogLog ℓ) := by
    calc
      _ ≤ -(1 / 2 - subpowerTopBandRho c) * c *
          Real.log (blockLogLog ℓ) := hcore
      _ = -((1 / 2 - subpowerTopBandRho c) * c) *
          Real.log (blockLogLog ℓ) := by ring
      _ = _ := by rw [subpowerTopBand_slack_mul hc]
  let q : ℝ := Real.exp (blockSigma c (blockLogLog ℓ)) - 1
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact sub_nonneg.mpr (by simpa using Real.exp_le_exp.mpr hσ0)
  have hq1 : q ≤ Real.exp 1 - 1 := by
    dsimp only [q]
    linarith [Real.exp_le_exp.mpr hσ1]
  have hrest :
      q * Real.log 2 + q * Erdos67.PrimeEstimates.mertensBound + 1 ≤
        (Real.exp 1 - 1) *
          (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1 := by
    calc
      q * Real.log 2 + q * Erdos67.PrimeEstimates.mertensBound + 1 ≤
          q * Real.log 2 + q * |Erdos67.PrimeEstimates.mertensBound| + 1 := by
        gcongr
        exact le_abs_self _
      _ = q * (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1 := by ring
      _ ≤ (Real.exp 1 - 1) *
          (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1 := by
        gcongr
  rw [subpowerBlockMomentFactor_eq_exp]
  have hfull :
      blockLogLog ℓ *
            (Real.exp (blockSigma c (blockLogLog ℓ)) - 1 -
              blockSigma c (blockLogLog ℓ)) -
          blockSigma c (blockLogLog ℓ) *
            Real.sqrt (c * blockLogLog ℓ * Real.log (blockLogLog ℓ)) +
        (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) * Real.log 2 +
        (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) *
          Erdos67.PrimeEstimates.mertensBound + 1 ≤
        -subpowerTopBandAlpha c * Real.log (blockLogLog ℓ) +
          ((Real.exp 1 - 1) *
            (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1) := by
    change _ + q * Real.log 2 + q * Erdos67.PrimeEstimates.mertensBound + 1 ≤ _
    linarith
  have hrpow : Real.rpow (blockLogLog ℓ) (-subpowerTopBandAlpha c) =
      Real.exp (Real.log (blockLogLog ℓ) * (-subpowerTopBandAlpha c)) := by
    change blockLogLog ℓ ^ (-subpowerTopBandAlpha c) = _
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hu)]
  rw [subpowerMomentConstant, hrpow]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert hfull using 1 <;> ring

/-- Eventual side conditions needed to turn the exact one-level majorant into a fixed negative
power for the exceptional band. -/
lemma eventually_subpowerTopBand_parameters {c : ℝ} (hc : 1 < c) :
    ∀ᶠ ℓ : ℕ in atTop,
      6 ≤ ℓ ∧
      1 ≤ Real.log (blockLogLog ℓ) ∧
      0 < subpowerBlockS c ℓ ∧
      subpowerBlockS c ℓ ≤ 1 ∧
      2 * subpowerBlockS c ℓ ≤ subpowerTopBandDelta c ∧
      blockSigma c (blockLogLog ℓ) ≤ 1 := by
  have hδ : 0 < subpowerTopBandDelta c / 2 := by
    positivity [subpowerTopBandDelta_pos hc]
  have hsδ : ∀ᶠ ℓ : ℕ in atTop,
      subpowerBlockS c ℓ < subpowerTopBandDelta c / 2 :=
    (tendsto_subpowerBlockS_zero c).eventually_lt_const hδ
  have hs1 : ∀ᶠ ℓ : ℕ in atTop, subpowerBlockS c ℓ < 1 :=
    (tendsto_subpowerBlockS_zero c).eventually_lt_const zero_lt_one
  have hσ1 : ∀ᶠ ℓ : ℕ in atTop, blockSigma c (blockLogLog ℓ) < 1 :=
    (tendsto_blockSigma_blockLogLog_zero c).eventually_lt_const zero_lt_one
  have hu : ∀ᶠ ℓ : ℕ in atTop, Real.exp 1 ≤ blockLogLog ℓ :=
    tendsto_blockLogLog_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [eventually_ge_atTop 6, hu, hsδ, hs1, hσ1] with ℓ hℓ hu hsδ hs1 hσ1
  have hu1 : 1 < blockLogLog ℓ :=
    (by linarith [Real.exp_one_gt_two] : 1 < Real.exp 1).trans_le hu
  have hlog : 1 ≤ Real.log (blockLogLog ℓ) := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (Real.exp_pos 1))
      (Set.mem_Ioi.mpr (zero_lt_one.trans hu1)) hu
  exact ⟨hℓ, hlog, subpowerBlockS_pos c (by linarith) ℓ hu1, hs1.le,
    (by linarith), hσ1.le⟩

/-- Constant in the exceptional-band one-level majorant. -/
noncomputable def subpowerTopBandConstant (c A : ℝ) : ℝ :=
  subpowerMomentConstant * Real.rpow 4 (subpowerTopBandAlpha c) *
    max 1 A⁻¹ * (4 / Real.sqrt c)

lemma subpowerTopBandConstant_nonneg (c A : ℝ) :
    0 ≤ subpowerTopBandConstant c A := by
  unfold subpowerTopBandConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg subpowerMomentConstant_pos.le (Real.rpow_nonneg (by norm_num) _))
      (le_trans zero_le_one (le_max_left _ _)))
    (div_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The full one-level shift majorant decays by a fixed negative power for every `c > 1`.  Global
summability is neither asserted nor needed: the exceptional set contains only logarithmically many
levels near the top cutoff. -/
theorem eventually_subpowerBlockShiftMajorant_le_topBand
    {c A : ℝ} (hc : 1 < c) (hA : 0 < A) :
    ∀ᶠ ℓ : ℕ in atTop,
      subpowerBlockShiftMajorant c A ℓ ≤
        subpowerTopBandConstant c A *
          Real.rpow ((ℓ : ℝ) + 2) (-subpowerTopBandDecay c) := by
  filter_upwards [eventually_subpowerBlockMomentFactor_le_topBand hc,
    eventually_subpowerTopBand_parameters hc] with ℓ hmoment hpar
  rcases hpar with ⟨hℓ, hlog, hs0, hs1, hsδ, hσ1⟩
  let u : ℝ := blockLogLog ℓ
  let v : ℝ := (ℓ : ℝ) + 2
  have hu0 : 0 < u := by
    dsimp only [u]
    exact (by positivity : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4).trans_le
      (blockLogLog_ge_quarter_add ℓ hℓ)
  have hv0 : 0 < v := by dsimp only [v]; positivity
  have huv : v / 4 ≤ u := by
    simpa only [u, v] using blockLogLog_ge_quarter_add ℓ hℓ
  have hpowUV : Real.rpow u (-subpowerTopBandAlpha c) ≤
      Real.rpow 4 (subpowerTopBandAlpha c) *
        Real.rpow v (-subpowerTopBandAlpha c) := by
    have hmono : Real.rpow u (-subpowerTopBandAlpha c) ≤
        Real.rpow (v / 4) (-subpowerTopBandAlpha c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) huv
        (by linarith [subpowerTopBandAlpha_pos hc])
    calc
      Real.rpow u (-subpowerTopBandAlpha c) ≤
          Real.rpow (v / 4) (-subpowerTopBandAlpha c) := hmono
      _ = Real.rpow 4 (subpowerTopBandAlpha c) *
          Real.rpow v (-subpowerTopBandAlpha c) := by
        change (v / 4) ^ (-subpowerTopBandAlpha c) =
          4 ^ subpowerTopBandAlpha c * v ^ (-subpowerTopBandAlpha c)
        rw [Real.div_rpow hv0.le (by norm_num : (0 : ℝ) ≤ 4)]
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv, inv_inv]
        ring
  have hthreshold := subpowerBlockThresholdFactor_le_of_two_mul_le
    c A (subpowerTopBandDelta c) hA ℓ hs0.le hs1 hsδ
  have hgeom := subpowerBlockShiftGeomFactor_le c (by linarith) ℓ hℓ hlog hs0 hσ1
  have hthreshold0 : 0 ≤ Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) :=
    Real.rpow_nonneg (mul_nonneg hA.le (blockAllocation_pos ℓ).le) _
  have hgeom0 : 0 ≤ (1 - Real.rpow 2 (-subpowerBlockS c ℓ / 2))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
  have hupper0 :
      0 ≤ subpowerMomentConstant * Real.rpow u (-subpowerTopBandAlpha c) :=
    mul_nonneg subpowerMomentConstant_pos.le (Real.rpow_nonneg hu0.le _)
  have hthresholdUpper0 :
      0 ≤ max 1 A⁻¹ * Real.rpow v (subpowerTopBandDelta c) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (Real.rpow_nonneg hv0.le _)
  have hgeomUpper0 : 0 ≤ (4 / Real.sqrt c) * Real.rpow v (1 / 2) :=
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hv0.le _)
  have hraw : subpowerBlockShiftMajorant c A ℓ ≤
      (subpowerMomentConstant * Real.rpow u (-subpowerTopBandAlpha c)) *
        (max 1 A⁻¹ * Real.rpow v (subpowerTopBandDelta c)) *
          ((4 / Real.sqrt c) * Real.rpow v (1 / 2)) := by
    unfold subpowerBlockShiftMajorant
    exact mul_le_mul
      (mul_le_mul hmoment hthreshold hthreshold0 hupper0)
      hgeom hgeom0 (mul_nonneg hupper0 hthresholdUpper0)
  have hraw' : subpowerBlockShiftMajorant c A ℓ ≤
      (subpowerMomentConstant *
          (Real.rpow 4 (subpowerTopBandAlpha c) *
            Real.rpow v (-subpowerTopBandAlpha c))) *
        (max 1 A⁻¹ * Real.rpow v (subpowerTopBandDelta c)) *
          ((4 / Real.sqrt c) * Real.rpow v (1 / 2)) :=
    hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowUV subpowerMomentConstant_pos.le)
        hthresholdUpper0)
      hgeomUpper0)
  have hrpows :
      Real.rpow v (-subpowerTopBandAlpha c) *
          Real.rpow v (subpowerTopBandDelta c) * Real.rpow v (1 / 2) =
        Real.rpow v
          (-subpowerTopBandAlpha c + subpowerTopBandDelta c + 1 / 2) := by
    change v ^ (-subpowerTopBandAlpha c) * v ^ subpowerTopBandDelta c *
        v ^ (1 / 2 : ℝ) =
      v ^ (-subpowerTopBandAlpha c + subpowerTopBandDelta c + 1 / 2)
    rw [← Real.rpow_add hv0, ← Real.rpow_add hv0]
  calc
    subpowerBlockShiftMajorant c A ℓ ≤
        (subpowerMomentConstant *
            (Real.rpow 4 (subpowerTopBandAlpha c) *
              Real.rpow v (-subpowerTopBandAlpha c))) *
          (max 1 A⁻¹ * Real.rpow v (subpowerTopBandDelta c)) *
            ((4 / Real.sqrt c) * Real.rpow v (1 / 2)) := hraw'
    _ = subpowerTopBandConstant c A *
        Real.rpow v (-subpowerTopBandDecay c) := by
      unfold subpowerTopBandConstant
      rw [← subpowerTopBand_exponent c, ← hrpows]
      ring
    _ = subpowerTopBandConstant c A *
        Real.rpow ((ℓ : ℝ) + 2) (-subpowerTopBandDecay c) := rfl

/-- Exceptional levels that can actually contribute for integers `n ≤ T`.  Levels whose left
endpoint is already at least `T` have identically zero block mass and are removed here. -/
def subpowerKubiliusActiveExceptionalLevels (L T : ℕ) : Finset ℕ :=
  (subpowerKubiliusExceptionalLevels L T (subpowerKubiliusCommonCutoff T)).filter
    (fun ℓ => dyadicExpCutoff ℓ < T)

@[simp] lemma mem_subpowerKubiliusActiveExceptionalLevels {L T ℓ : ℕ} :
    ℓ ∈ subpowerKubiliusActiveExceptionalLevels L T ↔
      ℓ ∈ subpowerKubiliusExceptionalLevels L T
        (subpowerKubiliusCommonCutoff T) ∧ dyadicExpCutoff ℓ < T := by
  simp [subpowerKubiliusActiveExceptionalLevels]

open Classical in
/-- A divisor block vanishes once its left endpoint is at least the integer being factored. -/
lemma weightedDivisorBlockMass_eq_zero_of_le
    (weight : ℕ → ℝ) {ℓ n : ℕ} (hn : 1 ≤ n) (hle : n ≤ dyadicExpCutoff ℓ) :
    weightedDivisorBlockMass weight ℓ n = 0 := by
  unfold weightedDivisorBlockMass
  apply Finset.sum_eq_zero
  intro d hd
  have hddiv : d ∣ n :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdn : d ≤ n := Nat.le_of_dvd (by omega) hddiv
  have hcutd := (Finset.mem_filter.mp hd).2.1
  omega

/-- A dyadic-exponential left endpoint below `T` has level at most the exact top level. -/
lemma level_le_subpowerKubiliusTopLevel {T ℓ : ℕ}
    (hcut : dyadicExpCutoff ℓ ≤ T) :
    ℓ ≤ subpowerKubiliusTopLevel T := by
  have hT0 : T ≠ 0 := by
    have hcutPos : 0 < dyadicExpCutoff ℓ := by
      unfold dyadicExpCutoff
      positivity
    omega
  have hinner : 2 ^ ℓ ≤ Nat.log 2 T := by
    rw [Nat.le_log_iff_pow_le (by omega) hT0]
    simpa only [dyadicExpCutoff] using hcut
  have hlogT0 : Nat.log 2 T ≠ 0 := by
    have hpowPos : 0 < 2 ^ ℓ := by positivity
    omega
  rw [subpowerKubiliusTopLevel, Nat.le_log_iff_pow_le (by omega) hlogT0]
  exact hinner

/-- Every active exceptional level lies between the common-cutoff level and the exact top level. -/
lemma subpowerKubiliusActiveExceptionalLevels_mem_bounds
    {L T ℓ : ℕ} (hℓ : ℓ ∈ subpowerKubiliusActiveExceptionalLevels L T) :
    subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T ≤ ℓ ∧
      ℓ ≤ subpowerKubiliusTopLevel T := by
  let H := subpowerKubiliusTopLevel T
  let g := subpowerKubiliusTopGap T
  have hdata := mem_subpowerKubiliusActiveExceptionalLevels.mp hℓ
  have hexceptional := (mem_subpowerKubiliusExceptionalLevels.mp hdata.1).2.2
  have hlower : H - g ≤ ℓ := by
    by_contra hnot
    have hsucc : ℓ + 1 ≤ H - g := by omega
    have hmono := dyadicExpCutoff_mono hsucc
    dsimp only [H, g] at hmono
    rw [← subpowerKubiliusCommonCutoff] at hmono
    omega
  have hupper : ℓ ≤ H := by
    dsimp only [H]
    exact level_le_subpowerKubiliusTopLevel hdata.2.le
  exact ⟨hlower, hupper⟩

/-- The active exceptional band contains at most `g + 1` levels, where
`g = subpowerKubiliusTopGap T`. -/
lemma subpowerKubiliusActiveExceptionalLevels_card_le
    (L T : ℕ) (hH : 32 ≤ subpowerKubiliusTopLevel T) :
    (subpowerKubiliusActiveExceptionalLevels L T).card ≤
      subpowerKubiliusTopGap T + 1 := by
  let H := subpowerKubiliusTopLevel T
  let g := subpowerKubiliusTopGap T
  have hgH : g ≤ H := by
    simpa only [H, g] using subpowerKubiliusTopGap_le_topLevel hH
  have hsubset : subpowerKubiliusActiveExceptionalLevels L T ⊆ Finset.Icc (H - g) H := by
    intro ℓ hℓ
    simp only [Finset.mem_Icc]
    simpa only [H, g] using subpowerKubiliusActiveExceptionalLevels_mem_bounds hℓ
  calc
    (subpowerKubiliusActiveExceptionalLevels L T).card ≤
        (Finset.Icc (H - g) H).card := Finset.card_le_card hsubset
    _ = g + 1 := by
      rw [Nat.card_Icc]
      omega

open Classical in
/-- The exceptional union is bounded by the sum of the old one-level shift majorants, after
discarding the levels that cannot contain a divisor of any `n ≤ T`. -/
theorem subpowerKubiliusExceptional_union_large_cards_div_le_majorants
    (c A : ℝ) (hc : 0 ≤ c) (hA : 0 < A) (L T J : ℕ) (hT : 0 < T)
    (hpar : ∀ ℓ ∈ subpowerKubiliusActiveExceptionalLevels L T,
      3 ≤ ℓ ∧ 0 < subpowerBlockS c ℓ ∧ subpowerBlockS c ℓ ≤ 1) :
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦
          ∃ ℓ ∈ subpowerKubiliusExceptionalLevels L T
              (subpowerKubiliusCommonCutoff T),
            subpowerBlockThreshold A ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
      ∑ ℓ ∈ subpowerKubiliusActiveExceptionalLevels L T,
        subpowerBlockShiftMajorant c A ℓ := by
  let active := subpowerKubiliusActiveExceptionalLevels L T
  let E : ℕ → Finset ℕ := fun j =>
    (Finset.Icc 1 T).filter (fun n ↦
      ∃ ℓ ∈ subpowerKubiliusExceptionalLevels L T
          (subpowerKubiliusCommonCutoff T),
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n)
  let B : ℕ → ℕ → Finset ℕ := fun ℓ j =>
    (Finset.Icc 1 T).filter (fun n ↦
      subpowerBlockThreshold A ℓ j <
        weightedDivisorBlockMass (subpowerWeight c) ℓ n)
  have hpoint : ∀ j : ℕ, ((E j).card : ℝ) ≤
      ∑ ℓ ∈ active, ((B ℓ j).card : ℝ) := by
    intro j
    have hsubset : E j ⊆ active.biUnion (fun ℓ => B ℓ j) := by
      intro n hn
      have hnIcc := (Finset.mem_filter.mp hn).1
      have hnBounds := Finset.mem_Icc.mp hnIcc
      obtain ⟨ℓ, hℓexceptional, hmass⟩ := (Finset.mem_filter.mp hn).2
      have hcut : dyadicExpCutoff ℓ < T := by
        by_contra hnot
        have hTcut : T ≤ dyadicExpCutoff ℓ := Nat.le_of_not_gt hnot
        have hzero := weightedDivisorBlockMass_eq_zero_of_le
          (subpowerWeight c) hnBounds.1 (hnBounds.2.trans hTcut)
        rw [hzero] at hmass
        linarith [subpowerBlockThreshold_pos A hA ℓ j]
      have hℓactive : ℓ ∈ active := by
        dsimp only [active]
        exact mem_subpowerKubiliusActiveExceptionalLevels.mpr
          ⟨hℓexceptional, hcut⟩
      exact Finset.mem_biUnion.mpr ⟨ℓ, hℓactive, by
        dsimp only [B]
        exact Finset.mem_filter.mpr ⟨hnIcc, hmass⟩⟩
    calc
      ((E j).card : ℝ) ≤ ((active.biUnion (fun ℓ => B ℓ j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ ∑ ℓ ∈ active, ((B ℓ j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
  have hsum : (∑ j ∈ Finset.range J, ((E j).card : ℝ)) ≤
      T * ∑ ℓ ∈ active, subpowerBlockShiftMajorant c A ℓ := by
    calc
      (∑ j ∈ Finset.range J, ((E j).card : ℝ)) ≤
          ∑ j ∈ Finset.range J, ∑ ℓ ∈ active, ((B ℓ j).card : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ hpoint j
      _ = ∑ ℓ ∈ active, ∑ j ∈ Finset.range J, ((B ℓ j).card : ℝ) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ ℓ ∈ active, T * subpowerBlockShiftMajorant c A ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        obtain ⟨hℓ3, hs0, hs1⟩ := hpar ℓ (by simpa only [active] using hℓ)
        simpa only [B] using
          sum_subpowerWeight_block_large_cards_le_majorant
            c A hc hA ℓ hℓ3 hs0 hs1 T J
      _ = T * ∑ ℓ ∈ active, subpowerBlockShiftMajorant c A ℓ := by
        rw [Finset.mul_sum]
  change (∑ j ∈ Finset.range J, ((E j).card : ℝ)) / T ≤ _
  calc
    (∑ j ∈ Finset.range J, ((E j).card : ℝ)) / T ≤
        (T * ∑ ℓ ∈ active, subpowerBlockShiftMajorant c A ℓ) / T :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = ∑ ℓ ∈ active, subpowerBlockShiftMajorant c A ℓ := by
      field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hT)]

open Classical in
/-- Quantitative exceptional-band estimate before taking the final limit.  Every active level lies
in `[H-g,H]`, so the union costs at most `g+1` copies of the negative-power one-level majorant. -/
theorem exists_subpowerKubiliusExceptional_union_large_cards_div_le_topBand
    (c A : ℝ) (hc : 1 < c) (hA : 0 < A) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ, 0 < T →
      32 ≤ subpowerKubiliusTopLevel T →
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦
            ∃ ℓ ∈ subpowerKubiliusExceptionalLevels L T
                (subpowerKubiliusCommonCutoff T),
              subpowerBlockThreshold A ℓ j <
                weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
        ((subpowerKubiliusTopGap T + 1 : ℕ) : ℝ) *
          subpowerTopBandConstant c A *
            Real.rpow
              ((subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T : ℕ) + 2)
              (-subpowerTopBandDecay c) := by
  have hevent := (eventually_subpowerBlockShiftMajorant_le_topBand hc hA).and
    (eventually_subpowerTopBand_parameters hc)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hevent.and (eventually_ge_atTop 6))
  have hL₀data := hL₀ L₀ le_rfl
  refine ⟨L₀, hL₀data.2, ?_⟩
  intro L hL T J hT hH
  let active := subpowerKubiliusActiveExceptionalLevels L T
  let H := subpowerKubiliusTopLevel T
  let g := subpowerKubiliusTopGap T
  let E : ℝ := subpowerTopBandConstant c A *
    Real.rpow ((H - g : ℕ) + 2) (-subpowerTopBandDecay c)
  have hactiveL : ∀ ℓ ∈ active, L ≤ ℓ := by
    intro ℓ hℓ
    have hmem := mem_subpowerKubiliusActiveExceptionalLevels.mp (by
      simpa only [active] using hℓ)
    exact (mem_subpowerKubiliusExceptionalLevels.mp hmem.1).1
  have hpar : ∀ ℓ ∈ active,
      3 ≤ ℓ ∧ 0 < subpowerBlockS c ℓ ∧ subpowerBlockS c ℓ ≤ 1 := by
    intro ℓ hℓ
    obtain ⟨hmoment, hparams⟩ := (hL₀ ℓ (hL.trans (hactiveL ℓ hℓ))).1
    exact ⟨by omega, hparams.2.2.1, hparams.2.2.2.1⟩
  have hraw := subpowerKubiliusExceptional_union_large_cards_div_le_majorants
    c A (zero_le_one.trans hc.le) hA L T J hT (by simpa only [active] using hpar)
  have hterm : ∀ ℓ ∈ active, subpowerBlockShiftMajorant c A ℓ ≤ E := by
    intro ℓ hℓ
    have hmoment := (hL₀ ℓ (hL.trans (hactiveL ℓ hℓ))).1.1
    have hlower := (subpowerKubiliusActiveExceptionalLevels_mem_bounds (by
      simpa only [active] using hℓ)).1
    have hbase : ((H - g : ℕ) + 2 : ℝ) ≤ (ℓ : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right (by simpa only [H, g] using hlower) 2
    have hrpow : Real.rpow ((ℓ : ℝ) + 2) (-subpowerTopBandDecay c) ≤
        Real.rpow ((H - g : ℕ) + 2) (-subpowerTopBandDecay c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase
        (by linarith [subpowerTopBandDecay_pos hc])
    exact hmoment.trans (mul_le_mul_of_nonneg_left hrpow
      (subpowerTopBandConstant_nonneg c A))
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (subpowerTopBandConstant_nonneg c A)
      (Real.rpow_nonneg (by positivity) _)
  have hcard : active.card ≤ g + 1 := by
    simpa only [active, g] using
      subpowerKubiliusActiveExceptionalLevels_card_le L T hH
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n ↦
          ∃ ℓ ∈ subpowerKubiliusExceptionalLevels L T
              (subpowerKubiliusCommonCutoff T),
            subpowerBlockThreshold A ℓ j <
              weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T ≤
        ∑ ℓ ∈ active, subpowerBlockShiftMajorant c A ℓ := by
      simpa only [active] using hraw
    _ ≤ ∑ _ℓ ∈ active, E := Finset.sum_le_sum hterm
    _ = (active.card : ℝ) * E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((g + 1 : ℕ) : ℝ) * E := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE
    _ = ((subpowerKubiliusTopGap T + 1 : ℕ) : ℝ) *
        subpowerTopBandConstant c A *
          Real.rpow
            ((subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T : ℕ) + 2)
            (-subpowerTopBandDecay c) := by
      dsimp only [E, H, g]
      ring

/-- A logarithm times any fixed negative power tends to zero, in the scaled form used by the
top-band envelope. -/
lemma tendsto_logAffine_mul_halfRpow_neg_atTop
    (d C : ℝ) (hd : 0 < d) :
    Tendsto (fun x : ℝ => (8 * Real.log x + 5) * C *
      Real.rpow (x / 2) (-d)) atTop (nhds 0) := by
  have hlogdiv := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
  change Tendsto (fun x : ℝ => Real.log x / Real.rpow x d) atTop (nhds 0) at hlogdiv
  have hlogmul : Tendsto (fun x : ℝ => Real.log x * Real.rpow x (-d))
      atTop (nhds 0) := by
    apply hlogdiv.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [show Real.rpow x (-d) = (Real.rpow x d)⁻¹ from Real.rpow_neg hx d]
    rw [div_eq_mul_inv]
  have hpow : Tendsto (fun x : ℝ => Real.rpow x (-d)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hd
  have hsum : Tendsto (fun x : ℝ =>
      8 * (Real.log x * Real.rpow x (-d)) + 5 * Real.rpow x (-d))
      atTop (nhds 0) := by
    convert (hlogmul.const_mul 8).add (hpow.const_mul 5) using 1 <;> norm_num
  have hscaled := hsum.const_mul (C * Real.rpow 2 d)
  have hscaled' : Tendsto (fun x : ℝ => C * Real.rpow 2 d *
      (8 * (Real.log x * Real.rpow x (-d)) + 5 * Real.rpow x (-d)))
      atTop (nhds 0) := by simpa using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hdiv : Real.rpow (x / 2) (-d) =
      Real.rpow x (-d) / Real.rpow 2 (-d) := by
    exact Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2) (-d)
  rw [hdiv]
  rw [show Real.rpow 2 (-d) = (Real.rpow 2 d)⁻¹ from
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) d]
  rw [div_eq_mul_inv, inv_inv]
  ring

/-- The exact dyadic top level tends to infinity with the averaging range. -/
lemma tendsto_subpowerKubiliusTopLevel_atTop :
    Tendsto subpowerKubiliusTopLevel atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (dyadicExpCutoff K)] with T hT
  exact level_le_subpowerKubiliusTopLevel hT

/-- The logarithmic band width is bounded by an affine natural logarithm of the top level. -/
lemma topGap_add_one_cast_le_log_topLevel {T : ℕ}
    (hH : 1 ≤ subpowerKubiliusTopLevel T) :
    ((subpowerKubiliusTopGap T + 1 : ℕ) : ℝ) ≤
      8 * Real.log (subpowerKubiliusTopLevel T : ℝ) + 5 := by
  let H := subpowerKubiliusTopLevel T
  have hlog0 : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by positivity
  have hk := Real.natLog_le_logb H 2
  have hk' : (Nat.log 2 H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
    calc
      (Nat.log 2 H : ℝ) ≤ Real.log (H : ℝ) / Real.log 2 := by
        norm_num [Real.logb] at hk ⊢
        exact hk
      _ ≤ 2 * Real.log (H : ℝ) := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith
  dsimp only [subpowerKubiliusTopGap, H]
  push_cast
  linarith

/-- Once the top coordinate is large, the logarithmic gap occupies at most half of it. -/
lemma two_mul_topGap_le_topLevel {T : ℕ}
    (hH : 4096 ≤ subpowerKubiliusTopLevel T) :
    2 * subpowerKubiliusTopGap T ≤ subpowerKubiliusTopLevel T := by
  let H := subpowerKubiliusTopLevel T
  have hHone : 1 ≤ H := by omega
  have hlog0 : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hHone)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by positivity
  have hk := Real.natLog_le_logb H 2
  have hk' : (Nat.log 2 H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
    calc
      (Nat.log 2 H : ℝ) ≤ Real.log (H : ℝ) / Real.log 2 := by
        norm_num [Real.logb] at hk ⊢
        exact hk
      _ ≤ 2 * Real.log (H : ℝ) := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith
  have hlog : Real.log (H : ℝ) ≤ 2 * Real.sqrt H := by
    calc
      Real.log (H : ℝ) ≤ Real.rpow (H : ℝ) (1 / 2) / (1 / 2) :=
        Real.log_le_rpow_div (by positivity) (by norm_num)
      _ = 2 * Real.sqrt H := by
        rw [show Real.rpow (H : ℝ) (1 / 2) = Real.sqrt H from
          (Real.sqrt_eq_rpow _).symm]
        ring
  have hsqrt : (64 : ℝ) ≤ Real.sqrt H := by
    have hs := Real.sqrt_le_sqrt (by exact_mod_cast hH : (4096 : ℝ) ≤ H)
    norm_num at hs ⊢
    exact hs
  have hsquare : (Real.sqrt H) ^ 2 = (H : ℝ) :=
    Real.sq_sqrt (by positivity)
  exact_mod_cast (show (2 : ℝ) * (4 * ((Nat.log 2 H : ℝ) + 1)) ≤ H by
    nlinarith)

/-- The explicit exceptional-band envelope tends to zero for every `c > 1`. -/
theorem tendsto_subpowerKubiliusTopBandEnvelope
    (c A : ℝ) (hc : 1 < c) :
    Tendsto (fun T : ℕ =>
      ((subpowerKubiliusTopGap T + 1 : ℕ) : ℝ) *
        subpowerTopBandConstant c A *
          Real.rpow
            ((subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T : ℕ) + 2)
            (-subpowerTopBandDecay c)) atTop (nhds 0) := by
  let d := subpowerTopBandDecay c
  let C₀ := subpowerTopBandConstant c A
  have hd : 0 < d := subpowerTopBandDecay_pos hc
  have hC₀ : 0 ≤ C₀ := subpowerTopBandConstant_nonneg c A
  have htopReal : Tendsto (fun T : ℕ => (subpowerKubiliusTopLevel T : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
        tendsto_subpowerKubiliusTopLevel_atTop
  have hupper : Tendsto (fun T : ℕ =>
      (8 * Real.log (subpowerKubiliusTopLevel T : ℝ) + 5) * C₀ *
        Real.rpow ((subpowerKubiliusTopLevel T : ℝ) / 2) (-d))
      atTop (nhds 0) :=
    (tendsto_logAffine_mul_halfRpow_neg_atTop d C₀ hd).comp htopReal
  apply squeeze_zero'
  · filter_upwards [] with T
    exact mul_nonneg
      (mul_nonneg (by positivity) hC₀)
      (Real.rpow_nonneg (by positivity) _)
  · filter_upwards
      [tendsto_subpowerKubiliusTopLevel_atTop.eventually_ge_atTop 4096]
      with T hH
    let H := subpowerKubiliusTopLevel T
    let g := subpowerKubiliusTopGap T
    have htwog : 2 * g ≤ H := by
      simpa only [H, g] using two_mul_topGap_le_topLevel hH
    have hgH : g ≤ H := by omega
    have hgap : ((g + 1 : ℕ) : ℝ) ≤ 8 * Real.log (H : ℝ) + 5 := by
      simpa only [H, g] using topGap_add_one_cast_le_log_topLevel (T := T) (by omega)
    have hlog0 : 0 ≤ Real.log (H : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega))
    have hcoeff0 : 0 ≤ 8 * Real.log (H : ℝ) + 5 := by positivity
    have hbase : (H : ℝ) / 2 ≤ ((H - g : ℕ) + 2 : ℝ) := by
      rw [Nat.cast_sub hgH]
      have htwogReal : (2 : ℝ) * g ≤ H := by exact_mod_cast htwog
      linarith
    have hrpow :
        Real.rpow ((H - g : ℕ) + 2) (-d) ≤
          Real.rpow ((H : ℝ) / 2) (-d) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    have hrpow0 : 0 ≤ Real.rpow ((H - g : ℕ) + 2) (-d) :=
      Real.rpow_nonneg (by positivity) _
    calc
      ((subpowerKubiliusTopGap T + 1 : ℕ) : ℝ) *
          subpowerTopBandConstant c A *
            Real.rpow
              ((subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T : ℕ) + 2)
              (-subpowerTopBandDecay c) =
          ((g + 1 : ℕ) : ℝ) * C₀ * Real.rpow ((H - g : ℕ) + 2) (-d) := rfl
      _ ≤ (8 * Real.log (H : ℝ) + 5) * C₀ *
          Real.rpow ((H - g : ℕ) + 2) (-d) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgap hC₀) hrpow0
      _ ≤ (8 * Real.log (H : ℝ) + 5) * C₀ *
          Real.rpow ((H : ℝ) / 2) (-d) := by
        exact mul_le_mul_of_nonneg_left hrpow (mul_nonneg hcoeff0 hC₀)
      _ = (8 * Real.log (subpowerKubiliusTopLevel T : ℝ) + 5) * C₀ *
          Real.rpow ((subpowerKubiliusTopLevel T : ℝ) / 2) (-d) := rfl
  · exact hupper

open Classical in
/-- The complete exceptional contribution is uniformly small in both the averaging range and the
number of shift thresholds once the starting divisor level is late enough. -/
theorem exists_subpowerKubiliusExceptional_union_large_cards_div_lt
    (c A ζ : ℝ) (hc : 1 < c) (hA : 0 < A) (hζ : 0 < ζ) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n ↦
            ∃ ℓ ∈ subpowerKubiliusExceptionalLevels L T
                (subpowerKubiliusCommonCutoff T),
              subpowerBlockThreshold A ℓ j <
                weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) / T < ζ := by
  obtain ⟨Lq, hLq6, hquant⟩ :=
    exists_subpowerKubiliusExceptional_union_large_cards_div_le_topBand c A hc hA
  obtain ⟨Lp, hparams⟩ := eventually_atTop.1 (eventually_subpowerTopBand_parameters hc)
  have henvEv : ∀ᶠ T : ℕ in atTop,
      ((subpowerKubiliusTopGap T + 1 : ℕ) : ℝ) *
          subpowerTopBandConstant c A *
            Real.rpow
              ((subpowerKubiliusTopLevel T - subpowerKubiliusTopGap T : ℕ) + 2)
              (-subpowerTopBandDecay c) < ζ :=
    (tendsto_subpowerKubiliusTopBandEnvelope c A hc).eventually_lt_const hζ
  obtain ⟨T₀, henv⟩ := eventually_atTop.1 henvEv
  let L₀ := max (max (max Lq Lp) T₀) 32
  refine ⟨L₀, ?_, ?_⟩
  · dsimp only [L₀]
    omega
  intro L hL T J
  by_cases hT0 : T = 0
  · subst T
    simpa using hζ
  have hT : 0 < T := Nat.pos_of_ne_zero hT0
  let active := subpowerKubiliusActiveExceptionalLevels L T
  have hactiveL : ∀ ℓ ∈ active, L ≤ ℓ := by
    intro ℓ hℓ
    have hmem := mem_subpowerKubiliusActiveExceptionalLevels.mp (by
      simpa only [active] using hℓ)
    exact (mem_subpowerKubiliusExceptionalLevels.mp hmem.1).1
  have hpar : ∀ ℓ ∈ active,
      3 ≤ ℓ ∧ 0 < subpowerBlockS c ℓ ∧ subpowerBlockS c ℓ ≤ 1 := by
    intro ℓ hℓ
    have hLpL : Lp ≤ L :=
      (le_max_right Lq Lp).trans
        ((le_max_left (max Lq Lp) T₀).trans (le_max_left _ 32) |>.trans hL)
    have hp := hparams ℓ (hLpL.trans (hactiveL ℓ hℓ))
    exact ⟨by omega, hp.2.2.1, hp.2.2.2.1⟩
  have hgeneric := subpowerKubiliusExceptional_union_large_cards_div_le_majorants
    c A (zero_le_one.trans hc.le) hA L T J hT (by simpa only [active] using hpar)
  have hLqL : Lq ≤ L :=
    (le_max_left Lq Lp).trans
      ((le_max_left (max Lq Lp) T₀).trans (le_max_left _ 32) |>.trans hL)
  have hT₀L : T₀ ≤ L :=
    (le_max_right (max Lq Lp) T₀).trans (le_max_left _ 32) |>.trans hL
  have h32L : 32 ≤ L := (le_max_right (max (max Lq Lp) T₀) 32).trans hL
  by_cases hTlarge : T₀ ≤ T
  · by_cases hH : 32 ≤ subpowerKubiliusTopLevel T
    · exact (hquant L hLqL T J hT hH).trans_lt (henv T hTlarge)
    · have hempty : active = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨ℓ, hℓ⟩
        have hupper := (subpowerKubiliusActiveExceptionalLevels_mem_bounds (by
          simpa only [active] using hℓ)).2
        have hlower := hactiveL ℓ hℓ
        omega
      rw [show subpowerKubiliusActiveExceptionalLevels L T = ∅ by simpa only [active] using hempty,
        Finset.sum_empty] at hgeneric
      exact hgeneric.trans_lt hζ
  · have hempty : active = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨ℓ, hℓ⟩
      have hmem := mem_subpowerKubiliusActiveExceptionalLevels.mp (by
        simpa only [active] using hℓ)
      have hindex : ℓ ≤ dyadicExpCutoff ℓ := by
        simpa using index_le_dyadicExpCutoff_add 0 ℓ
      have hlower := hactiveL ℓ hℓ
      omega
    rw [show subpowerKubiliusActiveExceptionalLevels L T = ∅ by simpa only [active] using hempty,
      Finset.sum_empty] at hgeneric
    exact hgeneric.trans_lt hζ

/-- The square of a logarithm still loses to a square root. -/
lemma tendsto_log_sq_mul_rpow_neg_half :
    Tendsto (fun x : ℝ => (Real.log x) ^ 2 * Real.rpow x (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
  have hdiv := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  change Tendsto (fun x : ℝ => Real.rpow (Real.log x) 2 /
    Real.rpow x (1 / 2)) atTop (nhds 0) at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [show Real.rpow x (-(1 / 2 : ℝ)) = (Real.rpow x (1 / 2))⁻¹ from
    Real.rpow_neg (zero_le_one.trans hx) (1 / 2)]
  rw [show Real.rpow (Real.log x) 2 = (Real.log x) ^ (2 : ℕ) by
    exact Real.rpow_natCast (Real.log x) 2]
  rw [div_eq_mul_inv]

/-- The exact top level is at most twice the natural logarithm of the averaging range. -/
lemma topLevel_cast_le_two_mul_log {T : ℕ} (hT : 1 ≤ T) :
    (subpowerKubiliusTopLevel T : ℝ) ≤ 2 * Real.log T := by
  have hlog0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by positivity
  have hk := Real.natLog_le_logb T 2
  have hk' : (Nat.log 2 T : ℝ) ≤ 2 * Real.log (T : ℝ) := by
    calc
      (Nat.log 2 T : ℝ) ≤ Real.log (T : ℝ) / Real.log 2 := by
        norm_num [Real.logb] at hk ⊢
        exact hk
      _ ≤ 2 * Real.log (T : ℝ) := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith
  have houter : subpowerKubiliusTopLevel T ≤ Nat.log 2 T := by
    exact Nat.log_le_self 2 (Nat.log 2 T)
  exact (by exact_mod_cast houter :
    (subpowerKubiliusTopLevel T : ℝ) ≤ Nat.log 2 T) |>.trans hk'

/-- The `H² / √T` term in the accumulated total-variation error tends to zero. -/
lemma tendsto_topLevel_sq_mul_rpow_neg_half :
    Tendsto (fun T : ℕ => (subpowerKubiliusTopLevel T : ℝ) ^ 2 *
      Real.rpow T (-(1 / 2 : ℝ))) atTop (nhds 0) := by
  have hupper : Tendsto (fun T : ℕ =>
      4 * (Real.log T) ^ 2 * Real.rpow T (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_assoc, mul_zero] using
      (tendsto_log_sq_mul_rpow_neg_half.const_mul 4).comp
        tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · filter_upwards [] with T
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hH := topLevel_cast_le_two_mul_log hT
    have hlog0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
    have hsq : (subpowerKubiliusTopLevel T : ℝ) ^ 2 ≤
        4 * (Real.log T) ^ 2 := by
      nlinarith [(sq_nonneg
        ((subpowerKubiliusTopLevel T : ℝ) - 2 * Real.log T))]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by positivity) _)
  · exact hupper

/-- The explicit accumulated total-variation majorant tends to zero. -/
theorem tendsto_subpowerKubiliusTVMajorant (K : ℝ) :
    Tendsto (fun T : ℕ =>
      4 * K / (subpowerKubiliusTopLevel T : ℝ) ^ 2 +
        4 * K * (subpowerKubiliusTopLevel T : ℝ) ^ 2 *
          Real.rpow T (-(1 / 2 : ℝ))) atTop (nhds 0) := by
  have htopReal : Tendsto (fun T : ℕ => (subpowerKubiliusTopLevel T : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
        tendsto_subpowerKubiliusTopLevel_atTop
  have hfirst : Tendsto (fun T : ℕ =>
      4 * K / (subpowerKubiliusTopLevel T : ℝ) ^ 2) atTop (nhds 0) := by
    have hrpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp htopReal
    have hsquare : Tendsto (fun T : ℕ =>
        (subpowerKubiliusTopLevel T : ℝ) ^ (2 : ℕ)) atTop atTop := by
      apply hrpow.congr'
      filter_upwards [] with T
      exact Real.rpow_natCast (subpowerKubiliusTopLevel T : ℝ) 2
    have hinv : Tendsto (fun T : ℕ =>
        ((subpowerKubiliusTopLevel T : ℝ) ^ (2 : ℕ))⁻¹) atTop (nhds 0) := by
      have hi := hsquare.inv_tendsto_atTop
      change Tendsto (fun T : ℕ =>
        ((subpowerKubiliusTopLevel T : ℝ) ^ (2 : ℕ))⁻¹) atTop (nhds 0) at hi
      exact hi
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (4 * K)
  have hsecond : Tendsto (fun T : ℕ =>
      4 * K * (subpowerKubiliusTopLevel T : ℝ) ^ 2 *
        Real.rpow T (-(1 / 2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_assoc, mul_zero] using
      tendsto_topLevel_sq_mul_rpow_neg_half.const_mul (4 * K)
  simpa only [zero_add] using hfirst.add hsecond

/-! ### Large shift thresholds -/

/-- Divisor count as a divisibility-indicator sum over a containing interval. -/
lemma card_divisors_eq_sum_Ico {m N : ℕ} (hm : m ≠ 0) (hmN : m < N) :
    m.divisors.card = ∑ k ∈ Finset.Ico 1 N, if k ∣ m then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 1
  ext k
  rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hk, -⟩
    have hkle := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hk
    have hkpos := Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hm)
    exact ⟨⟨by omega, by omega⟩, hk⟩
  · rintro ⟨-, hk⟩
    exact ⟨hk, hm⟩

/-- There are at most `N/k` positive multiples of `k` below `N`. -/
lemma card_multiples_Ico_le (N k : ℕ) (hk : 0 < k) :
    (((Finset.Ico 1 N).filter (fun m => k ∣ m)).card : ℝ) ≤ (N : ℝ) / k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    simp
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have h := Nat.card_multiples' N' k
  have heq : (Finset.Ico 1 (N' + 1)).filter (fun m => k ∣ m) =
      (Finset.range N'.succ).filter (fun m => m ≠ 0 ∧ k ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, Nat.succ_eq_add_one]
    omega
  rw [heq, h]
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    ((N' / k : ℕ) : ℝ) ≤ (N' : ℝ) / k := Nat.cast_div_le
    _ ≤ ((N' + 1 : ℕ) : ℝ) / k := by
      gcongr
      exact_mod_cast Nat.le_succ N'

/-- Elementary upper bound for a finite harmonic interval. -/
lemma sum_Icc_inv_le_subpowerKubilius {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, (k : ℝ)⁻¹ ≤
      1 + Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have haReal : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hinv := inv_le_one_of_one_le₀ haReal
    linarith
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hstep : ((b + 1 : ℕ) : ℝ)⁻¹ ≤
        Real.log (b + 1 : ℕ) - Real.log b := by
      push_cast
      rw [← Real.log_div (by positivity) hb.ne']
      have hlog := Real.one_sub_inv_le_log_of_pos
        (show (0 : ℝ) < (b + 1) / b by positivity)
      rw [inv_div, show (1 : ℝ) - b / (b + 1) = ((b : ℝ) + 1)⁻¹ by
        field_simp
        ring] at hlog
      exact hlog
    linarith

/-- Elementary average-order upper bound for the divisor function. -/
theorem sum_card_divisors_range_le (N : ℕ) :
    ∑ m ∈ Finset.range N, (m.divisors.card : ℝ) ≤
      N * (Real.log N + 1) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N <;> simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : ∑ m ∈ Finset.range N, (m.divisors.card : ℝ) =
      ∑ m ∈ Finset.Ico 1 N,
        ∑ k ∈ Finset.Ico 1 N, (if k ∣ m then (1 : ℝ) else 0) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ N),
      ← Finset.range_eq_Ico, Finset.sum_range_one]
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_add]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ico] at hm
    rw [card_divisors_eq_sum_Ico (by omega) hm.2]
    push_cast
    rfl
  rw [h1, Finset.sum_comm]
  have h2 : ∀ k ∈ Finset.Ico 1 N,
      ∑ m ∈ Finset.Ico 1 N, (if k ∣ m then (1 : ℝ) else 0) ≤ (N : ℝ) / k := by
    intro k hk
    rw [Finset.sum_boole]
    exact card_multiples_Ico_le N k (Finset.mem_Ico.1 hk).1
  calc
    ∑ k ∈ Finset.Ico 1 N,
        ∑ m ∈ Finset.Ico 1 N, (if k ∣ m then (1 : ℝ) else 0) ≤
        ∑ k ∈ Finset.Ico 1 N, (N : ℝ) / k := Finset.sum_le_sum h2
    _ = N * ∑ k ∈ Finset.Icc 1 (N - 1), (k : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      have heq : Finset.Ico 1 N = Finset.Icc 1 (N - 1) := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [heq]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [div_eq_mul_inv]
    _ ≤ N * (1 + Real.log ((N - 1 : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ)) := by
      gcongr
      exact sum_Icc_inv_le_subpowerKubilius le_rfl (by omega)
    _ ≤ N * (Real.log N + 1) := by
      gcongr
      rw [Nat.cast_one, Real.log_one, sub_zero]
      have hcast : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
      have hlog := Real.log_le_log (by exact_mod_cast (show 0 < N - 1 by omega)) hcast
      linarith

open Classical in
/-- Markov's inequality for a marginal-divisor large-value event, dominated by the divisor
function because all marginals are at most one. -/
lemma marginalDivisorMass_large_card_mul_le_sum_card_divisors
    (delta : ℕ → ℝ) (hdelta : ∀ m, delta m ≤ 1)
    (M T : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (((Finset.Icc 1 T).filter (fun n => Y < marginalDivisorMass delta M n)).card : ℝ) * Y ≤
      ∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) := by
  let B := (Finset.Icc 1 T).filter (fun n => Y < marginalDivisorMass delta M n)
  calc
    (B.card : ℝ) * Y = ∑ _n ∈ B, Y := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ B, marginalDivisorMass delta M n := by
      exact Finset.sum_le_sum fun n hn => (Finset.mem_filter.mp hn).2.le
    _ ≤ ∑ n ∈ B, (n.divisors.card : ℝ) := by
      exact Finset.sum_le_sum fun n _ => marginalDivisorMass_le_card_divisors delta hdelta M n
    _ ≤ ∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)

/-- Geometric pointwise bound for a large marginal-divisor event at shift threshold `j`. -/
lemma marginalDivisorMass_large_card_le_geometric
    (delta : ℕ → ℝ) (hdelta : ∀ m, delta m ≤ 1)
    (M T j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (((Finset.Icc 1 T).filter (fun n =>
      ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ) ≤
      (((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1) / ε) *
        (Real.rpow 2 (-(1 / 2 : ℝ))) ^ j := by
  let Y : ℝ := ε * Real.rpow 2 ((j : ℝ) / 2)
  let S : ℝ := ((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1)
  have hY : 0 < Y := by
    dsimp only [Y]
    exact mul_pos hε (Real.rpow_pos_of_pos (by norm_num) _)
  have hmarkov := marginalDivisorMass_large_card_mul_le_sum_card_divisors
    delta hdelta M T Y hY.le
  have hsubset : Finset.Icc 1 T ⊆ Finset.range (T + 1) := by
    intro n hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2
  have hsum : (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ)) ≤ S := by
    calc
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ)) ≤
          ∑ n ∈ Finset.range (T + 1), (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
      _ ≤ S := by simpa only [S] using sum_card_divisors_range_le (T + 1)
  have hcard :
      (((Finset.Icc 1 T).filter (fun n =>
        ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ) ≤
        S / Y := by
    apply (le_div_iff₀ hY).2
    exact hmarkov.trans hsum
  have hpow :
      (Real.rpow 2 ((j : ℝ) / 2))⁻¹ =
        (Real.rpow 2 (-(1 / 2 : ℝ))) ^ j := by
    rw [show (Real.rpow 2 ((j : ℝ) / 2))⁻¹ =
      Real.rpow 2 (-((j : ℝ) / 2)) from
        (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((j : ℝ) / 2)).symm]
    rw [show (Real.rpow 2 (-(1 / 2 : ℝ))) ^ j =
      Real.rpow 2 (-(1 / 2 : ℝ) * j) from
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) _ j).symm]
    congr 1
    ring
  calc
    (((Finset.Icc 1 T).filter (fun n =>
      ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ) ≤
        S / Y := hcard
    _ = (S / ε) * (Real.rpow 2 (-(1 / 2 : ℝ))) ^ j := by
      dsimp only [Y]
      rw [div_eq_mul_inv, mul_inv_rev, hpow]
      ring
    _ = (((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1) / ε) *
        (Real.rpow 2 (-(1 / 2 : ℝ))) ^ j := rfl

/-- The sum over all shift thresholds `j ∈ [J₀,J)` is bounded by a geometric tail. -/
theorem sum_marginalDivisorMass_large_cards_Ico_le
    (delta : ℕ → ℝ) (hdelta : ∀ m, delta m ≤ 1)
    (M T J₀ J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∑ j ∈ Finset.Ico J₀ J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ)) ≤
      (((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1) / ε) *
        ((Real.rpow 2 (-(1 / 2 : ℝ))) ^ J₀ /
          (1 - Real.rpow 2 (-(1 / 2 : ℝ)))) := by
  let q : ℝ := Real.rpow 2 (-(1 / 2 : ℝ))
  let C : ℝ := ((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1) / ε
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have hlog : 0 ≤ Real.log ((T + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ T + 1 by omega))
    exact div_nonneg
      (mul_nonneg (by positivity)
        (by linarith))
      hε.le
  calc
    (∑ j ∈ Finset.Ico J₀ J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ)) ≤
        ∑ j ∈ Finset.Ico J₀ J, C * q ^ j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [C, q] using
        marginalDivisorMass_large_card_le_geometric delta hdelta M T j ε hε
    _ = C * ∑ j ∈ Finset.Ico J₀ J, q ^ j := by rw [Finset.mul_sum]
    _ ≤ C * (q ^ J₀ / (1 - q)) := by
      exact mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) hC0
    _ = (((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1) / ε) *
        ((Real.rpow 2 (-(1 / 2 : ℝ))) ^ J₀ /
          (1 - Real.rpow 2 (-(1 / 2 : ℝ)))) := rfl

/-- The logarithmic factor in the elementary divisor-average bound is at most exponential in the
exact dyadic top level.  This is paired below with twice that much geometric decay. -/
lemma log_succ_add_one_le_topLevel_pow (T : ℕ)
    (hH : 1 ≤ subpowerKubiliusTopLevel T) :
    Real.log (T + 1 : ℕ) + 1 ≤
      5 * Real.log 2 * (2 : ℝ) ^ subpowerKubiliusTopLevel T := by
  let A := Nat.log 2 T
  let H := subpowerKubiliusTopLevel T
  have hA0 : A ≠ 0 := by
    intro hA
    have hHzero : H = 0 := by simp [H, subpowerKubiliusTopLevel, A, hA]
    omega
  have hT0 : T ≠ 0 := by
    intro hT
    subst T
    simp [A] at hA0
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT0
  have hAupper : A + 1 ≤ 2 ^ (H + 1) := by
    have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) A
    have hle : A + 1 ≤ 2 ^ (Nat.log 2 A + 1) := by omega
    simpa only [H, subpowerKubiliusTopLevel, A] using hle
  have hTupper : T ≤ 2 ^ (A + 1) := by
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) T).le
  have hlogT : Real.log (T : ℝ) ≤
      (2 : ℝ) ^ (H + 1) * Real.log 2 := by
    calc
      Real.log (T : ℝ) ≤ Real.log ((2 : ℝ) ^ (A + 1)) := by
        apply Real.log_le_log (by exact_mod_cast hTpos)
        exact_mod_cast hTupper
      _ = ((A + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
      _ ≤ ((2 ^ (H + 1) : ℕ) : ℝ) * Real.log 2 := by
        gcongr
      _ = (2 : ℝ) ^ (H + 1) * Real.log 2 := by push_cast; ring
  have hsucc : Real.log (T + 1 : ℕ) ≤
      Real.log 2 + (2 : ℝ) ^ (H + 1) * Real.log 2 := by
    calc
      Real.log (T + 1 : ℕ) ≤ Real.log ((2 : ℕ) * T : ℕ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show T + 1 ≤ 2 * T by omega)
      _ = Real.log 2 + Real.log T := by
        push_cast
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by exact_mod_cast hT0)]
      _ ≤ Real.log 2 + (2 : ℝ) ^ (H + 1) * Real.log 2 := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog20 : 0 ≤ Real.log 2 := by positivity
  have hpowone : (1 : ℝ) ≤ (2 : ℝ) ^ H := one_le_pow₀ (by norm_num)
  have hlog_le : Real.log 2 ≤ (2 : ℝ) ^ H * Real.log 2 := by
    nlinarith
  have hone_le : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ H * Real.log 2 := by
    nlinarith
  rw [pow_succ] at hsucc
  dsimp only [H] at hsucc ⊢
  nlinarith

/-- Four top-level units of the geometric threshold cost exactly one fourth per top level. -/
lemma rpow_neg_half_pow_four_mul (H : ℕ) :
    (Real.rpow 2 (-(1 / 2 : ℝ))) ^ (4 * H) = (1 / 4 : ℝ) ^ H := by
  rw [pow_mul]
  congr 1
  rw [show (Real.rpow 2 (-(1 / 2 : ℝ))) ^ 4 =
      Real.rpow 2 (-(1 / 2 : ℝ) * 4) from
    (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) _ 4).symm]
  norm_num

lemma two_pow_mul_rpow_neg_half_pow_four_mul (H : ℕ) :
    (2 : ℝ) ^ H * (Real.rpow 2 (-(1 / 2 : ℝ))) ^ (4 * H) =
      (1 / 2 : ℝ) ^ H := by
  rw [rpow_neg_half_pow_four_mul]
  rw [← mul_pow]
  congr 1
  norm_num

open Classical in
/-- After truncating at four times the exact top level, the entire remaining shift tail is bounded
by a fixed constant times `2⁻ᴴ`. -/
theorem sum_marginalDivisorMass_large_cards_high_div_le
    (delta : ℕ → ℝ) (hdelta : ∀ m, delta m ≤ 1)
    (M T J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hH : 1 ≤ subpowerKubiliusTopLevel T) :
    (∑ j ∈ Finset.Ico (4 * subpowerKubiliusTopLevel T) J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ)) / T ≤
      ((10 * Real.log 2 / ε) /
          (1 - Real.rpow 2 (-(1 / 2 : ℝ)))) *
        (1 / 2 : ℝ) ^ subpowerKubiliusTopLevel T := by
  let H := subpowerKubiliusTopLevel T
  let q : ℝ := Real.rpow 2 (-(1 / 2 : ℝ))
  let P : ℝ := (2 : ℝ) ^ H
  let R : ℝ := q ^ (4 * H)
  let a : ℝ := ((T + 1 : ℕ) : ℝ) / T
  let b : ℝ := (Real.log (T + 1 : ℕ) + 1) / ε
  let d : ℝ := 1 / (1 - q)
  have hT0 : T ≠ 0 := by
    intro hT
    subst T
    simp [subpowerKubiliusTopLevel] at hH
  have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT0
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have ha : a ≤ 2 := by
    dsimp only [a]
    rw [div_le_iff₀ hTpos]
    exact_mod_cast (show T + 1 ≤ 2 * T by omega)
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact div_nonneg
      (add_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ T + 1 by omega)))
        zero_le_one)
      hε.le
  have hB0 : 0 ≤ (5 * Real.log 2 * P) / ε := by
    dsimp only [P]
    positivity
  have hb : b ≤ (5 * Real.log 2 * P) / ε := by
    dsimp only [b, P, H]
    exact div_le_div_of_nonneg_right
      (log_succ_add_one_le_topLevel_pow T hH) hε.le
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hab : a * b ≤ 2 * ((5 * Real.log 2 * P) / ε) :=
    mul_le_mul ha hb hb0 (by norm_num)
  have hraw := sum_marginalDivisorMass_large_cards_Ico_le
    delta hdelta M T (4 * H) J ε hε
  calc
    (∑ j ∈ Finset.Ico (4 * subpowerKubiliusTopLevel T) J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M n)).card : ℝ)) / T ≤
        ((((T + 1 : ℕ) : ℝ) * (Real.log (T + 1 : ℕ) + 1) / ε) *
          (q ^ (4 * H) / (1 - q))) / T := by
      apply div_le_div_of_nonneg_right
      · simpa only [H, q] using hraw
      · positivity
    _ = a * b * d * R := by
      dsimp only [a, b, d, R]
      field_simp [hT0, hε.ne', hden.ne']
    _ ≤ 2 * ((5 * Real.log 2 * P) / ε) * d * R := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hab hd0) hR0
    _ = ((10 * Real.log 2 / ε) / (1 - q)) * (P * R) := by
      dsimp only [d]
      ring
    _ = ((10 * Real.log 2 / ε) /
          (1 - Real.rpow 2 (-(1 / 2 : ℝ)))) *
        (1 / 2 : ℝ) ^ subpowerKubiliusTopLevel T := by
      rw [show P * R = (1 / 2 : ℝ) ^ H by
        simpa only [P, R, q] using
          two_pow_mul_rpow_neg_half_pow_four_mul H]

/-- The explicit high-shift envelope tends to zero. -/
lemma tendsto_subpowerKubiliusHighShiftEnvelope (ε : ℝ) :
    Tendsto (fun T : ℕ =>
      ((10 * Real.log 2 / ε) /
          (1 - Real.rpow 2 (-(1 / 2 : ℝ)))) *
        (1 / 2 : ℝ) ^ subpowerKubiliusTopLevel T) atTop (nhds 0) := by
  have hpow : Tendsto (fun H : ℕ => (1 / 2 : ℝ) ^ H) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcomp := hpow.comp tendsto_subpowerKubiliusTopLevel_atTop
  simpa only [Function.comp_def, mul_zero] using hcomp.const_mul
    ((10 * Real.log 2 / ε) / (1 - Real.rpow 2 (-(1 / 2 : ℝ))))

open Classical in
/-- The shifts beyond the Kubilius truncation are uniformly negligible once the divisor cutoff is
late.  For small averaging ranges the marginal mass vanishes identically; for large ranges the
geometric envelope applies. -/
theorem exists_sum_marginalDivisorMass_large_cards_high_div_lt
    (delta : ℕ → ℝ) (hdelta : ∀ m, delta m ≤ 1)
    (ε ζ : ℝ) (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ,
      (∑ j ∈ Finset.Ico (4 * subpowerKubiliusTopLevel T) J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T < ζ := by
  have hev : ∀ᶠ T : ℕ in atTop,
      ((10 * Real.log 2 / ε) /
          (1 - Real.rpow 2 (-(1 / 2 : ℝ)))) *
        (1 / 2 : ℝ) ^ subpowerKubiliusTopLevel T < ζ :=
    (tendsto_subpowerKubiliusHighShiftEnvelope ε).eventually_lt_const hζ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1
    (hev.and (tendsto_subpowerKubiliusTopLevel_atTop.eventually_ge_atTop 1))
  let L₀ := max T₀ 6
  refine ⟨L₀, by simp [L₀], ?_⟩
  intro L hL T J
  by_cases hlarge : T₀ ≤ T
  · have hdata := hT₀ T hlarge
    exact (sum_marginalDivisorMass_large_cards_high_div_le
      delta hdelta (dyadicExpCutoff L) T J ε hε hdata.2).trans_lt hdata.1
  · have hTL : T ≤ dyadicExpCutoff L := by
      have hTL' : T ≤ L := by
        have hTlt : T < T₀ := Nat.lt_of_not_ge hlarge
        have hT₀L : T₀ ≤ L := (le_max_left T₀ 6).trans hL
        omega
      exact hTL'.trans (by simpa using index_le_dyadicExpCutoff_add 0 L)
    have hzero : ∀ j : ℕ,
        (Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n) = ∅ := by
      intro j
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn
      have hnT := (Finset.mem_Icc.mp hn).2
      have hmass := marginalDivisorMass_eq_zero_of_le delta (dyadicExpCutoff L) n
        (hnT.trans hTL)
      rw [hmass]
      exact (not_lt_of_ge
        (mul_nonneg hε.le (Real.rpow_nonneg (by norm_num) _)))
    simp only [hzero, Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div]
    exact hζ

lemma summable_blockLogLog_neg_rpow {D : ℝ} (hD : 1 < D) :
    Summable (fun ℓ : ℕ ↦ Real.rpow (blockLogLog ℓ) (-D)) := by
  have hseries₀ : Summable (fun ℓ : ℕ ↦
      1 / |(ℓ : ℝ) + 2| ^ D) :=
    (Real.summable_one_div_nat_add_rpow 2 D).2 hD
  have hseries : Summable (fun ℓ : ℕ ↦
      Real.rpow ((ℓ : ℝ) + 2) (-D)) := by
    apply hseries₀.congr
    intro ℓ
    change 1 / |(ℓ : ℝ) + 2| ^ D = ((ℓ : ℝ) + 2) ^ (-D)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (ℓ : ℝ) + 2)]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) + 2)]
    rw [one_div]
  have hsum : Summable (fun ℓ : ℕ ↦ Real.rpow 4 D *
      Real.rpow ((ℓ : ℝ) + 2) (-D)) := hseries.mul_left _
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 6] with ℓ hℓ
  let u : ℝ := blockLogLog ℓ
  let v : ℝ := (ℓ : ℝ) + 2
  have hu₀ : 0 < u := by
    dsimp only [u]
    exact (by positivity : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4).trans_le
      (blockLogLog_ge_quarter_add ℓ hℓ)
  have hv₀ : 0 < v := by
    dsimp only [v]
    positivity
  have huv : v / 4 ≤ u := by
    simpa only [u, v] using blockLogLog_ge_quarter_add ℓ hℓ
  have hpow : Real.rpow u (-D) ≤
      Real.rpow 4 D * Real.rpow v (-D) := by
    calc
      Real.rpow u (-D) ≤ Real.rpow (v / 4) (-D) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) huv (by linarith)
      _ = Real.rpow 4 D * Real.rpow v (-D) := by
        change (v / 4) ^ (-D) = 4 ^ D * v ^ (-D)
        rw [Real.div_rpow hv₀.le (by norm_num : (0 : ℝ) ≤ 4)]
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv, inv_inv]
        ring
  have hrpow₀ : 0 ≤ Real.rpow u (-D) := by
    rw [Real.rpow_eq_pow]
    exact Real.rpow_nonneg hu₀.le _
  calc
    |Real.rpow u (-D)| = Real.rpow u (-D) := abs_of_nonneg hrpow₀
    _ ≤ Real.rpow 4 D * Real.rpow v (-D) := hpow

open Classical in
/-- The complete square-divisor contribution in the canonical grouped bound is uniformly small
once the first arithmetic level is late enough.  The exponent may be any `D > 1`; later assembly
can take `D = 2`. -/
theorem exists_subpowerKubiliusCanonical_square_sum_lt
    (D ζ : ℝ) (hD : 1 < D) (hζ : 0 < ζ) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ (c : ℝ) (L T Y : ℕ), L₀ ≤ L →
      (∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
        ∑ ℓ ∈ s, squareDivisorMomentConstant *
          Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) < ζ := by
  let f : ℕ → ℝ := fun ℓ ↦ squareDivisorMomentConstant *
    Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant
  have hsumBase := summable_blockLogLog_neg_rpow hD
  have hsum : Summable f := by
    refine (hsumBase.mul_left
      (squareDivisorMomentConstant * subpowerSquareShiftConstant)).congr ?_
    intro ℓ
    dsimp only [f]
    ring
  have hf₀ : ∀ ℓ, 6 ≤ ℓ → 0 ≤ f ℓ := by
    intro ℓ hℓ
    have hlog : 0 ≤ blockLogLog ℓ := by
      exact (by positivity : (0 : ℝ) ≤ ((ℓ : ℝ) + 2) / 4).trans
        (blockLogLog_ge_quarter_add ℓ hℓ)
    dsimp only [f]
    exact mul_nonneg
      (mul_nonneg squareDivisorMomentConstant_nonneg
        (Real.rpow_nonneg hlog _))
      subpowerSquareShiftConstant_pos.le
  have htailEv : ∀ᶠ L : ℕ in atTop, (∑' i : ℕ, f (i + L)) < ζ :=
    (tendsto_sum_nat_add f).eventually_lt_const hζ
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1
    (htailEv.and (eventually_ge_atTop 6))
  have hL₀data := hL₀ L₀ le_rfl
  refine ⟨L₀, hL₀data.2, ?_⟩
  intro c L T Y hL
  have hdata := hL₀ L hL
  have hoffsetInj : Set.InjOn (fun ℓ : ℕ ↦ ℓ - L)
      (subpowerKubiliusOrdinaryLevels L T Y : Set ℕ) := by
    intro a ha b hb hab
    have haL := (mem_subpowerKubiliusOrdinaryLevels.mp ha).1
    have hbL := (mem_subpowerKubiliusOrdinaryLevels.mp hb).1
    calc
      a = (a - L) + L := (Nat.sub_add_cancel haL).symm
      _ = (b - L) + L := congrArg (fun n ↦ n + L) hab
      _ = b := Nat.sub_add_cancel hbL
  have hrewrite :
      (∑ ℓ ∈ subpowerKubiliusOrdinaryLevels L T Y, f ℓ) =
        ∑ i ∈ (subpowerKubiliusOrdinaryLevels L T Y).image (fun ℓ ↦ ℓ - L),
          f (i + L) := by
    calc
      (∑ ℓ ∈ subpowerKubiliusOrdinaryLevels L T Y, f ℓ) =
          ∑ ℓ ∈ subpowerKubiliusOrdinaryLevels L T Y, f ((ℓ - L) + L) := by
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Nat.sub_add_cancel (mem_subpowerKubiliusOrdinaryLevels.mp hℓ).1]
      _ = ∑ i ∈ (subpowerKubiliusOrdinaryLevels L T Y).image (fun ℓ ↦ ℓ - L),
          f (i + L) :=
        (Finset.sum_image (f := fun i ↦ f (i + L)) hoffsetInj).symm
  have hshift : Summable (fun i : ℕ ↦ f (i + L)) :=
    hsum.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hfinite :
      (∑ i ∈ (subpowerKubiliusOrdinaryLevels L T Y).image (fun ℓ ↦ ℓ - L),
        f (i + L)) ≤ ∑' i : ℕ, f (i + L) :=
    hshift.sum_le_tsum _ (fun i _ ↦ hf₀ (i + L) (by omega))
  calc
    (∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
        ∑ ℓ ∈ s, squareDivisorMomentConstant *
          Real.rpow (blockLogLog ℓ) (-D) * subpowerSquareShiftConstant) =
        ∑ ℓ ∈ subpowerKubiliusOrdinaryLevels L T Y, f ℓ := by
      change (∑ s ∈ subpowerKubiliusLevelGroups c L T Y, ∑ ℓ ∈ s, f ℓ) = _
      rw [← Finset.sum_biUnion
        (subpowerKubiliusLevelGroups_pairwiseDisjoint c L T Y),
        subpowerKubiliusLevelGroups_biUnion]
    _ = ∑ i ∈ (subpowerKubiliusOrdinaryLevels L T Y).image (fun ℓ ↦ ℓ - L),
        f (i + L) := hrewrite
    _ ≤ ∑' i : ℕ, f (i + L) := hfinite
    _ < ζ := hdata.1

open Classical in
/-- The model-crossing contribution in the canonical grouped bound is uniformly small once the
starting arithmetic level is late enough.  The proof reindexes the nonempty canonical fibers by
their distinct geometric schedule indices and applies the sparse finite-family model tail. -/
theorem exists_subpowerKubiliusCanonical_model_sum_lt
    (c C ε D ζ : ℝ) (hc : 1 < c) (hD : 0 ≤ D)
    (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ L T Y J : ℕ,
      (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
        Real.log (Real.log (subpowerKubiliusGroupCutoff s : ℝ)) +
            Erdos67.PrimeEstimates.mertensBound ≤
          kubiliusBlockRatio (subpowerKubiliusModelCoefficient c) *
            subpowerKubiliusGroupAnchor c s) →
      (∀ s ∈ subpowerKubiliusLevelGroups c L T Y,
        K₀ ≤ subpowerKubiliusGroupingIndex c (s.sup id)) →
      (∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
        4 * kubiliusPrimeCutoffLoweredCrossingMass
          (subpowerKubiliusGroupCutoff s)
          (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
            (subpowerKubiliusLossB (ε / C)) (subpowerKubiliusGroupAnchor c s)
              ((J + 3) / 4)) < ζ := by
  have hmodelc : 1 < subpowerKubiliusModelCoefficient c :=
    one_lt_subpowerKubiliusModelCoefficient hc
  have hq : 1 < subpowerKubiliusGroupingRatio c :=
    one_lt_subpowerKubiliusGroupingRatio hc
  have hA : 0 ≤ subpowerKubiliusLossA D := subpowerKubiliusLossA_nonneg D hD
  have hB : 0 ≤ subpowerKubiliusLossB (ε / C) :=
    subpowerKubiliusLossB_nonneg (ε / C)
  obtain ⟨K₀, htail⟩ :=
    exists_kubiliusPrimeCutoffLoweredCrossingMass_injective_sum_lt_of_ratio
      hmodelc hq (subpowerKubiliusLossA D) (subpowerKubiliusLossB (ε / C))
        hA hB (ζ / 4) (by positivity)
  refine ⟨K₀, ?_⟩
  intro L T Y J hvar hlate
  let groups := subpowerKubiliusLevelGroups c L T Y
  have hraw := htail groups
    (fun s ↦ subpowerKubiliusGroupingIndex c (s.sup id))
    subpowerKubiliusGroupCutoff (fun _ ↦ (J + 3) / 4)
    (subpowerKubiliusLevelGroup_index_injOn c L T Y) hlate
    (fun s hs ↦ ⟨dyadicExpCutoff_two_le _, hvar s hs⟩)
  calc
    (∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
        4 * kubiliusPrimeCutoffLoweredCrossingMass
          (subpowerKubiliusGroupCutoff s)
          (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
            (subpowerKubiliusLossB (ε / C)) (subpowerKubiliusGroupAnchor c s)
              ((J + 3) / 4)) =
        4 * ∑ s ∈ subpowerKubiliusLevelGroups c L T Y,
          kubiliusPrimeCutoffLoweredCrossingMass
            (subpowerKubiliusGroupCutoff s)
            (subpowerKubiliusModelCoefficient c) (subpowerKubiliusLossA D)
              (subpowerKubiliusLossB (ε / C)) (subpowerKubiliusGroupAnchor c s)
                ((J + 3) / 4) := by rw [Finset.mul_sum]
    _ < 4 * (ζ / 4) := mul_lt_mul_of_pos_left hraw (by norm_num)
    _ = ζ := by ring

open Classical in
/-- The canonical Kubilius estimate controls every threshold below four times the exact top level.
The four displayed terms are each assigned one quarter of the requested error. -/
theorem exists_subpower_marginal_large_cards_truncated_div_lt_of_kubilius
    (hKub : KubiliusTV)
    (c C ε ζ : ℝ) (hc : 1 < c) (hC : 0 < C) (hε : 0 < ε) (hζ : 0 < ζ)
    (delta : ℕ → ℝ)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ,
      J ≤ 4 * subpowerKubiliusTopLevel T →
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T < ζ := by
  have hquarter : 0 < ζ / 4 := by positivity
  have hA : 0 < ε / C := div_pos hε hC
  obtain ⟨K, hKpos, hcanonical⟩ :=
    exists_sum_marginalDivisorMass_large_cards_div_le_canonical_kubilius hKub
  obtain ⟨K₀, hmodel⟩ :=
    exists_subpowerKubiliusCanonical_model_sum_lt c C ε 2 (ζ / 4)
      hc (by norm_num) hquarter
  obtain ⟨Lc, hLc6, hcanonicalAll⟩ :=
    hcanonical c C ε 2 delta hc hC hε (by norm_num) hdelta K₀
  obtain ⟨Le, hLe6, hexceptional⟩ :=
    exists_subpowerKubiliusExceptional_union_large_cards_div_lt
      c (ε / C) (ζ / 4) hc hA hquarter
  obtain ⟨Ls, hLs6, hsquare⟩ :=
    exists_subpowerKubiliusCanonical_square_sum_lt 2 (ζ / 4)
      (by norm_num) hquarter
  have htvEv : ∀ᶠ T : ℕ in atTop,
      4 * K / (subpowerKubiliusTopLevel T : ℝ) ^ 2 +
          4 * K * (subpowerKubiliusTopLevel T : ℝ) ^ 2 *
            Real.rpow T (-(1 / 2 : ℝ)) < ζ / 4 :=
    (tendsto_subpowerKubiliusTVMajorant K).eventually_lt_const hquarter
  have hall : ∀ᶠ T : ℕ in atTop,
      (4 * K / (subpowerKubiliusTopLevel T : ℝ) ^ 2 +
          4 * K * (subpowerKubiliusTopLevel T : ℝ) ^ 2 *
            Real.rpow T (-(1 / 2 : ℝ)) < ζ / 4) ∧
        32 ≤ subpowerKubiliusTopLevel T ∧ 1 ≤ T := by
    filter_upwards [htvEv,
      tendsto_subpowerKubiliusTopLevel_atTop.eventually_ge_atTop 32,
      eventually_ge_atTop 1] with T htv hH hT
    exact ⟨htv, hH, hT⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hall
  let L₀ := max (max (max Lc Le) Ls) (max T₀ 6)
  refine ⟨L₀, by simp [L₀], ?_⟩
  intro L hL T J hJ
  by_cases hlarge : T₀ ≤ T
  · have hdata := hT₀ T hlarge
    have hLcL : Lc ≤ L := by
      exact (le_max_left Lc Le |>.trans (le_max_left (max Lc Le) Ls) |>.trans
        (le_max_left (max (max Lc Le) Ls) (max T₀ 6))).trans hL
    have hLeL : Le ≤ L := by
      exact (le_max_right Lc Le |>.trans (le_max_left (max Lc Le) Ls) |>.trans
        (le_max_left (max (max Lc Le) Ls) (max T₀ 6))).trans hL
    have hLsL : Ls ≤ L := by
      exact (le_max_right (max Lc Le) Ls |>.trans
        (le_max_left (max (max Lc Le) Ls) (max T₀ 6))).trans hL
    have hTpos : 0 < T := by omega
    have hYT : subpowerKubiliusCommonCutoff T ≤ T :=
      subpowerKubiliusCommonCutoff_le (by omega)
    have hcan := hcanonicalAll L hLcL T (subpowerKubiliusCommonCutoff T) J
      hTpos hYT
    have he := hexceptional L hLeL T J
    have hs := hsquare c L T (subpowerKubiliusCommonCutoff T) hLsL
    have hm := hmodel L T (subpowerKubiliusCommonCutoff T) J hcan.2.1 hcan.2.2
    have htvle := subpowerKubiliusCanonical_tv_sum_commonCutoff_le
      K c L T J hKpos.le hdata.2.1 hJ
    have htv :
        (∑ s ∈ subpowerKubiliusLevelGroups c L T
            (subpowerKubiliusCommonCutoff T),
          J * K * (Real.rpow
            (Real.log T / Real.log (subpowerKubiliusGroupCutoff s))
            (-(Real.log T / Real.log (subpowerKubiliusGroupCutoff s))) +
              Real.rpow T (-(1 / 2 : ℝ)))) < ζ / 4 :=
      htvle.trans_lt hdata.1
    have hbound :
        subpowerKubiliusCanonicalGroupedBound K c C ε 2 L T J
          (subpowerKubiliusCommonCutoff T) < ζ := by
      unfold subpowerKubiliusCanonicalGroupedBound
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      linarith
    exact hcan.1.trans_lt hbound
  · have hTL : T ≤ dyadicExpCutoff L := by
      have hTlt : T < T₀ := Nat.lt_of_not_ge hlarge
      have hT₀L : T₀ ≤ L := by
        exact (le_max_left T₀ 6 |>.trans
          (le_max_right (max (max Lc Le) Ls) (max T₀ 6))).trans hL
      have hTL' : T ≤ L := by omega
      exact hTL'.trans (by simpa using index_le_dyadicExpCutoff_add 0 L)
    have hzero : ∀ j : ℕ,
        (Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n) = ∅ := by
      intro j
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn
      have hnT := (Finset.mem_Icc.mp hn).2
      rw [marginalDivisorMass_eq_zero_of_le delta (dyadicExpCutoff L) n
        (hnT.trans hTL)]
      exact not_lt_of_ge (mul_nonneg hε.le (Real.rpow_nonneg (by norm_num) _))
    simp only [hzero, Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div]
    exact hζ

open Classical in
/-- Uniform large-marginal density estimate for all shift thresholds.  The initial `4H` shifts use
the canonical Kubilius argument, while the remaining shifts use the elementary geometric tail. -/
theorem exists_subpower_marginal_large_cards_div_lt_of_kubilius
    (hKub : KubiliusTV)
    (c C ε ζ : ℝ) (hc : 1 < c) (hC : 0 < C) (hε : 0 < ε) (hζ : 0 < ζ)
    (delta : ℕ → ℝ) (hdeltaUpper : ∀ m, delta m ≤ 1)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T < ζ := by
  have hhalf : 0 < ζ / 2 := by positivity
  obtain ⟨Lt, hLt6, htruncated⟩ :=
    exists_subpower_marginal_large_cards_truncated_div_lt_of_kubilius
      hKub c C ε (ζ / 2) hc hC hε hhalf delta hdelta
  obtain ⟨Lh, hLh6, hhigh⟩ :=
    exists_sum_marginalDivisorMass_large_cards_high_div_lt
      delta hdeltaUpper ε (ζ / 2) hε hhalf
  let L₀ := max Lt Lh
  refine ⟨L₀, by simp [L₀, hLt6, hLh6], ?_⟩
  intro L hL T J
  have hLtL : Lt ≤ L := (le_max_left Lt Lh).trans hL
  have hLhL : Lh ≤ L := (le_max_right Lt Lh).trans hL
  by_cases hJ : J ≤ 4 * subpowerKubiliusTopLevel T
  · exact (htruncated L hLtL T J hJ).trans (by linarith)
  · have hcutJ : 4 * subpowerKubiliusTopLevel T ≤ J := Nat.le_of_not_ge hJ
    have hlow := htruncated L hLtL T
      (4 * subpowerKubiliusTopLevel T) le_rfl
    have htail := hhigh L hLhL T J
    calc
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T =
          (∑ j ∈ Finset.range (4 * subpowerKubiliusTopLevel T),
            (((Finset.Icc 1 T).filter (fun n =>
              ε * Real.rpow 2 ((j : ℝ) / 2) <
                marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T +
          (∑ j ∈ Finset.Ico (4 * subpowerKubiliusTopLevel T) J,
            (((Finset.Icc 1 T).filter (fun n =>
              ε * Real.rpow 2 ((j : ℝ) / 2) <
                marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) / T := by
        rw [← add_div, Finset.sum_range_add_sum_Ico _ hcutJ]
      _ < ζ := by linarith

open Classical in
/-- Unnormalized form of the uniform large-marginal estimate used by the deterministic residual
criterion. -/
theorem exists_subpower_marginal_large_cards_le_of_kubilius
    (hKub : KubiliusTV)
    (c C ε ζ : ℝ) (hc : 1 < c) (hC : 0 < C) (hε : 0 < ε) (hζ : 0 < ζ)
    (delta : ℕ → ℝ) (hdeltaUpper : ∀ m, delta m ≤ 1)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∃ L₀ : ℕ, 6 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) ≤ ζ * T := by
  obtain ⟨L₀, hL₀, hnorm⟩ :=
    exists_subpower_marginal_large_cards_div_lt_of_kubilius
      hKub c C ε ζ hc hC hε hζ delta hdeltaUpper hdelta
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL T J
  by_cases hT0 : T = 0
  · subst T
    simp
  · have hT : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT0
    exact ((div_lt_iff₀ hT).mp (hnorm L hL T J)).le

/-- The deterministic capped residual becomes uniformly small under the sub-power domination
hypothesis for every `c > 1`, using `KubiliusTV` only through the large-card estimate above. -/
lemma subpower_capped_marginal_residual_small_of_kubilius
    (hKub : KubiliusTV)
    (delta : ℕ → ℝ) (hdeltaRange : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1)
    (c C : ℝ) (hc : 1 < c) (hC : 0 < C)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∀ b : ℕ, 2 ≤ b → ∀ η : ℝ, 0 < η →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
        cappedMarginalResidualAverage b delta M N ≤ η := by
  intro b hb η hη
  let G : ℝ := ∑' j : ℕ, residualGoodMajorant j
  have hG : 0 ≤ G := tsum_nonneg fun j => by
    unfold residualGoodMajorant
    exact mul_nonneg (by norm_num)
      (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  have hG1 : 0 < G + 1 := by linarith
  let ε : ℝ := η / (4 * (G + 1))
  let ζ : ℝ := η / 12
  let τ : ℝ := η / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨L₀, hL₀, hlargeAll⟩ :=
    exists_subpower_marginal_large_cards_le_of_kubilius
      hKub c C ε ζ hc hC hε hζ delta (fun m => (hdeltaRange m).2) hdelta
  have htailEv : ∀ᶠ J : ℕ in atTop,
      (∑' k : ℕ, residualTailMajorant (k + J)) < τ :=
    (tendsto_sum_nat_add residualTailMajorant).eventually_lt_const hτ
  obtain ⟨K, htailK⟩ := eventually_atTop.1 htailEv
  let L := L₀ + 3 * K
  let M := dyadicExpCutoff L
  have hL : L₀ ≤ L := by dsimp [L]; omega
  have hMK : 3 * K ≤ M := by
    dsimp [M, L]
    exact index_le_dyadicExpCutoff_add L₀ (3 * K)
  have hlarge : ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta M n)).card : ℝ)) ≤ ζ * T := by
    simpa [M] using hlargeAll L hL
  have htail : ∀ J : ℕ, K ≤ J →
      (∑' k : ℕ, residualTailMajorant (k + J)) ≤ τ := by
    intro J hKJ
    exact (htailK J hKJ).le
  refine ⟨M, ?_, ?_⟩
  · exact dyadicExpCutoff_two_le L
  intro N hN
  have havg := cappedMarginalResidualAverage_le_of_large_cards
    b hb delta hdeltaRange M K hMK ε ζ τ hε.le hζ.le hlarge htail N hN
  have hgood : ε * G ≤ η / 4 := by
    calc
      ε * G ≤ ε * (G + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = η / 4 := by
        dsimp [ε]
        field_simp [ne_of_gt hG1]
  calc
    cappedMarginalResidualAverage b delta M N ≤ ε * G + τ + 3 * ζ := by
      simpa [G] using havg
    _ ≤ η / 4 + η / 4 + 3 * (η / 12) := by
      dsimp [τ, ζ]
      gcongr
    _ ≤ η := by linarith

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
  have hX' := hX
  obtain ⟨hdeltaRange, _hMeas, _hIndep, _hLaw⟩ := hX
  have hweight : 0 < subpowerWeight c 2 := by
    unfold subpowerWeight
    exact mul_pos (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _)
      (Real.exp_pos _)
  have hprod : 0 ≤ C * subpowerWeight c 2 :=
    (hdeltaRange 2).1.trans (hdelta 2 (by omega))
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left hprod hweight
  apply ae_not_normal_of_capped_marginal_residual μ delta X hX'
  by_cases hC0 : C = 0
  · intro b hb η hη
    have hdeltaZero : ∀ m : ℕ, 2 ≤ m → delta m = 0 := by
      intro m hm
      apply le_antisymm
      · simpa [hC0] using hdelta m hm
      · exact (hdeltaRange m).1
    refine ⟨2, by omega, ?_⟩
    intro N hN
    have hmass : ∀ n : ℕ, marginalDivisorMass delta 2 n = 0 := by
      intro n
      unfold marginalDivisorMass
      apply Finset.sum_eq_zero
      intro m hm
      exact hdeltaZero m (by
        have hm2 := (Finset.mem_filter.mp hm).2
        omega)
    have hres : ∀ n : ℕ, marginalShiftResidual b delta 2 n = 0 := by
      intro n
      unfold marginalShiftResidual
      simp only [hmass, mul_zero, tsum_zero]
    unfold cappedMarginalResidualAverage
    simp [hres, hη.le]
  · exact subpower_capped_marginal_residual_small_of_kubilius hK
      delta hdeltaRange c C hc (lt_of_le_of_ne hC (Ne.symm hC0)) hdelta

end NormalNumbers.ErdosBorweinSubpowerKub
