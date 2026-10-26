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

lemma one_lt_subpowerKubiliusModelCoefficient {c : ℝ} (hc : 1 < c) :
    1 < subpowerKubiliusModelCoefficient c :=
  one_lt_kubiliusBlockRatio hc

lemma subpowerKubiliusModelCoefficient_lt {c : ℝ} (hc : 1 < c) :
    subpowerKubiliusModelCoefficient c < c :=
  kubiliusBlockRatio_lt hc

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
