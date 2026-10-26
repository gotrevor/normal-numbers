/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinEndpointKubAux

/-!
# Exponential tilting for finite Bernoulli subset laws

This file supplies the exact finite change-of-measure layer needed by the moderate-deviation
argument in `CoefmassErdosBorweinMultiShift.lean`.  Analytic estimates on the tilted mean,
variance, and normalizer are deliberately separate from these identities.
-/

namespace NormalNumbers.ErdosBorweinMultiShift

open scoped BigOperators
open NormalNumbers.ErdosBorweinEndpointKub

/-- The Bernoulli parameter obtained from `q` by exponential tilting through `theta`. -/
noncomputable def bernoulliTiltParameter {alpha : Type*} (q : alpha -> Real) (theta : Real)
    (p : alpha) : Real :=
  q p * Real.exp theta / (1 - q p + q p * Real.exp theta)

/-- The product normalizer for exponential tilting of a finite Bernoulli subset law. -/
noncomputable def bernoulliTiltNormalizer {alpha : Type*} (U : Finset alpha)
    (q : alpha -> Real) (theta : Real) : Real :=
  ∏ p ∈ U, (1 - q p + q p * Real.exp theta)

theorem bernoulliTiltDenominator_pos {alpha : Type*} {q : alpha -> Real} {p : alpha}
    (theta : Real) (hq0 : 0 <= q p) (hq1 : q p <= 1) :
    0 < 1 - q p + q p * Real.exp theta := by
  by_cases hq : q p = 1
  · simp [hq, Real.exp_pos]
  · have hlt : q p < 1 := lt_of_le_of_ne hq1 hq
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hlt)
      (mul_nonneg hq0 (Real.exp_pos theta).le)

theorem bernoulliTiltParameter_nonneg {alpha : Type*} {q : alpha -> Real} {p : alpha}
    (theta : Real) (hq0 : 0 <= q p) (hq1 : q p <= 1) :
    0 <= bernoulliTiltParameter q theta p := by
  exact div_nonneg (mul_nonneg hq0 (Real.exp_pos theta).le)
    (bernoulliTiltDenominator_pos theta hq0 hq1).le

theorem bernoulliTiltParameter_le_one {alpha : Type*} {q : alpha -> Real} {p : alpha}
    (theta : Real) (hq0 : 0 <= q p) (hq1 : q p <= 1) :
    bernoulliTiltParameter q theta p <= 1 := by
  apply (div_le_one (bernoulliTiltDenominator_pos theta hq0 hq1)).2
  linarith

/-- The tilt denominator interpolates between `1` and `exp theta` for a nonnegative tilt. -/
theorem bernoulliTiltDenominator_bounds {alpha : Type*} {q : alpha -> Real} {p : alpha}
    {theta : Real} (hq0 : 0 <= q p) (hq1 : q p <= 1) (htheta : 0 <= theta) :
    1 <= 1 - q p + q p * Real.exp theta ∧
      1 - q p + q p * Real.exp theta <= Real.exp theta := by
  have he : 1 <= Real.exp theta := Real.one_le_exp htheta
  have ht : 0 <= Real.exp theta - 1 := sub_nonneg.mpr he
  have hlow : 0 <= q p * (Real.exp theta - 1) := mul_nonneg hq0 ht
  have hupp : q p * (Real.exp theta - 1) <= Real.exp theta - 1 :=
    mul_le_of_le_one_left ht hq1
  constructor <;> nlinarith

/-- Exact displacement of one Bernoulli parameter under exponential tilting. -/
theorem bernoulliTiltParameter_sub {alpha : Type*} {q : alpha -> Real} {p : alpha}
    (theta : Real) (hq0 : 0 <= q p) (hq1 : q p <= 1) :
    bernoulliTiltParameter q theta p - q p =
      q p * (1 - q p) * (Real.exp theta - 1) /
        (1 - q p + q p * Real.exp theta) := by
  have hd := bernoulliTiltDenominator_pos theta hq0 hq1
  unfold bernoulliTiltParameter
  field_simp
  ring

/-- Exact variance of one tilted Bernoulli coordinate in terms of the original parameter. -/
theorem bernoulliTiltParameter_variance {alpha : Type*} {q : alpha -> Real} {p : alpha}
    (theta : Real) (hq0 : 0 <= q p) (hq1 : q p <= 1) :
    bernoulliTiltParameter q theta p * (1 - bernoulliTiltParameter q theta p) =
      q p * (1 - q p) * Real.exp theta /
        (1 - q p + q p * Real.exp theta) ^ 2 := by
  have hd := bernoulliTiltDenominator_pos theta hq0 hq1
  unfold bernoulliTiltParameter
  field_simp
  ring

/-- A nonnegative tilt increases each parameter by its original variance times a factor between
`1 - exp (-theta)` and `exp theta - 1`. -/
theorem bernoulliTiltParameter_sub_bounds {alpha : Type*} {q : alpha -> Real} {p : alpha}
    {theta : Real} (hq0 : 0 <= q p) (hq1 : q p <= 1) (htheta : 0 <= theta) :
    q p * (1 - q p) * (1 - Real.exp (-theta)) <=
        bernoulliTiltParameter q theta p - q p ∧
      bernoulliTiltParameter q theta p - q p <=
        q p * (1 - q p) * (Real.exp theta - 1) := by
  have hd := bernoulliTiltDenominator_pos theta hq0 hq1
  have hdb := bernoulliTiltDenominator_bounds hq0 hq1 htheta
  have hvar : 0 <= q p * (1 - q p) := mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hexpm : 0 <= Real.exp theta - 1 := sub_nonneg.mpr (Real.one_le_exp htheta)
  let numerator := q p * (1 - q p) * (Real.exp theta - 1)
  have hnum : 0 <= numerator := mul_nonneg hvar hexpm
  rw [bernoulliTiltParameter_sub theta hq0 hq1]
  constructor
  · have hdiv : numerator / Real.exp theta <=
        numerator / (1 - q p + q p * Real.exp theta) :=
      div_le_div_of_nonneg_left hnum hd hdb.2
    calc
      q p * (1 - q p) * (1 - Real.exp (-theta)) =
          numerator / Real.exp theta := by
        dsimp [numerator]
        rw [Real.exp_neg]
        field_simp
      _ <= _ := hdiv
  · exact (div_le_iff₀ hd).2 (by
      change numerator <= numerator * (1 - q p + q p * Real.exp theta)
      nlinarith)

/-- The elementary lower Taylor bound used to control each factor of the tilt normalizer. -/
theorem sub_sq_le_log_one_add {s : Real} (hs : 0 <= s) :
    s - s ^ 2 <= Real.log (1 + s) := by
  have hpos : 0 < 1 + s := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 : Real) / (1 + s) by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hpos), Real.log_one, zero_sub] at h
  have hrw : (1 : Real) / (1 + s) - 1 = -(s / (1 + s)) := by
    field_simp
    ring
  rw [hrw] at h
  have hfrac : s / (1 + s) <= Real.log (1 + s) := by linarith
  have htaylor : s - s ^ 2 <= s / (1 + s) := by
    rw [le_div_iff₀ hpos]
    nlinarith [pow_nonneg hs 3]
  exact htaylor.trans hfrac

/-- On the unit interval, the loss in `1 - exp (-theta)` is at most quadratic. -/
theorem sub_sq_le_one_sub_exp_neg {theta : Real} (htheta0 : 0 <= theta)
    (htheta1 : theta <= 1) :
    theta - theta ^ 2 <= 1 - Real.exp (-theta) := by
  have habs : |(-theta : Real)| <= 1 := by
    rw [abs_neg, abs_of_nonneg htheta0]
    exact htheta1
  have hrem := Real.abs_exp_sub_one_sub_id_le habs
  have hupper : Real.exp (-theta) - 1 - (-theta) <= theta ^ 2 := by
    calc
      Real.exp (-theta) - 1 - (-theta) <=
          |Real.exp (-theta) - 1 - (-theta)| := le_abs_self _
      _ <= (-theta) ^ 2 := hrem
      _ = theta ^ 2 := by ring
  linarith

/-- On the unit interval, `exp theta - 1` is at most its linear term plus a quadratic error. -/
theorem exp_sub_one_le_add_sq {theta : Real} (htheta0 : 0 <= theta)
    (htheta1 : theta <= 1) :
    Real.exp theta - 1 <= theta + theta ^ 2 := by
  have habs : |theta| <= 1 := by rw [abs_of_nonneg htheta0]; exact htheta1
  have hrem := Real.abs_exp_sub_one_sub_id_le habs
  have hupper := le_trans (le_abs_self (Real.exp theta - 1 - theta)) hrem
  linarith

/-- Summing the coordinatewise displacement bounds locates the tilted mean between two explicit
multiples of the original Bernoulli variance. -/
theorem bernoulliTiltMean_sub_bounds {alpha : Type*} (U : Finset alpha) (q : alpha -> Real)
    {theta : Real} (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (htheta : 0 <= theta) :
    (∑ p ∈ U, q p * (1 - q p)) * (1 - Real.exp (-theta)) <=
        (∑ p ∈ U, bernoulliTiltParameter q theta p) - ∑ p ∈ U, q p ∧
      (∑ p ∈ U, bernoulliTiltParameter q theta p) - ∑ p ∈ U, q p <=
        (∑ p ∈ U, q p * (1 - q p)) * (Real.exp theta - 1) := by
  rw [← Finset.sum_sub_distrib]
  constructor
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun p hp =>
      (bernoulliTiltParameter_sub_bounds (hq0 p hp) (hq1 p hp) htheta).1
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun p hp =>
      (bernoulliTiltParameter_sub_bounds (hq0 p hp) (hq1 p hp) htheta).2

/-- The original Bernoulli variance is its mean minus the square-mass correction. -/
theorem sum_bernoulliVariance_eq_sub_squareMass {alpha : Type*} (U : Finset alpha)
    (q : alpha -> Real) :
    (∑ p ∈ U, q p * (1 - q p)) =
      (∑ p ∈ U, q p) - ∑ p ∈ U, (q p) ^ 2 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- A nonnegative exponential tilt increases the total Bernoulli variance by at most the factor
`exp theta`. -/
theorem bernoulliTiltVariance_le {alpha : Type*} (U : Finset alpha) (q : alpha -> Real)
    {theta : Real} (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (htheta : 0 <= theta) :
    ∑ p ∈ U, bernoulliTiltParameter q theta p * (1 - bernoulliTiltParameter q theta p) <=
      Real.exp theta * ∑ p ∈ U, q p * (1 - q p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [bernoulliTiltParameter_variance theta (hq0 p hp) (hq1 p hp)]
  have hn : 0 <= q p * (1 - q p) * Real.exp theta :=
    mul_nonneg (mul_nonneg (hq0 p hp) (sub_nonneg.mpr (hq1 p hp))) (Real.exp_pos theta).le
  have hd := (bernoulliTiltDenominator_bounds (hq0 p hp) (hq1 p hp) htheta).1
  have hdiv : q p * (1 - q p) * Real.exp theta /
      (1 - q p + q p * Real.exp theta) ^ 2 <= q p * (1 - q p) * Real.exp theta :=
    div_le_self hn (one_le_pow₀ hd)
  calc
    q p * (1 - q p) * Real.exp theta /
        (1 - q p + q p * Real.exp theta) ^ 2 <=
      q p * (1 - q p) * Real.exp theta := hdiv
    _ = Real.exp theta * (q p * (1 - q p)) := by ring

/-- Product-level lower Taylor bound for the tilt normalizer.  The quadratic correction is kept as
`sum q²`; for prime parameters this is bounded independently of the growing mean. -/
theorem bernoulliTiltNormalizer_lower {alpha : Type*} (U : Finset alpha) (q : alpha -> Real)
    {theta : Real} (hq0 : ∀ p ∈ U, 0 <= q p) (htheta : 0 <= theta) :
    Real.exp ((Real.exp theta - 1) * (∑ p ∈ U, q p) -
        (Real.exp theta - 1) ^ 2 * ∑ p ∈ U, (q p) ^ 2) <=
      bernoulliTiltNormalizer U q theta := by
  let a := Real.exp theta - 1
  have ha : 0 <= a := sub_nonneg.mpr (Real.one_le_exp htheta)
  have hfactor : ∀ p ∈ U,
      Real.exp (q p * a - (q p * a) ^ 2) <= 1 - q p + q p * Real.exp theta := by
    intro p hp
    have hs : 0 <= q p * a := mul_nonneg (hq0 p hp) ha
    have hlog := sub_sq_le_log_one_add hs
    have hpos : 0 < 1 + q p * a := by positivity
    calc
      Real.exp (q p * a - (q p * a) ^ 2) <= Real.exp (Real.log (1 + q p * a)) :=
        Real.exp_le_exp.mpr hlog
      _ = 1 + q p * a := Real.exp_log hpos
      _ = 1 - q p + q p * Real.exp theta := by dsimp [a]; ring
  calc
    Real.exp ((Real.exp theta - 1) * (∑ p ∈ U, q p) -
        (Real.exp theta - 1) ^ 2 * ∑ p ∈ U, (q p) ^ 2) =
        Real.exp (∑ p ∈ U, (q p * a - (q p * a) ^ 2)) := by
      congr 1
      dsimp [a]
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∏ p ∈ U, Real.exp (q p * a - (q p * a) ^ 2) := Real.exp_sum _ _
    _ <= ∏ p ∈ U, (1 - q p + q p * Real.exp theta) := by
      exact Finset.prod_le_prod (fun p hp => (Real.exp_pos _).le) hfactor
    _ = bernoulliTiltNormalizer U q theta := rfl

open Classical in
/-- Exact Radon--Nikodym identity between an original finite Bernoulli law and its exponential
tilt. -/
theorem bernoulliSubsetWeight_eq_tilted {alpha : Type*} [DecidableEq alpha]
    (U S : Finset alpha) (q : alpha -> Real) (theta : Real) (hS : S ⊆ U)
    (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1) :
    bernoulliSubsetWeight U S q =
      bernoulliTiltNormalizer U q theta * Real.exp (-(theta * S.card)) *
        bernoulliSubsetWeight U S (bernoulliTiltParameter q theta) := by
  have hlocal : ∀ p ∈ U,
      (if p ∈ S then q p else 1 - q p) =
        (1 - q p + q p * Real.exp theta) *
          (if p ∈ S then Real.exp (-theta) else 1) *
            (if p ∈ S then bernoulliTiltParameter q theta p
              else 1 - bernoulliTiltParameter q theta p) := by
    intro p hp
    have hd := bernoulliTiltDenominator_pos theta (hq0 p hp) (hq1 p hp)
    by_cases hpS : p ∈ S
    · simp only [hpS, if_true, bernoulliTiltParameter]
      field_simp
      rw [Real.exp_neg]
      field_simp
    · simp only [hpS, if_false, bernoulliTiltParameter]
      field_simp
      ring
  have hselected :
      (∏ p ∈ U, if p ∈ S then Real.exp (-theta) else 1) =
        Real.exp (-(theta * S.card)) := by
    rw [Finset.prod_ite]
    have hfilter : U.filter (fun p => p ∈ S) = S := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · exact fun hp => hp.2
      · exact fun hp => ⟨hS hp, hp⟩
    rw [hfilter]
    simp only [Finset.prod_const, one_pow, mul_one]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold bernoulliSubsetWeight bernoulliTiltNormalizer
  calc
    (∏ p ∈ U, if p ∈ S then q p else 1 - q p) =
        ∏ p ∈ U, ((1 - q p + q p * Real.exp theta) *
          (if p ∈ S then Real.exp (-theta) else 1) *
            (if p ∈ S then bernoulliTiltParameter q theta p
              else 1 - bernoulliTiltParameter q theta p)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hlocal p hp
    _ = (∏ p ∈ U, (1 - q p + q p * Real.exp theta)) *
          (∏ p ∈ U, if p ∈ S then Real.exp (-theta) else 1) *
            ∏ p ∈ U, (if p ∈ S then bernoulliTiltParameter q theta p
              else 1 - bernoulliTiltParameter q theta p) := by
      simp only [Finset.prod_mul_distrib]
    _ = _ := by rw [hselected]

open Classical in
/-- The moment generating function of the selected-cardinality statistic is the tilt
normalizer. -/
theorem bernoulliSubsetExpectation_exp_card {alpha : Type*} [DecidableEq alpha]
    (U : Finset alpha) (q : alpha -> Real) (theta : Real) :
    bernoulliSubsetExpectation U q (fun S => Real.exp (theta * S.card)) =
      bernoulliTiltNormalizer U q theta := by
  rw [bernoulliSubsetExpectation]
  calc
    (∑ S ∈ U.powerset, bernoulliSubsetWeight U S q * Real.exp (theta * S.card)) =
        ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q *
          ∏ p ∈ U, (if p ∈ S then Real.exp theta else 1) := by
      apply Finset.sum_congr rfl
      intro S hS
      congr 1
      rw [Finset.prod_ite]
      have hsub := Finset.mem_powerset.mp hS
      have hfilter : U.filter (fun p => p ∈ S) = S := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · exact fun hp => hp.2
        · exact fun hp => ⟨hsub hp, hp⟩
      rw [hfilter]
      simp only [Finset.prod_const, one_pow, mul_one]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = ∏ p ∈ U, (q p * Real.exp theta + (1 - q p) * 1) :=
      bernoulliSubset_expectation_prod U q (fun _ => Real.exp theta) (fun _ => 1)
    _ = bernoulliTiltNormalizer U q theta := by
      unfold bernoulliTiltNormalizer
      apply Finset.prod_congr rfl
      intro p hp
      ring

open Classical in
/-- Quantitative lower transfer from a centered window under the tilted law to the corresponding
cardinality window under the original law.  This is the exact change-of-measure half of the
tilted-Chebyshev moderate-deviation argument. -/
theorem bernoulliSubsetMass_tiltedWindow_lower {alpha : Type*} [DecidableEq alpha]
    (U : Finset alpha) (q : alpha -> Real) {theta radius : Real}
    (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (htheta : 0 <= theta) (hradius : 0 < radius) :
    let qt := bernoulliTiltParameter q theta
    let mean := ∑ p ∈ U, qt p
    let variance := ∑ p ∈ U, qt p * (1 - qt p)
    bernoulliTiltNormalizer U q theta * Real.exp (-theta * (mean + radius)) *
        (1 - variance / radius ^ 2) <=
      bernoulliSubsetMass U q
        {S | mean - radius < (S.card : Real) ∧ (S.card : Real) < mean + radius} := by
  dsimp only
  let qt := bernoulliTiltParameter q theta
  let mean : Real := ∑ p ∈ U, qt p
  let variance : Real := ∑ p ∈ U, qt p * (1 - qt p)
  have hqt0 : ∀ p ∈ U, 0 <= qt p := fun p hp =>
    bernoulliTiltParameter_nonneg theta (hq0 p hp) (hq1 p hp)
  have hqt1 : ∀ p ∈ U, qt p <= 1 := fun p hp =>
    bernoulliTiltParameter_le_one theta (hq0 p hp) (hq1 p hp)
  let A : Set (Finset alpha) :=
    {S | mean - radius < (S.card : Real) ∧ (S.card : Real) < mean + radius}
  have htiltedLower : 1 - variance / radius ^ 2 <= bernoulliSubsetMass U qt A := by
    have htail := bernoulliSubsetMass_centeredSum_abs_ge_le U qt hqt0 hqt1 hradius
    have hcenter : ∀ S ∈ U.powerset,
        bernoulliCenteredSum U qt S = (S.card : Real) - mean := by
      intro S hS
      rw [bernoulliCenteredSum_eq_card_inter_sub_sum]
      have hinter : S ∩ U = S := Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hS)
      rw [hinter]
    have hcomplMass : bernoulliSubsetMass U qt Aᶜ =
        bernoulliSubsetMass U qt
          {S | radius <= |bernoulliCenteredSum U qt S|} := by
      unfold bernoulliSubsetMass
      apply Finset.sum_congr rfl
      intro S hS
      have hc := hcenter S hS
      have hevent : S ∈ Aᶜ ↔ radius <= |bernoulliCenteredSum U qt S| := by
        simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq]
        rw [hc]
        constructor
        · intro h
          rw [le_abs]
          by_cases hlower : mean - radius < (S.card : Real)
          · left
            have hupper : mean + radius <= (S.card : Real) := by
              by_contra hnot
              exact h ⟨hlower, lt_of_not_ge hnot⟩
            linarith
          · right
            have hlower' : (S.card : Real) <= mean - radius := le_of_not_gt hlower
            linarith
        · intro h
          rw [le_abs] at h
          intro hA
          rcases h with h | h <;> linarith [hA.1, hA.2]
      by_cases hA : S ∈ Aᶜ
      · have ht : S ∈ {S | radius <= |bernoulliCenteredSum U qt S|} := hevent.mp hA
        rw [if_pos hA, if_pos ht]
      · have ht : S ∉ {S | radius <= |bernoulliCenteredSum U qt S|} :=
          fun ht => hA (hevent.mpr ht)
        rw [if_neg hA, if_neg ht]
    calc
      1 - variance / radius ^ 2 <=
          1 - bernoulliSubsetMass U qt
            {S | radius <= |bernoulliCenteredSum U qt S|} := by
        change bernoulliSubsetMass U qt
          {S | radius <= |bernoulliCenteredSum U qt S|} <=
            variance / radius ^ 2 at htail
        linarith
      _ = 1 - bernoulliSubsetMass U qt Aᶜ := by rw [hcomplMass]
      _ = bernoulliSubsetMass U qt A := by
        rw [bernoulliSubsetMass_compl]
        ring
  calc
    bernoulliTiltNormalizer U q theta * Real.exp (-theta * (mean + radius)) *
          (1 - variance / radius ^ 2) <=
        bernoulliTiltNormalizer U q theta * Real.exp (-theta * (mean + radius)) *
          bernoulliSubsetMass U qt A := by
      gcongr
      exact mul_nonneg
        (Finset.prod_nonneg fun p hp =>
          (bernoulliTiltDenominator_pos theta (hq0 p hp) (hq1 p hp)).le)
        (Real.exp_pos _).le
    _ = ∑ S ∈ U.powerset,
          bernoulliTiltNormalizer U q theta * Real.exp (-theta * (mean + radius)) *
            (if S ∈ A then bernoulliSubsetWeight U S qt else 0) := by
      unfold bernoulliSubsetMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hSA : S ∈ A <;> simp [hSA]
    _ <= ∑ S ∈ U.powerset,
          if S ∈ A then bernoulliSubsetWeight U S q else 0 := by
      apply Finset.sum_le_sum
      intro S hS
      by_cases hSA : S ∈ A
      · simp only [hSA, if_true]
        rw [bernoulliSubsetWeight_eq_tilted U S q theta
          (Finset.mem_powerset.mp hS) hq0 hq1]
        have hcard : (S.card : Real) < mean + radius := hSA.2
        have hexp : Real.exp (-theta * (mean + radius)) <=
            Real.exp (-(theta * S.card)) := by
          apply Real.exp_le_exp.2
          nlinarith
        have hnorm : 0 <= bernoulliTiltNormalizer U q theta :=
          Finset.prod_nonneg fun p hp =>
            (bernoulliTiltDenominator_pos theta (hq0 p hp) (hq1 p hp)).le
        have hweight : 0 <= bernoulliSubsetWeight U S qt :=
          bernoulliSubsetWeight_nonneg U S qt hqt0 hqt1
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp hnorm) hweight
      · simp [hSA]
    _ = bernoulliSubsetMass U q A := by
      unfold bernoulliSubsetMass
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hSA : S ∈ A <;> simp [hSA]

open Classical in
/-- A one-sided finite moderate-deviation bound with all analytic losses exposed.  Once the tilted
mean lies at least `radius` above the requested threshold and `radius²` dominates the elementary
upper bound for the tilted variance, the upper-tail cost is the quadratic normalizer correction
plus the exact exponential change-of-measure cost. -/
theorem bernoulliSubsetMass_card_ge_tilt_lower {alpha : Type*} [DecidableEq alpha]
    (U : Finset alpha) (q : alpha -> Real) {theta radius x : Real}
    (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (htheta : 0 <= theta) (hradius : 0 < radius)
    (hlocate : (∑ p ∈ U, q p) + x <=
      (∑ p ∈ U, bernoulliTiltParameter q theta p) - radius)
    (hvariance : Real.exp theta * (∑ p ∈ U, q p * (1 - q p)) <= radius ^ 2) :
    Real.exp ((Real.exp theta - 1) * (∑ p ∈ U, q p) -
        (Real.exp theta - 1) ^ 2 * (∑ p ∈ U, (q p) ^ 2) -
        theta * ((∑ p ∈ U, bernoulliTiltParameter q theta p) + radius)) *
        (1 - Real.exp theta * (∑ p ∈ U, q p * (1 - q p)) / radius ^ 2) <=
      bernoulliSubsetMass U q {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := by
  let qt := bernoulliTiltParameter q theta
  let mean : Real := ∑ p ∈ U, qt p
  let variance : Real := ∑ p ∈ U, qt p * (1 - qt p)
  let originalVariance : Real := ∑ p ∈ U, q p * (1 - q p)
  let squareMass : Real := ∑ p ∈ U, (q p) ^ 2
  let normalizerLower : Real :=
    Real.exp ((Real.exp theta - 1) * (∑ p ∈ U, q p) -
      (Real.exp theta - 1) ^ 2 * squareMass)
  let windowFactor : Real := 1 - variance / radius ^ 2
  let lowerFactor : Real := 1 - Real.exp theta * originalVariance / radius ^ 2
  have hradiusSq : 0 < radius ^ 2 := sq_pos_of_pos hradius
  have hvar := bernoulliTiltVariance_le U q hq0 hq1 htheta
  have hfactor : lowerFactor <= windowFactor := by
    dsimp [lowerFactor, windowFactor, variance, originalVariance]
    have hdiv : variance / radius ^ 2 <= Real.exp theta * originalVariance / radius ^ 2 :=
      div_le_div_of_nonneg_right hvar hradiusSq.le
    linarith
  have hlowerFactor : 0 <= lowerFactor := by
    dsimp [lowerFactor, originalVariance]
    rw [sub_nonneg, div_le_one hradiusSq]
    exact hvariance
  have hnormalizer : normalizerLower <= bernoulliTiltNormalizer U q theta := by
    dsimp [normalizerLower, squareMass]
    exact bernoulliTiltNormalizer_lower U q hq0 htheta
  have hnormalizerNonneg : 0 <= bernoulliTiltNormalizer U q theta :=
    Finset.prod_nonneg fun p hp =>
      (bernoulliTiltDenominator_pos theta (hq0 p hp) (hq1 p hp)).le
  have hwindow := bernoulliSubsetMass_tiltedWindow_lower U q hq0 hq1 htheta hradius
  have hmono : bernoulliSubsetMass U q
      {S | mean - radius < (S.card : Real) ∧ (S.card : Real) < mean + radius} <=
      bernoulliSubsetMass U q {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := by
    apply bernoulliSubsetMass_mono U q _ hq0 hq1
    intro S hS
    exact le_trans hlocate (le_of_lt hS.1)
  calc
    Real.exp ((Real.exp theta - 1) * (∑ p ∈ U, q p) -
        (Real.exp theta - 1) ^ 2 * (∑ p ∈ U, (q p) ^ 2) -
        theta * ((∑ p ∈ U, bernoulliTiltParameter q theta p) + radius)) *
        (1 - Real.exp theta * (∑ p ∈ U, q p * (1 - q p)) / radius ^ 2) =
      normalizerLower * Real.exp (-theta * (mean + radius)) * lowerFactor := by
        dsimp [normalizerLower, mean, squareMass, lowerFactor, originalVariance, qt]
        rw [← Real.exp_add]
        congr 2
        ring
    _ <= bernoulliTiltNormalizer U q theta * Real.exp (-theta * (mean + radius)) *
        lowerFactor := by
      gcongr
    _ <= bernoulliTiltNormalizer U q theta * Real.exp (-theta * (mean + radius)) *
        windowFactor := by
      gcongr
    _ <= bernoulliSubsetMass U q
        {S | mean - radius < (S.card : Real) ∧ (S.card : Real) < mean + radius} := by
      dsimp [windowFactor, variance, mean, qt]
      exact hwindow
    _ <= bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := hmono

open Classical in
/-- A finite near-Gaussian moderate-deviation lower bound.  The hypotheses separate the two
parameter-selection obligations: the tilted mean must clear the threshold using the quadratic
lower bound for `1 - exp (-theta)`, and twice the elementary tilted-variance bound must fit inside
the chosen window.  The conclusion has leading cost `mean * theta^2 / 2`; all remaining losses are
explicitly lower order when `theta -> 0`, `squareMass = o(mean)`, and `radius = o(mean * theta)`. -/
theorem bernoulliSubsetMass_card_ge_quadratic_lower {alpha : Type*} [DecidableEq alpha]
    (U : Finset alpha) (q : alpha -> Real) {theta radius x : Real}
    (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (htheta0 : 0 <= theta) (htheta1 : theta <= 1) (hradius : 0 < radius)
    (hlocate : x + radius <=
      (∑ p ∈ U, q p * (1 - q p)) * (theta - theta ^ 2))
    (hvariance : 2 * Real.exp theta * (∑ p ∈ U, q p * (1 - q p)) <= radius ^ 2) :
    (1 / 2 : Real) * Real.exp (-(((∑ p ∈ U, q p) / 2 +
        4 * ∑ p ∈ U, (q p) ^ 2) * theta ^ 2 +
        (∑ p ∈ U, q p) * theta ^ 3 + theta * radius)) <=
      bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := by
  let mean : Real := ∑ p ∈ U, q p
  let variance : Real := ∑ p ∈ U, q p * (1 - q p)
  let squareMass : Real := ∑ p ∈ U, (q p) ^ 2
  let tiltedMean : Real := ∑ p ∈ U, bernoulliTiltParameter q theta p
  let a : Real := Real.exp theta - 1
  let loss : Real :=
    (mean / 2 + 4 * squareMass) * theta ^ 2 + mean * theta ^ 3 + theta * radius
  have hmean0 : 0 <= mean := by
    dsimp [mean]
    exact Finset.sum_nonneg fun p hp => hq0 p hp
  have hvariance0 : 0 <= variance := by
    dsimp [variance]
    exact Finset.sum_nonneg fun p hp => mul_nonneg (hq0 p hp) (sub_nonneg.mpr (hq1 p hp))
  have hsquareMass0 : 0 <= squareMass := by
    dsimp [squareMass]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hvarianceMean : variance <= mean := by
    dsimp [variance, mean]
    apply Finset.sum_le_sum
    intro p hp
    nlinarith [sq_nonneg (q p)]
  have hmeanBounds := bernoulliTiltMean_sub_bounds U q hq0 hq1 htheta0
  have hsubExp := sub_sq_le_one_sub_exp_neg htheta0 htheta1
  have hlocate' : mean + x <= tiltedMean - radius := by
    have hmul : variance * (theta - theta ^ 2) <=
        variance * (1 - Real.exp (-theta)) :=
      mul_le_mul_of_nonneg_left hsubExp hvariance0
    dsimp [mean, variance, tiltedMean] at hmul ⊢
    nlinarith [hlocate, hmeanBounds.1]
  have hvariance' : Real.exp theta * variance <= radius ^ 2 := by
    dsimp [variance] at hvariance ⊢
    nlinarith [mul_nonneg (Real.exp_pos theta).le
      (Finset.sum_nonneg fun p hp => mul_nonneg (hq0 p hp) (sub_nonneg.mpr (hq1 p hp)))]
  have hbase := bernoulliSubsetMass_card_ge_tilt_lower U q hq0 hq1 htheta0 hradius
    hlocate' hvariance'
  have ha0 : 0 <= a := by
    dsimp [a]
    exact sub_nonneg.mpr (Real.one_le_exp htheta0)
  have haLower : theta + theta ^ 2 / 2 <= a := by
    dsimp [a]
    nlinarith [Real.quadratic_le_exp_of_nonneg htheta0]
  have haUpper : a <= theta + theta ^ 2 := by
    dsimp [a]
    exact exp_sub_one_le_add_sq htheta0 htheta1
  have hthetaSq : theta ^ 2 <= theta := by nlinarith [mul_nonneg htheta0 (sub_nonneg.mpr htheta1)]
  have haTwoTheta : a <= 2 * theta := by nlinarith
  have haSq : a ^ 2 <= 4 * theta ^ 2 := by nlinarith [sq_nonneg (a - 2 * theta)]
  have hthetaCube0 : 0 <= theta ^ 3 := by positivity
  have hmeanA : mean * (theta + theta ^ 2 / 2) <= mean * a :=
    mul_le_mul_of_nonneg_left haLower hmean0
  have hsquareA : a ^ 2 * squareMass <= 4 * theta ^ 2 * squareMass :=
    mul_le_mul_of_nonneg_right haSq hsquareMass0
  have hthetaA : theta * a <= theta ^ 2 + theta ^ 3 := by
    calc
      theta * a <= theta * (theta + theta ^ 2) :=
        mul_le_mul_of_nonneg_left haUpper htheta0
      _ = theta ^ 2 + theta ^ 3 := by ring
  have hvarianceThetaA : variance * (theta * a) <=
      variance * (theta ^ 2 + theta ^ 3) :=
    mul_le_mul_of_nonneg_left hthetaA hvariance0
  have hvarianceThetaSq : variance * theta ^ 2 <= mean * theta ^ 2 :=
    mul_le_mul_of_nonneg_right hvarianceMean (sq_nonneg theta)
  have hvarianceThetaCube : variance * theta ^ 3 <= mean * theta ^ 3 :=
    mul_le_mul_of_nonneg_right hvarianceMean hthetaCube0
  have htiltedMeanUpper : tiltedMean <= mean + variance * a := by
    dsimp [tiltedMean, mean, variance, a]
    linarith [hmeanBounds.2]
  have hthetaMean : theta * (tiltedMean + radius) <=
      theta * (mean + variance * a + radius) :=
    mul_le_mul_of_nonneg_left (by linarith [htiltedMeanUpper]) htheta0
  have hexponent : -loss <=
      a * mean - a ^ 2 * squareMass - theta * (tiltedMean + radius) := by
    dsimp [loss]
    nlinarith [hmeanA, hsquareA, hvarianceThetaA, hvarianceThetaSq,
      hvarianceThetaCube, hthetaMean]
  have hradiusSq : 0 < radius ^ 2 := sq_pos_of_pos hradius
  have hratio : Real.exp theta * variance / radius ^ 2 <= (1 / 2 : Real) := by
    rw [div_le_iff₀ hradiusSq]
    dsimp [variance] at hvariance ⊢
    nlinarith
  have hfactor : (1 / 2 : Real) <=
      1 - Real.exp theta * variance / radius ^ 2 := by linarith
  calc
    (1 / 2 : Real) * Real.exp (-(((∑ p ∈ U, q p) / 2 +
        4 * ∑ p ∈ U, (q p) ^ 2) * theta ^ 2 +
        (∑ p ∈ U, q p) * theta ^ 3 + theta * radius)) =
        (1 / 2 : Real) * Real.exp (-loss) := by rfl
    _ <= (1 / 2 : Real) *
        Real.exp (a * mean - a ^ 2 * squareMass - theta * (tiltedMean + radius)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ <= (1 - Real.exp theta * variance / radius ^ 2) *
        Real.exp (a * mean - a ^ 2 * squareMass - theta * (tiltedMean + radius)) := by
      exact mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
    _ = Real.exp ((Real.exp theta - 1) * (∑ p ∈ U, q p) -
          (Real.exp theta - 1) ^ 2 * (∑ p ∈ U, (q p) ^ 2) -
          theta * ((∑ p ∈ U, bernoulliTiltParameter q theta p) + radius)) *
        (1 - Real.exp theta * (∑ p ∈ U, q p * (1 - q p)) / radius ^ 2) := by
      dsimp [a, mean, variance, squareMass, tiltedMean]
      ring
    _ <= bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := hbase

open Classical in
/-- Explicit parameter choice for the finite moderate-deviation bound.  If the square-mass is at
most `eta` times the mean, the deviation is small enough that
`theta = (1 + 4 eta) x / mean <= eta`, and `x` is large enough compared with `sqrt mean`, then a
window of radius `eta * x` gives a lower bound whose exponential constant is within `20 eta` of
the Gaussian constant `1/2`. -/
theorem bernoulliSubsetMass_card_ge_explicit_moderate_lower
    {alpha : Type*} [DecidableEq alpha] (U : Finset alpha) (q : alpha -> Real)
    {eta x : Real} (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (heta0 : 0 < eta) (heta1 : eta <= 1 / 100)
    (hmean : 0 < ∑ p ∈ U, q p) (hx : 0 < x)
    (hsquareMass : (∑ p ∈ U, (q p) ^ 2) <= eta * ∑ p ∈ U, q p)
    (hsmallTilt : (1 + 4 * eta) * x / (∑ p ∈ U, q p) <= eta)
    (hlargeDeviation : 6 * (∑ p ∈ U, q p) <= eta ^ 2 * x ^ 2) :
    (1 / 2 : Real) * Real.exp (-((1 / 2 + 20 * eta) * x ^ 2 /
        (∑ p ∈ U, q p))) <=
      bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := by
  let mean : Real := ∑ p ∈ U, q p
  let variance : Real := ∑ p ∈ U, q p * (1 - q p)
  let squareMass : Real := ∑ p ∈ U, (q p) ^ 2
  let theta : Real := (1 + 4 * eta) * x / mean
  let radius : Real := eta * x
  let exactLoss : Real :=
    (mean / 2 + 4 * squareMass) * theta ^ 2 + mean * theta ^ 3 + theta * radius
  have heta0' : 0 <= eta := heta0.le
  have hetaLeOne : eta <= 1 := heta1.trans (by norm_num)
  have htheta0 : 0 <= theta := by
    dsimp [theta]
    positivity
  have hthetaEta : theta <= eta := by
    simpa only [theta, mean] using hsmallTilt
  have htheta1 : theta <= 1 := hthetaEta.trans hetaLeOne
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hmeanPos : 0 < mean := by simpa only [mean] using hmean
  have hmean0 : 0 <= mean := hmeanPos.le
  have hvariance0 : 0 <= variance := by
    dsimp [variance]
    exact Finset.sum_nonneg fun p hp => mul_nonneg (hq0 p hp) (sub_nonneg.mpr (hq1 p hp))
  have hvarianceMean : variance <= mean := by
    dsimp [variance, mean]
    apply Finset.sum_le_sum
    intro p hp
    nlinarith [sq_nonneg (q p)]
  have hvarianceEq : variance = mean - squareMass := by
    simpa only [variance, mean, squareMass] using sum_bernoulliVariance_eq_sub_squareMass U q
  have hsquareMass' : squareMass <= eta * mean := by
    simpa only [squareMass, mean] using hsquareMass
  have hvarianceLower : (1 - eta) * mean <= variance := by
    rw [hvarianceEq]
    linarith
  have honeSubEta0 : 0 <= 1 - eta := sub_nonneg.mpr hetaLeOne
  have hthetaOneSubEta0 : 0 <= theta * (1 - eta) := mul_nonneg htheta0 honeSubEta0
  have hthetaLoss : theta * (1 - eta) <= theta - theta ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hthetaEta htheta0
    nlinarith
  have hmeanTheta : mean * theta = (1 + 4 * eta) * x := by
    dsimp [theta]
    field_simp [ne_of_gt hmeanPos]
  have hlocateCoeff : 1 + eta <= (1 - eta) ^ 2 * (1 + 4 * eta) := by
    have hbracket : 0 <= 1 - 7 * eta + 4 * eta ^ 2 := by
      nlinarith [sq_nonneg eta]
    nlinarith [mul_nonneg heta0' hbracket]
  have hlocate : x + radius <= variance * (theta - theta ^ 2) := by
    calc
      x + radius = (1 + eta) * x := by dsimp [radius]; ring
      _ <= ((1 - eta) ^ 2 * (1 + 4 * eta)) * x :=
        mul_le_mul_of_nonneg_right hlocateCoeff hx.le
      _ = ((1 - eta) * mean) * (theta * (1 - eta)) := by
        calc
          ((1 - eta) ^ 2 * (1 + 4 * eta)) * x =
              (1 - eta) ^ 2 * ((1 + 4 * eta) * x) := by ring
          _ = (1 - eta) ^ 2 * (mean * theta) := by rw [hmeanTheta]
          _ = ((1 - eta) * mean) * (theta * (1 - eta)) := by ring
      _ <= variance * (theta * (1 - eta)) :=
        mul_le_mul_of_nonneg_right hvarianceLower hthetaOneSubEta0
      _ <= variance * (theta - theta ^ 2) :=
        mul_le_mul_of_nonneg_left hthetaLoss hvariance0
  have hexpTheta : Real.exp theta <= 3 := by
    exact (Real.exp_le_exp.mpr htheta1).trans Real.exp_one_lt_three.le
  have hvarianceWindow : 2 * Real.exp theta * variance <= radius ^ 2 := by
    calc
      2 * Real.exp theta * variance <= 2 * 3 * variance := by
        gcongr
      _ <= 6 * mean := by
        nlinarith
      _ <= eta ^ 2 * x ^ 2 := by simpa only [mean] using hlargeDeviation
      _ = radius ^ 2 := by dsimp [radius]; ring
  have hquad := bernoulliSubsetMass_card_ge_quadratic_lower U q hq0 hq1
    htheta0 htheta1 hradius hlocate hvarianceWindow
  have hmeanThetaSq : mean * theta ^ 2 = (1 + 4 * eta) ^ 2 * x ^ 2 / mean := by
    dsimp [theta]
    field_simp [ne_of_gt hmeanPos]
  have hcoeff : mean / 2 + 4 * squareMass <= mean * (1 / 2 + 4 * eta) := by
    nlinarith
  have htermOne : (mean / 2 + 4 * squareMass) * theta ^ 2 <=
      (1 / 2 + 4 * eta) * ((1 + 4 * eta) ^ 2 * x ^ 2 / mean) := by
    calc
      (mean / 2 + 4 * squareMass) * theta ^ 2 <=
          (mean * (1 / 2 + 4 * eta)) * theta ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg theta)
      _ = (1 / 2 + 4 * eta) * (mean * theta ^ 2) := by ring
      _ = _ := by rw [hmeanThetaSq]
  have htermTwo : mean * theta ^ 3 <=
      eta * ((1 + 4 * eta) ^ 2 * x ^ 2 / mean) := by
    calc
      mean * theta ^ 3 = (mean * theta ^ 2) * theta := by ring
      _ <= (mean * theta ^ 2) * eta := by
        exact mul_le_mul_of_nonneg_left hthetaEta (mul_nonneg hmean0 (sq_nonneg theta))
      _ = _ := by rw [hmeanThetaSq]; ring
  have htermThree : theta * radius = eta * (1 + 4 * eta) * x ^ 2 / mean := by
    dsimp [theta, radius]
    field_simp [ne_of_gt hmeanPos]
  have hetaSq : eta ^ 2 <= eta / 100 := by
    have h := mul_le_mul_of_nonneg_left heta1 heta0'
    nlinarith
  have hetaCube : eta ^ 3 <= eta / 10000 := by
    have h := mul_le_mul_of_nonneg_left hetaSq heta0'
    nlinarith
  have hcoarseCoeff :
      (1 / 2 + 4 * eta) * (1 + 4 * eta) ^ 2 +
          eta * (1 + 4 * eta) ^ 2 + eta * (1 + 4 * eta) <=
        1 / 2 + 20 * eta := by
    calc
      (1 / 2 + 4 * eta) * (1 + 4 * eta) ^ 2 +
          eta * (1 + 4 * eta) ^ 2 + eta * (1 + 4 * eta) =
        1 / 2 + 10 * eta + 52 * eta ^ 2 + 80 * eta ^ 3 := by ring
      _ <= 1 / 2 + 10 * eta + 52 * (eta / 100) + 80 * (eta / 10000) := by
        gcongr
      _ <= 1 / 2 + 20 * eta := by linarith
  have hscale0 : 0 <= x ^ 2 / mean := div_nonneg (sq_nonneg x) hmean0
  have hloss : exactLoss <= (1 / 2 + 20 * eta) * (x ^ 2 / mean) := by
    dsimp [exactLoss]
    rw [htermThree]
    calc
      (mean / 2 + 4 * squareMass) * theta ^ 2 + mean * theta ^ 3 +
          eta * (1 + 4 * eta) * x ^ 2 / mean <=
        (1 / 2 + 4 * eta) * ((1 + 4 * eta) ^ 2 * x ^ 2 / mean) +
          eta * ((1 + 4 * eta) ^ 2 * x ^ 2 / mean) +
            eta * (1 + 4 * eta) * x ^ 2 / mean := add_le_add (add_le_add htermOne htermTwo) le_rfl
      _ = ((1 / 2 + 4 * eta) * (1 + 4 * eta) ^ 2 +
          eta * (1 + 4 * eta) ^ 2 + eta * (1 + 4 * eta)) * (x ^ 2 / mean) := by ring
      _ <= (1 / 2 + 20 * eta) * (x ^ 2 / mean) :=
        mul_le_mul_of_nonneg_right hcoarseCoeff hscale0
  calc
    (1 / 2 : Real) * Real.exp (-((1 / 2 + 20 * eta) * x ^ 2 /
        (∑ p ∈ U, q p))) =
        (1 / 2 : Real) * Real.exp (-((1 / 2 + 20 * eta) * x ^ 2 / mean)) := by rfl
    _ <= (1 / 2 : Real) * Real.exp (-exactLoss) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hloss)) (by norm_num)
    _ <= bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := by
      simpa only [exactLoss, mean, squareMass, theta, radius] using hquad

open Classical in
/-- The preceding explicit estimate in the standard moderate-deviation form.  The extra condition
`4 log 2 * mean <= eps * x^2` absorbs the fixed Chebyshev factor `1/2` into the `eps`-loss in the
exponent. -/
theorem bernoulliSubsetMass_card_ge_moderate_lower
    {alpha : Type*} [DecidableEq alpha] (U : Finset alpha) (q : alpha -> Real)
    {eps eta x : Real} (hq0 : ∀ p ∈ U, 0 <= q p) (hq1 : ∀ p ∈ U, q p <= 1)
    (heps : 0 < eps) (heta0 : 0 < eta) (heta1 : eta <= 1 / 100)
    (hetaEps : 80 * eta <= eps)
    (hmean : 0 < ∑ p ∈ U, q p) (hx : 0 < x)
    (hsquareMass : (∑ p ∈ U, (q p) ^ 2) <= eta * ∑ p ∈ U, q p)
    (hsmallTilt : (1 + 4 * eta) * x / (∑ p ∈ U, q p) <= eta)
    (hlargeDeviation : 6 * (∑ p ∈ U, q p) <= eta ^ 2 * x ^ 2)
    (habsorb : 4 * Real.log 2 * (∑ p ∈ U, q p) <= eps * x ^ 2) :
    Real.exp (-((1 + eps) * x ^ 2 / (2 * ∑ p ∈ U, q p))) <=
      bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := by
  let mean : Real := ∑ p ∈ U, q p
  let z : Real := x ^ 2 / mean
  have hmeanPos : 0 < mean := by simpa only [mean] using hmean
  have hz0 : 0 <= z := div_nonneg (sq_nonneg x) hmeanPos.le
  have hfinite := bernoulliSubsetMass_card_ge_explicit_moderate_lower U q hq0 hq1
    heta0 heta1 hmean hx hsquareMass hsmallTilt hlargeDeviation
  have hetaLoss : 20 * eta <= eps / 4 := by linarith
  have hlogLoss : Real.log 2 <= eps / 4 * z := by
    have hmul : Real.log 2 * mean <= eps * x ^ 2 / 4 := by
      have habsorb' : 4 * Real.log 2 * mean <= eps * x ^ 2 := by
        simpa only [mean] using habsorb
      nlinarith [habsorb']
    rw [show eps / 4 * z = (eps * x ^ 2 / 4) / mean by
      dsimp [z]
      field_simp [ne_of_gt hmeanPos]]
    exact (le_div_iff₀ hmeanPos).2 hmul
  have htotal : Real.log 2 + (1 / 2 + 20 * eta) * z <=
      (1 + eps) / 2 * z := by
    have hetaScaled : (1 / 2 + 20 * eta) * z <= (1 / 2 + eps / 4) * z :=
      mul_le_mul_of_nonneg_right (by linarith) hz0
    have hlogScaled := hlogLoss
    nlinarith
  have hhalf : (1 / 2 : Real) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
    norm_num [div_eq_mul_inv]
  calc
    Real.exp (-((1 + eps) * x ^ 2 / (2 * ∑ p ∈ U, q p))) =
        Real.exp (-((1 + eps) / 2 * z)) := by
      dsimp [z, mean]
      congr 2
      field_simp [ne_of_gt hmean]
    _ <= Real.exp (-(Real.log 2 + (1 / 2 + 20 * eta) * z)) :=
      Real.exp_le_exp.mpr (neg_le_neg htotal)
    _ = (1 / 2 : Real) * Real.exp (-((1 / 2 + 20 * eta) * x ^ 2 /
        (∑ p ∈ U, q p))) := by
      rw [hhalf, ← Real.exp_add]
      dsimp [z, mean]
      congr 2
      ring
    _ <= bernoulliSubsetMass U q
        {S | (∑ p ∈ U, q p) + x <= (S.card : Real)} := hfinite

/-! ### The per-prime comparison needed for the multishift coupling -/

/-- Concrete refutation of the tempting conditioned-product identity.  For two independent
Bernoulli(`1/3`) coordinates, conditioning on at most one success gives singleton mass `1/4`,
whereas the categorical law used by `multiShiftMass` gives each singleton mass `1/3`. -/
theorem conditionedIndependent_singleton_ne_categorical :
    (((1 / 3 : Real) * (1 - 1 / 3)) /
      ((1 - 1 / 3) ^ 2 + 2 * (1 / 3) * (1 - 1 / 3))) ≠ 1 / 3 := by
  norm_num

/-- The singleton deficit between `J` independent Bernoulli-`q` coordinates and the categorical
law which selects each singleton with mass `q` is at most `J (J - 1) q²`.  This is the correct
per-prime total-variation cost: the categorical law is *not* literally the independent law
conditioned to have at most one success. -/
theorem independentSingletonDefect_le {q : Real} (hq0 : 0 <= q) (hq1 : q <= 1) (J : Nat) :
    (J : Real) * q * (1 - (1 - q) ^ (J - 1)) <=
      (J : Real) * (J - 1 : Nat) * q ^ 2 := by
  have hbern := one_add_mul_le_pow (a := -q) (by linarith) (J - 1)
  have hdefect : 1 - (1 - q) ^ (J - 1) <= ((J - 1 : Nat) : Real) * q := by
    have hbern' : 1 + ((J - 1 : Nat) : Real) * (-q) <= (1 - q) ^ (J - 1) := by
      simpa only [sub_eq_add_neg] using hbern
    nlinarith [hbern']
  calc
    (J : Real) * q * (1 - (1 - q) ^ (J - 1)) <=
        (J : Real) * q * (((J - 1 : Nat) : Real) * q) :=
      mul_le_mul_of_nonneg_left hdefect (mul_nonneg (Nat.cast_nonneg J) hq0)
    _ = (J : Real) * (J - 1 : Nat) * q ^ 2 := by ring

end NormalNumbers.ErdosBorweinMultiShift
