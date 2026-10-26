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

end NormalNumbers.ErdosBorweinMultiShift
