/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Finite Bernoulli subset model

Algebraic foundations for the Kubilius-model endpoint argument.  These lemmas avoid a measure-space
encoding: a state is a subset of a finite set, and its mass is the product of the Bernoulli factors.
`bernoulliSubset_expectation_prod` is the independence identity used by all later moment estimates.
-/

namespace NormalNumbers.ErdosBorweinEndpointKub

open scoped BigOperators

open Classical in
/-- Product obtained by independently choosing the `f` or `g` factor at every site. -/
noncomputable def subsetChoiceWeight {α : Type*} [DecidableEq α]
    (U S : Finset α) (f g : α → ℝ) : ℝ :=
  ∏ p ∈ U, if p ∈ S then f p else g p

open Classical in
theorem subsetChoiceWeight_eq {α : Type*} [DecidableEq α]
    (U S : Finset α) (f g : α → ℝ) (hS : S ⊆ U) :
    subsetChoiceWeight U S f g = (∏ p ∈ S, f p) * ∏ p ∈ U \ S, g p := by
  rw [subsetChoiceWeight, Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter]
  have hinter : U ∩ S = S := Finset.inter_eq_right.mpr hS
  rw [hinter]
  have hdiff : U.filter (fun x ↦ x ∉ S) = U \ S := by ext; simp
  rw [hdiff]

open Classical in
/-- Finite distributivity: summing over all choices factors into a product of local sums. -/
theorem sum_subsetChoiceWeight {α : Type*} [DecidableEq α]
    (U : Finset α) (f g : α → ℝ) :
    ∑ S ∈ U.powerset, subsetChoiceWeight U S f g = ∏ p ∈ U, (f p + g p) := by
  rw [Finset.prod_add f g U]
  apply Finset.sum_congr rfl
  intro S hS
  rw [subsetChoiceWeight_eq U S f g (Finset.mem_powerset.mp hS)]

open Classical in
/-- Mass of one subset under independent Bernoulli variables of parameters `q`. -/
noncomputable def bernoulliSubsetWeight {α : Type*} [DecidableEq α]
    (U S : Finset α) (q : α → ℝ) : ℝ :=
  ∏ p ∈ U, if p ∈ S then q p else 1 - q p

open Classical in
theorem bernoulliSubsetWeight_eq {α : Type*} [DecidableEq α]
    (U S : Finset α) (q : α → ℝ) (hS : S ⊆ U) :
    bernoulliSubsetWeight U S q = (∏ p ∈ S, q p) * ∏ p ∈ U \ S, (1 - q p) :=
  subsetChoiceWeight_eq U S q (fun p ↦ 1 - q p) hS

open Classical in
/-- The Bernoulli subset weights have total mass one. -/
theorem sum_bernoulliSubsetWeight {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) :
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q = 1 := by
  change ∑ S ∈ U.powerset, subsetChoiceWeight U S q (fun p ↦ 1 - q p) = 1
  rw [sum_subsetChoiceWeight]
  simp

open Classical in
/-- Bernoulli subset weights are nonnegative when every parameter lies in `[0,1]`. -/
theorem bernoulliSubsetWeight_nonneg {α : Type*} [DecidableEq α]
    (U S : Finset α) (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p)
    (hq1 : ∀ p ∈ U, q p ≤ 1) :
    0 ≤ bernoulliSubsetWeight U S q := by
  apply Finset.prod_nonneg
  intro p hp
  by_cases h : p ∈ S
  · simp [h, hq0 p hp]
  · simp [h, sub_nonneg.mpr (hq1 p hp)]

open Classical in
/-- Mass of an event in the finite Bernoulli subset model. -/
noncomputable def bernoulliSubsetMass {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (A : Set (Finset α)) : ℝ :=
  ∑ S ∈ U.powerset, if S ∈ A then bernoulliSubsetWeight U S q else 0

open Classical in
theorem bernoulliSubsetMass_univ {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) :
    bernoulliSubsetMass U q Set.univ = 1 := by
  simp [bernoulliSubsetMass, sum_bernoulliSubsetWeight]

open Classical in
theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (A : Set (Finset α))
    (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1) :
    0 ≤ bernoulliSubsetMass U q A := by
  apply Finset.sum_nonneg
  intro S hS
  split
  · exact bernoulliSubsetWeight_nonneg U S q hq0 hq1
  · exact le_rfl

open Classical in
theorem bernoulliSubsetMass_mono {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) {A B : Set (Finset α)} (hAB : A ⊆ B)
    (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1) :
    bernoulliSubsetMass U q A ≤ bernoulliSubsetMass U q B := by
  apply Finset.sum_le_sum
  intro S hS
  by_cases hSA : S ∈ A
  · simp [hSA, hAB hSA]
  · simp only [hSA, if_false]
    split
    · exact bernoulliSubsetWeight_nonneg U S q hq0 hq1
    · exact le_rfl

open Classical in
theorem bernoulliSubsetMass_le_one {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (A : Set (Finset α))
    (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1) :
    bernoulliSubsetMass U q A ≤ 1 := by
  rw [← bernoulliSubsetMass_univ U q]
  exact bernoulliSubsetMass_mono U q (Set.subset_univ A) hq0 hq1

open Classical in
/-- Independence identity for arbitrary products of local two-valued observables. -/
theorem bernoulliSubset_expectation_prod {α : Type*} [DecidableEq α]
    (U : Finset α) (q a b : α → ℝ) :
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q *
        ∏ p ∈ U, (if p ∈ S then a p else b p) =
      ∏ p ∈ U, (q p * a p + (1 - q p) * b p) := by
  calc
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q *
        ∏ p ∈ U, (if p ∈ S then a p else b p) =
      ∑ S ∈ U.powerset,
        subsetChoiceWeight U S (fun p ↦ q p * a p) (fun p ↦ (1 - q p) * b p) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [bernoulliSubsetWeight, subsetChoiceWeight, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : p ∈ S <;> simp [h]
    _ = _ := sum_subsetChoiceWeight _ _ _

open Classical in
/-- One coordinate has expectation equal to its Bernoulli parameter. -/
theorem bernoulliSubset_membership_expectation {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) {p : α} (hp : p ∈ U) :
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q *
        (if p ∈ S then 1 else 0) = q p := by
  have h := bernoulliSubset_expectation_prod U q
    (fun _ ↦ 1) (fun i ↦ if i = p then 0 else 1)
  have hlhs : ∀ S ∈ U.powerset,
      (∏ i ∈ U, if i ∈ S then (1 : ℝ) else if i = p then 0 else 1) =
        if p ∈ S then 1 else 0 := by
    intro S hS
    by_cases hpm : p ∈ S
    · simp only [hpm, if_true]
      apply Finset.prod_eq_one
      intro i hi
      by_cases hiS : i ∈ S
      · simp [hiS]
      · have hip : i ≠ p := by
          intro hip
          subst i
          exact hiS hpm
        simp [hiS, hip]
    · simp only [hpm, if_false]
      refine Finset.prod_eq_zero hp ?_
      simp [hpm]
  have hlhs' :
      (∑ S ∈ U.powerset, bernoulliSubsetWeight U S q *
        ∏ i ∈ U, if i ∈ S then (1 : ℝ) else if i = p then 0 else 1) =
      ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q *
        (if p ∈ S then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [hlhs S hS]
  rw [hlhs'] at h
  have hrhs :
      (∏ i ∈ U, (q i * 1 + (1 - q i) * if i = p then 0 else 1)) = q p := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton p _ (fun hnot ↦ (hnot hp).elim)]
    have hprod : ∏ i ∈ U \ {p},
        (q i * 1 + (1 - q i) * if i = p then 0 else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hip : i ≠ p := by simpa using (Finset.mem_sdiff.mp hi).2
      simp [hip]
    rw [hprod]
    simp
  rw [hrhs] at h
  exact h

open Classical in
/-- The subset cardinality has mean `∑ p ∈ U, q p`. -/
theorem bernoulliSubset_card_expectation {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) :
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q * (S.card : ℝ) =
      ∑ p ∈ U, q p := by
  have hcard : ∀ S ∈ U.powerset,
      (S.card : ℝ) = ∑ p ∈ U, if p ∈ S then 1 else 0 := by
    intro S hS
    have hsub := Finset.mem_powerset.mp hS
    have hfilter : U.filter (fun p ↦ p ∈ S) = S := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hsub h, h⟩
    have hnat : S.card = ∑ p ∈ U, if p ∈ S then 1 else 0 := by
      rw [← Finset.card_filter, hfilter]
    exact_mod_cast hnat
  calc
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q * (S.card : ℝ) =
        ∑ S ∈ U.powerset, ∑ p ∈ U,
          bernoulliSubsetWeight U S q * (if p ∈ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hcard S hS, Finset.mul_sum]
    _ = ∑ p ∈ U, ∑ S ∈ U.powerset,
          bernoulliSubsetWeight U S q * (if p ∈ S then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ U, q p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact bernoulliSubset_membership_expectation U q hp

end NormalNumbers.ErdosBorweinEndpointKub
