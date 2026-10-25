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

open Classical in
/-- Expectation of a real observable on the finite Bernoulli subset model. -/
noncomputable def bernoulliSubsetExpectation {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (F : Finset α → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q * F S

open Classical in
theorem bernoulliSubsetWeight_insert_absent {α : Type*} [DecidableEq α]
    {U S : Finset α} {p : α} (q : α → ℝ) (hp : p ∉ U) (hS : S ⊆ U) :
    bernoulliSubsetWeight (insert p U) S q =
      (1 - q p) * bernoulliSubsetWeight U S q := by
  have hpS : p ∉ S := fun hpS ↦ hp (hS hpS)
  simp [bernoulliSubsetWeight, hp, hpS]

open Classical in
theorem bernoulliSubsetWeight_insert_present {α : Type*} [DecidableEq α]
    {U S : Finset α} {p : α} (q : α → ℝ) (hp : p ∉ U) :
    bernoulliSubsetWeight (insert p U) (insert p S) q =
      q p * bernoulliSubsetWeight U S q := by
  rw [bernoulliSubsetWeight, Finset.prod_insert hp]
  simp only [Finset.mem_insert, true_or, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hxp : x ≠ p := by
    intro hxp
    subst x
    exact hp hx
  simp [hxp]

open Classical in
/-- Split an expectation after adjoining one independent Bernoulli coordinate. -/
theorem bernoulliSubsetExpectation_insert {α : Type*} [DecidableEq α]
    {U : Finset α} {p : α} (hp : p ∉ U) (q : α → ℝ) (F : Finset α → ℝ) :
    bernoulliSubsetExpectation (insert p U) q F =
      (1 - q p) * bernoulliSubsetExpectation U q F +
        q p * bernoulliSubsetExpectation U q (fun S ↦ F (insert p S)) := by
  simp only [bernoulliSubsetExpectation]
  rw [Finset.sum_powerset_insert hp]
  apply congrArg₂ (· + ·)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [bernoulliSubsetWeight_insert_absent q hp (Finset.mem_powerset.mp hS)]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [bernoulliSubsetWeight_insert_present q hp]
    ring

open Classical in
/-- Adjoining a coordinate does not change the expectation of an observable that ignores it. -/
theorem bernoulliSubsetExpectation_insert_of_invariant {α : Type*} [DecidableEq α]
    {U : Finset α} {p : α} (hp : p ∉ U) (q : α → ℝ) (F : Finset α → ℝ)
    (hF : ∀ S ∈ U.powerset, F (insert p S) = F S) :
    bernoulliSubsetExpectation (insert p U) q F = bernoulliSubsetExpectation U q F := by
  rw [bernoulliSubsetExpectation_insert hp]
  have hinvariant : bernoulliSubsetExpectation U q (fun S ↦ F (insert p S)) =
      bernoulliSubsetExpectation U q F := by
    apply Finset.sum_congr rfl
    intro S hS
    change bernoulliSubsetWeight U S q * F (insert p S) =
      bernoulliSubsetWeight U S q * F S
    rw [hF S hS]
  rw [hinvariant]
  ring

open Classical in
theorem bernoulliSubsetExpectation_congr {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) {F G : Finset α → ℝ}
    (hFG : ∀ S ∈ U.powerset, F S = G S) :
    bernoulliSubsetExpectation U q F = bernoulliSubsetExpectation U q G := by
  apply Finset.sum_congr rfl
  intro S hS
  rw [hFG S hS]

open Classical in
/-- Marginalization over coordinates disjoint from the support of an observable. -/
theorem bernoulliSubsetExpectation_union_disjoint {α : Type*} [DecidableEq α]
    (B D : Finset α) (hBD : Disjoint B D) (q : α → ℝ) (F : Finset α → ℝ) :
    bernoulliSubsetExpectation (B ∪ D) q (fun S ↦ F (S ∩ B)) =
      bernoulliSubsetExpectation B q F := by
  induction D using Finset.induction_on with
  | empty =>
      simp only [Finset.union_empty]
      apply bernoulliSubsetExpectation_congr
      intro S hS
      rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hS)]
  | @insert p D hp ih =>
      have hpB : p ∉ B := by
        intro hpB
        exact Finset.disjoint_left.mp hBD hpB (Finset.mem_insert_self p D)
      have hBD' : Disjoint B D := hBD.mono_right (Finset.subset_insert p D)
      have hpUnion : p ∉ B ∪ D := by simp [hpB, hp]
      rw [show B ∪ insert p D = insert p (B ∪ D) by ext; simp [or_assoc]]
      calc
        bernoulliSubsetExpectation (insert p (B ∪ D)) q (fun S ↦ F (S ∩ B)) =
            bernoulliSubsetExpectation (B ∪ D) q (fun S ↦ F (S ∩ B)) := by
          apply bernoulliSubsetExpectation_insert_of_invariant hpUnion
          intro S hS
          simp [hpB]
        _ = bernoulliSubsetExpectation B q F := ih hBD'

open Classical in
/-- An observable of `S ∩ B` has the same expectation in every larger Bernoulli universe. -/
theorem bernoulliSubsetExpectation_inter {α : Type*} [DecidableEq α]
    (U B : Finset α) (hBU : B ⊆ U) (q : α → ℝ) (F : Finset α → ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ F (S ∩ B)) =
      bernoulliSubsetExpectation B q F := by
  rw [← Finset.union_sdiff_of_subset hBU]
  exact bernoulliSubsetExpectation_union_disjoint B (U \ B)
    Finset.disjoint_sdiff q F

open Classical in
/-- Cylinder events have the same mass in a Bernoulli universe and in their coordinate support. -/
theorem bernoulliSubsetMass_inter {α : Type*} [DecidableEq α]
    (U B : Finset α) (hBU : B ⊆ U) (q : α → ℝ) (A : Set (Finset α)) :
    bernoulliSubsetMass U q {S | S ∩ B ∈ A} = bernoulliSubsetMass B q A := by
  have hleft : bernoulliSubsetMass U q {S | S ∩ B ∈ A} =
      bernoulliSubsetExpectation U q (fun S ↦ if S ∩ B ∈ A then 1 else 0) := by
    unfold bernoulliSubsetMass bernoulliSubsetExpectation
    apply Finset.sum_congr rfl
    intro S hS
    split <;> simp_all
  have hright : bernoulliSubsetMass B q A =
      bernoulliSubsetExpectation B q (fun S ↦ if S ∈ A then 1 else 0) := by
    unfold bernoulliSubsetMass bernoulliSubsetExpectation
    apply Finset.sum_congr rfl
    intro S hS
    split <;> simp_all
  rw [hleft, hright]
  exact bernoulliSubsetExpectation_inter U B hBU q (fun S ↦ if S ∈ A then 1 else 0)

open Classical in
theorem bernoulliSubsetMass_eq_expectation_indicator {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (A : Set (Finset α)) :
    bernoulliSubsetMass U q A =
      bernoulliSubsetExpectation U q (fun S ↦ if S ∈ A then 1 else 0) := by
  unfold bernoulliSubsetMass bernoulliSubsetExpectation
  apply Finset.sum_congr rfl
  intro S hS
  split <;> simp_all

open Classical in
theorem bernoulliSubsetMass_compl {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (A : Set (Finset α)) :
    bernoulliSubsetMass U q Aᶜ = 1 - bernoulliSubsetMass U q A := by
  have hsum : bernoulliSubsetMass U q A + bernoulliSubsetMass U q Aᶜ = 1 := by
    rw [← sum_bernoulliSubsetWeight U q]
    unfold bernoulliSubsetMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hSA : S ∈ A <;> simp [hSA]
  linarith

open Classical in
/-- Observables on disjoint coordinate blocks are independent in the finite Bernoulli model. -/
theorem bernoulliSubsetExpectation_mul_inter_disjoint {α : Type*} [DecidableEq α]
    (B D : Finset α) (hBD : Disjoint B D) (q : α → ℝ)
    (F G : Finset α → ℝ) :
    bernoulliSubsetExpectation (B ∪ D) q
        (fun S ↦ F (S ∩ B) * G (S ∩ D)) =
      bernoulliSubsetExpectation B q F * bernoulliSubsetExpectation D q G := by
  induction D using Finset.induction_on generalizing G with
  | empty =>
      simp only [Finset.union_empty, Finset.inter_empty]
      have hleft :
          bernoulliSubsetExpectation B q (fun S ↦ F (S ∩ B) * G ∅) =
            bernoulliSubsetExpectation B q (fun S ↦ F S * G ∅) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hS)]
      have hempty : bernoulliSubsetExpectation ∅ q G = G ∅ := by
        simp [bernoulliSubsetExpectation, bernoulliSubsetWeight]
      rw [hleft, hempty]
      unfold bernoulliSubsetExpectation
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S hS
      ring
  | @insert p D hp ih =>
      have hpB : p ∉ B := by
        intro hpB
        exact Finset.disjoint_left.mp hBD hpB (Finset.mem_insert_self p D)
      have hBD' : Disjoint B D := hBD.mono_right (Finset.subset_insert p D)
      have hpUnion : p ∉ B ∪ D := by simp [hpB, hp]
      rw [show B ∪ insert p D = insert p (B ∪ D) by ext; simp [or_assoc]]
      rw [bernoulliSubsetExpectation_insert hpUnion]
      have hzero :
          bernoulliSubsetExpectation (B ∪ D) q
              (fun S ↦ F (S ∩ B) * G (S ∩ insert p D)) =
            bernoulliSubsetExpectation (B ∪ D) q
              (fun S ↦ F (S ∩ B) * G (S ∩ D)) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        have hpS : p ∉ S := by
          intro hpS
          exact hpUnion (Finset.mem_powerset.mp hS hpS)
        congr 2
        ext x
        simp [hpS]
      have hone :
          bernoulliSubsetExpectation (B ∪ D) q
              (fun S ↦ F (insert p S ∩ B) * G (insert p S ∩ insert p D)) =
            bernoulliSubsetExpectation (B ∪ D) q
              (fun S ↦ F (S ∩ B) * G (insert p (S ∩ D))) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        congr 2
        · ext x
          simp [hpB]
        · ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          tauto
      rw [hzero, hone, ih hBD', ih (G := fun S ↦ G (insert p S)) hBD']
      rw [bernoulliSubsetExpectation_insert hp]
      ring

open Classical in
/-- Cylinder events on two disjoint coordinate blocks have product mass. -/
theorem bernoulliSubsetMass_two_cylinders {α : Type*} [DecidableEq α]
    (U B D : Finset α) (hBU : B ⊆ U) (hDU : D ⊆ U) (hBD : Disjoint B D)
    (q : α → ℝ) (A C : Set (Finset α)) :
    bernoulliSubsetMass U q {S | S ∩ B ∈ A ∧ S ∩ D ∈ C} =
      bernoulliSubsetMass U q {S | S ∩ B ∈ A} *
        bernoulliSubsetMass U q {S | S ∩ D ∈ C} := by
  have hUnionU : B ∪ D ⊆ U := Finset.union_subset hBU hDU
  have hleft :
      bernoulliSubsetMass U q {S | S ∩ B ∈ A ∧ S ∩ D ∈ C} =
        bernoulliSubsetMass (B ∪ D) q {S | S ∩ B ∈ A ∧ S ∩ D ∈ C} := by
    rw [← bernoulliSubsetMass_inter U (B ∪ D) hUnionU q
      {S | S ∩ B ∈ A ∧ S ∩ D ∈ C}]
    congr 1
    ext S
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr
        (Finset.subset_union_left : B ⊆ B ∪ D), Finset.inter_eq_right.mpr
        (Finset.subset_union_right : D ⊆ B ∪ D)] using h
    · intro h
      simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr
        (Finset.subset_union_left : B ⊆ B ∪ D), Finset.inter_eq_right.mpr
        (Finset.subset_union_right : D ⊆ B ∪ D)] using h
  have hlocal :
      bernoulliSubsetMass (B ∪ D) q {S | S ∩ B ∈ A ∧ S ∩ D ∈ C} =
        bernoulliSubsetMass B q A * bernoulliSubsetMass D q C := by
    rw [bernoulliSubsetMass_eq_expectation_indicator,
      bernoulliSubsetMass_eq_expectation_indicator,
      bernoulliSubsetMass_eq_expectation_indicator]
    rw [← bernoulliSubsetExpectation_mul_inter_disjoint B D hBD q
      (fun S ↦ if S ∈ A then 1 else 0) (fun S ↦ if S ∈ C then 1 else 0)]
    apply bernoulliSubsetExpectation_congr
    intro S hS
    by_cases hA : S ∩ B ∈ A <;> by_cases hC : S ∩ D ∈ C <;> simp [hA, hC]
  rw [hleft, hlocal, bernoulliSubsetMass_inter U B hBU q A,
    bernoulliSubsetMass_inter U D hDU q C]

open Classical in
/-- Exact finite joint independence for cylinder events on pairwise-disjoint blocks. -/
theorem bernoulliSubsetMass_cylinders {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hBU : ∀ i ∈ I, B i ⊆ U)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (q : α → ℝ) (A : ι → Set (Finset α)) :
    bernoulliSubsetMass U q {S | ∀ i ∈ I, S ∩ B i ∈ A i} =
      ∏ i ∈ I, bernoulliSubsetMass U q {S | S ∩ B i ∈ A i} := by
  induction I using Finset.induction_on with
  | empty => simp [bernoulliSubsetMass_univ]
  | @insert p I hp ih =>
      let D : Finset α := I.biUnion B
      let C : Set (Finset α) := {R | ∀ i ∈ I, R ∩ B i ∈ A i}
      have hpU : B p ⊆ U := hBU p (Finset.mem_insert_self p I)
      have hDU : D ⊆ U := by
        change I.biUnion B ⊆ U
        rw [Finset.biUnion_subset]
        intro i hi
        exact hBU i (Finset.mem_insert_of_mem hi)
      have hpD : Disjoint (B p) D := by
        change Disjoint (B p) (I.biUnion B)
        rw [Finset.disjoint_biUnion_right]
        intro i hi
        exact hdisj p (Finset.mem_insert_self p I) i (Finset.mem_insert_of_mem hi)
          (Ne.symm (fun hip ↦ hp (hip ▸ hi)))
      have hrest : {S | S ∩ D ∈ C} = {S | ∀ i ∈ I, S ∩ B i ∈ A i} := by
        ext S
        simp only [C, Set.mem_setOf_eq]
        constructor <;> intro h i hi
        · have hiD : B i ⊆ D := by
            change B i ⊆ I.biUnion B
            exact Finset.subset_biUnion_of_mem B hi
          simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr hiD] using h i hi
        · have hiD : B i ⊆ D := by
            change B i ⊆ I.biUnion B
            exact Finset.subset_biUnion_of_mem B hi
          simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr hiD] using h i hi
      have hall :
          {S | ∀ i ∈ insert p I, S ∩ B i ∈ A i} =
            {S | S ∩ B p ∈ A p ∧ S ∩ D ∈ C} := by
        ext S
        simp only [Set.mem_setOf_eq, Finset.forall_mem_insert]
        rw [show (∀ i ∈ I, S ∩ B i ∈ A i) ↔ S ∩ D ∈ C by
          simpa only [Set.ext_iff, Set.mem_setOf_eq] using (Set.ext_iff.mp hrest S).symm]
      rw [hall, bernoulliSubsetMass_two_cylinders U (B p) D hpU hDU hpD q (A p) C]
      rw [hrest]
      rw [ih (fun i hi ↦ hBU i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij ↦ hdisj i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij)]
      rw [Finset.prod_insert hp]

open Classical in
/-- A common upper bound for pairwise-disjoint cylinder events multiplies over the blocks. -/
theorem bernoulliSubsetMass_cylinders_le_pow {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hBU : ∀ i ∈ I, B i ⊆ U)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1)
    (A : ι → Set (Finset α)) (c : ℝ)
    (hA : ∀ i ∈ I, bernoulliSubsetMass U q {S | S ∩ B i ∈ A i} ≤ c) :
    bernoulliSubsetMass U q {S | ∀ i ∈ I, S ∩ B i ∈ A i} ≤ c ^ I.card := by
  rw [bernoulliSubsetMass_cylinders U I B hBU hdisj q A]
  calc
    (∏ i ∈ I, bernoulliSubsetMass U q {S | S ∩ B i ∈ A i}) ≤ ∏ _i ∈ I, c :=
      Finset.prod_le_prod
        (fun i hi ↦ bernoulliSubsetMass_nonneg U q _ hq0 hq1)
        (fun i hi ↦ hA i hi)
    _ = c ^ I.card := by simp

open Classical in
/-- If every block event has mass at least `r`, simultaneous failure on pairwise-disjoint blocks
has mass at most `(1-r)^#blocks`. -/
theorem bernoulliSubsetMass_cylinder_complements_le_pow {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hBU : ∀ i ∈ I, B i ⊆ U)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1)
    (A : ι → Set (Finset α)) (r : ℝ)
    (hA : ∀ i ∈ I, r ≤ bernoulliSubsetMass U q {S | S ∩ B i ∈ A i}) :
    bernoulliSubsetMass U q {S | ∀ i ∈ I, S ∩ B i ∉ A i} ≤
      (1 - r) ^ I.card := by
  apply bernoulliSubsetMass_cylinders_le_pow U I B hBU hdisj q hq0 hq1
    (fun i ↦ (A i)ᶜ) (1 - r)
  intro i hi
  have hcompl := bernoulliSubsetMass_compl U q {S | S ∩ B i ∈ A i}
  have heq : {S | S ∩ B i ∈ (A i)ᶜ} = ({S | S ∩ B i ∈ A i} : Set (Finset α))ᶜ := by
    ext S
    simp
  rw [heq, hcompl]
  linarith [hA i hi]

open Classical in
theorem bernoulliSubsetExpectation_const {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (a : ℝ) :
    bernoulliSubsetExpectation U q (fun _ ↦ a) = a := by
  rw [bernoulliSubsetExpectation, ← Finset.sum_mul, sum_bernoulliSubsetWeight]
  exact one_mul a

open Classical in
theorem bernoulliSubsetExpectation_add {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (F G : Finset α → ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ F S + G S) =
      bernoulliSubsetExpectation U q F + bernoulliSubsetExpectation U q G := by
  simp only [bernoulliSubsetExpectation, mul_add, Finset.sum_add_distrib]

open Classical in
theorem bernoulliSubsetExpectation_sub {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (F G : Finset α → ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ F S - G S) =
      bernoulliSubsetExpectation U q F - bernoulliSubsetExpectation U q G := by
  simp only [bernoulliSubsetExpectation, mul_sub, Finset.sum_sub_distrib]

open Classical in
theorem bernoulliSubsetExpectation_const_mul {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (a : ℝ) (F : Finset α → ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ a * F S) =
      a * bernoulliSubsetExpectation U q F := by
  unfold bernoulliSubsetExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

open Classical in
theorem bernoulliSubsetExpectation_sq_sub_const {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (F : Finset α → ℝ) (a : ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ (F S - a) ^ 2) =
      bernoulliSubsetExpectation U q (fun S ↦ (F S) ^ 2) -
        2 * a * bernoulliSubsetExpectation U q F + a ^ 2 := by
  calc
    bernoulliSubsetExpectation U q (fun S ↦ (F S - a) ^ 2) =
        bernoulliSubsetExpectation U q
          (fun S ↦ (F S) ^ 2 - (2 * a) * F S + a ^ 2) := by
      apply bernoulliSubsetExpectation_congr
      intro S hS
      ring
    _ = _ := by
      rw [bernoulliSubsetExpectation_add, bernoulliSubsetExpectation_sub,
        bernoulliSubsetExpectation_const_mul, bernoulliSubsetExpectation_const]

open Classical in
theorem bernoulliSubsetExpectation_sq_add_const {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (F : Finset α → ℝ) (a : ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ (F S + a) ^ 2) =
      bernoulliSubsetExpectation U q (fun S ↦ (F S) ^ 2) +
        2 * a * bernoulliSubsetExpectation U q F + a ^ 2 := by
  calc
    bernoulliSubsetExpectation U q (fun S ↦ (F S + a) ^ 2) =
        bernoulliSubsetExpectation U q
          (fun S ↦ (F S) ^ 2 + (2 * a) * F S + a ^ 2) := by
      apply bernoulliSubsetExpectation_congr
      intro S hS
      ring
    _ = _ := by
      rw [bernoulliSubsetExpectation_add, bernoulliSubsetExpectation_add,
        bernoulliSubsetExpectation_const_mul, bernoulliSubsetExpectation_const]

open Classical in
/-- Fourth-moment update after adding one centered Bernoulli variable.  The cubic cross term
cancels because the old sum has mean zero. -/
theorem bernoulliSubsetExpectation_fourth_mixture {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (F : Finset α → ℝ) (a : ℝ)
    (hmean : bernoulliSubsetExpectation U q F = 0) :
    (1 - a) * bernoulliSubsetExpectation U q (fun S ↦ (F S - a) ^ 4) +
        a * bernoulliSubsetExpectation U q (fun S ↦ (F S + (1 - a)) ^ 4) =
      bernoulliSubsetExpectation U q (fun S ↦ (F S) ^ 4) +
        6 * (a * (1 - a)) * bernoulliSubsetExpectation U q (fun S ↦ (F S) ^ 2) +
        a * (1 - a) * ((1 - a) ^ 3 + a ^ 3) := by
  calc
    (1 - a) * bernoulliSubsetExpectation U q (fun S ↦ (F S - a) ^ 4) +
          a * bernoulliSubsetExpectation U q (fun S ↦ (F S + (1 - a)) ^ 4) =
        bernoulliSubsetExpectation U q (fun S ↦
          (1 - a) * (F S - a) ^ 4 + a * (F S + (1 - a)) ^ 4) := by
      rw [bernoulliSubsetExpectation_add, bernoulliSubsetExpectation_const_mul,
        bernoulliSubsetExpectation_const_mul]
    _ = bernoulliSubsetExpectation U q (fun S ↦
          (F S) ^ 4 + (6 * (a * (1 - a))) * (F S) ^ 2 +
            (4 * (a * (1 - a)) * (1 - 2 * a)) * F S +
              a * (1 - a) * ((1 - a) ^ 3 + a ^ 3)) := by
      apply bernoulliSubsetExpectation_congr
      intro S hS
      ring
    _ = _ := by
      rw [bernoulliSubsetExpectation_add, bernoulliSubsetExpectation_add,
        bernoulliSubsetExpectation_add, bernoulliSubsetExpectation_const_mul,
        bernoulliSubsetExpectation_const_mul, bernoulliSubsetExpectation_const,
        hmean]
      ring

open Classical in
/-- Sum of the centered membership indicators `1_{p ∈ S} - q(p)`. -/
noncomputable def bernoulliCenteredSum {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (S : Finset α) : ℝ :=
  ∑ p ∈ U, if p ∈ S then 1 - q p else -q p

open Classical in
/-- Centered membership sums add over disjoint coordinate blocks. -/
theorem bernoulliCenteredSum_union {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (q : α → ℝ) (S : Finset α) :
    bernoulliCenteredSum (A ∪ B) q S =
      bernoulliCenteredSum A q S + bernoulliCenteredSum B q S := by
  unfold bernoulliCenteredSum
  exact Finset.sum_union hAB

open Classical in
/-- A centered membership sum is the selected cardinality minus its Bernoulli mean. -/
theorem bernoulliCenteredSum_eq_card_inter_sub_sum {α : Type*} [DecidableEq α]
    (U S : Finset α) (q : α → ℝ) :
    bernoulliCenteredSum U q S =
      ((S ∩ U).card : ℝ) - ∑ p ∈ U, q p := by
  unfold bernoulliCenteredSum
  calc
    ∑ p ∈ U, (if p ∈ S then (1 : ℝ) - q p else -q p) =
        ∑ p ∈ U, ((if p ∈ S then (1 : ℝ) else 0) - q p) := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpS : p ∈ S <;> simp [hpS]
    _ = (∑ p ∈ U, if p ∈ S then (1 : ℝ) else 0) - ∑ p ∈ U, q p := by
      rw [Finset.sum_sub_distrib]
    _ = ((S ∩ U).card : ℝ) - ∑ p ∈ U, q p := by
      congr 1
      norm_cast
      rw [← Finset.card_filter]
      congr 1
      ext p
      simp [and_comm]

open Classical in
theorem bernoulliCenteredSum_inter {α : Type*} [DecidableEq α]
    (U S : Finset α) (q : α → ℝ) :
    bernoulliCenteredSum U q (S ∩ U) = bernoulliCenteredSum U q S := by
  unfold bernoulliCenteredSum
  apply Finset.sum_congr rfl
  intro p hp
  simp [hp]

open Classical in
theorem bernoulliCenteredSum_insert_absent {α : Type*} [DecidableEq α]
    {U S : Finset α} {p : α} (q : α → ℝ) (hp : p ∉ U) (hpS : p ∉ S) :
    bernoulliCenteredSum (insert p U) q S = bernoulliCenteredSum U q S - q p := by
  simp [bernoulliCenteredSum, hp, hpS]
  ring

open Classical in
theorem bernoulliCenteredSum_insert_present {α : Type*} [DecidableEq α]
    {U S : Finset α} {p : α} (q : α → ℝ) (hp : p ∉ U) :
    bernoulliCenteredSum (insert p U) q (insert p S) =
      bernoulliCenteredSum U q S + (1 - q p) := by
  unfold bernoulliCenteredSum
  rw [Finset.sum_insert hp]
  simp only [Finset.mem_insert, true_or, if_true]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hxp : x ≠ p := by
    intro hxp
    subst x
    exact hp hx
  simp [hxp]

open Classical in
/-- A sum of centered independent Bernoulli indicators has mean zero. -/
theorem bernoulliSubset_centeredSum_expectation {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) :
    bernoulliSubsetExpectation U q (bernoulliCenteredSum U q) = 0 := by
  induction U using Finset.induction_on with
  | empty => simp [bernoulliSubsetExpectation, bernoulliCenteredSum, bernoulliSubsetWeight]
  | @insert p U hp ih =>
      rw [bernoulliSubsetExpectation_insert hp]
      have habsent : bernoulliSubsetExpectation U q (bernoulliCenteredSum (insert p U) q) =
          bernoulliSubsetExpectation U q (fun S ↦ bernoulliCenteredSum U q S - q p) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        exact bernoulliCenteredSum_insert_absent q hp
          (Finset.notMem_of_mem_powerset_of_notMem hS hp)
      have hpresent : bernoulliSubsetExpectation U q
            (fun S ↦ bernoulliCenteredSum (insert p U) q (insert p S)) =
          bernoulliSubsetExpectation U q
            (fun S ↦ bernoulliCenteredSum U q S + (1 - q p)) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        exact bernoulliCenteredSum_insert_present q hp
      rw [habsent, hpresent, bernoulliSubsetExpectation_sub,
        bernoulliSubsetExpectation_add, bernoulliSubsetExpectation_const,
        bernoulliSubsetExpectation_const, ih]
      ring

open Classical in
/-- Exact variance identity for a finite sum of centered independent Bernoulli indicators. -/
theorem bernoulliSubset_centeredSum_secondMoment {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) :
    bernoulliSubsetExpectation U q (fun S ↦ (bernoulliCenteredSum U q S) ^ 2) =
      ∑ p ∈ U, q p * (1 - q p) := by
  induction U using Finset.induction_on with
  | empty => simp [bernoulliSubsetExpectation, bernoulliCenteredSum, bernoulliSubsetWeight]
  | @insert p U hp ih =>
      rw [bernoulliSubsetExpectation_insert hp]
      have habsent : bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum (insert p U) q S) ^ 2) =
          bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum U q S - q p) ^ 2) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        rw [bernoulliCenteredSum_insert_absent q hp
          (Finset.notMem_of_mem_powerset_of_notMem hS hp)]
      have hpresent : bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum (insert p U) q (insert p S)) ^ 2) =
          bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum U q S + (1 - q p)) ^ 2) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        rw [bernoulliCenteredSum_insert_present q hp]
      rw [habsent, hpresent, bernoulliSubsetExpectation_sq_sub_const,
        bernoulliSubsetExpectation_sq_add_const,
        bernoulliSubset_centeredSum_expectation, ih, Finset.sum_insert hp]
      ring

open Classical in
/-- Fourth-moment bound for a finite sum of centered independent Bernoulli indicators. -/
theorem bernoulliSubset_centeredSum_fourthMoment_le {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p)
    (hq1 : ∀ p ∈ U, q p ≤ 1) :
    bernoulliSubsetExpectation U q (fun S ↦ (bernoulliCenteredSum U q S) ^ 4) ≤
      3 * (∑ p ∈ U, q p * (1 - q p)) ^ 2 + ∑ p ∈ U, q p * (1 - q p) := by
  induction U using Finset.induction_on with
  | empty => simp [bernoulliSubsetExpectation, bernoulliCenteredSum, bernoulliSubsetWeight]
  | @insert p U hp ih =>
      have hq0U : ∀ x ∈ U, 0 ≤ q x := fun x hx ↦ hq0 x (Finset.mem_insert_of_mem hx)
      have hq1U : ∀ x ∈ U, q x ≤ 1 := fun x hx ↦ hq1 x (Finset.mem_insert_of_mem hx)
      have ihU := ih hq0U hq1U
      have hqp0 : 0 ≤ q p := hq0 p (Finset.mem_insert_self p U)
      have hqp1 : q p ≤ 1 := hq1 p (Finset.mem_insert_self p U)
      let V : ℝ := ∑ x ∈ U, q x * (1 - q x)
      let v : ℝ := q p * (1 - q p)
      have hv0 : 0 ≤ v := mul_nonneg hqp0 (sub_nonneg.mpr hqp1)
      have hlocal :
          q p * (1 - q p) * ((1 - q p) ^ 3 + (q p) ^ 3) ≤ v := by
        have hid : q p * (1 - q p) * ((1 - q p) ^ 3 + (q p) ^ 3) =
            v - 3 * v ^ 2 := by
          simp only [v]
          ring
        rw [hid]
        nlinarith [sq_nonneg v]
      rw [bernoulliSubsetExpectation_insert hp]
      have habsent : bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum (insert p U) q S) ^ 4) =
          bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum U q S - q p) ^ 4) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        rw [bernoulliCenteredSum_insert_absent q hp
          (Finset.notMem_of_mem_powerset_of_notMem hS hp)]
      have hpresent : bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum (insert p U) q (insert p S)) ^ 4) =
          bernoulliSubsetExpectation U q
            (fun S ↦ (bernoulliCenteredSum U q S + (1 - q p)) ^ 4) := by
        apply bernoulliSubsetExpectation_congr
        intro S hS
        rw [bernoulliCenteredSum_insert_present q hp]
      rw [habsent, hpresent,
        bernoulliSubsetExpectation_fourth_mixture U q (bernoulliCenteredSum U q) (q p)
          (bernoulliSubset_centeredSum_expectation U q),
        bernoulliSubset_centeredSum_secondMoment, Finset.sum_insert hp]
      change bernoulliSubsetExpectation U q
          (fun S ↦ (bernoulliCenteredSum U q S) ^ 4) + 6 * v * V +
            q p * (1 - q p) * ((1 - q p) ^ 3 + (q p) ^ 3) ≤
        3 * (v + V) ^ 2 + (v + V)
      nlinarith [sq_nonneg v]

open Classical in
/-- Chebyshev bound for a centered Bernoulli subset sum, stated directly in terms of event mass. -/
theorem bernoulliSubsetMass_centeredSum_abs_ge_le {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p)
    (hq1 : ∀ p ∈ U, q p ≤ 1) {r : ℝ} (hr : 0 < r) :
    bernoulliSubsetMass U q {S | r ≤ |bernoulliCenteredSum U q S|} ≤
      (∑ p ∈ U, q p * (1 - q p)) / r ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  apply (le_div_iff₀ hr2).2
  rw [← bernoulliSubset_centeredSum_secondMoment U q]
  unfold bernoulliSubsetMass bernoulliSubsetExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro S hS
  have hw : 0 ≤ bernoulliSubsetWeight U S q :=
    bernoulliSubsetWeight_nonneg U S q hq0 hq1
  by_cases hlarge : r ≤ |bernoulliCenteredSum U q S|
  · simp only [Set.mem_setOf_eq, hlarge, if_true]
    have hsquare : r ^ 2 ≤ (bernoulliCenteredSum U q S) ^ 2 := by
      nlinarith [sq_nonneg (|bernoulliCenteredSum U q S| - r),
        sq_abs (bernoulliCenteredSum U q S)]
    exact mul_le_mul_of_nonneg_left hsquare hw
  · simp only [Set.mem_setOf_eq, hlarge, if_false, zero_mul]
    exact mul_nonneg hw (sq_nonneg _)

/-- A finite centered law with controlled fourth moment has a uniformly positive upper tail.
This elementary one-sided Paley--Zygmund substitute is phrased for raw finite sums so that it can
also be reused outside the Bernoulli subset model. -/
theorem finite_centered_fourth_upperTail
    {ι : Type*} (s : Finset ι) (w X : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwt : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * X i = 0) {V : ℝ}
    (hsecond : ∑ i ∈ s, w i * (X i) ^ 2 = V) (hV : 1 ≤ V)
    (hfourth : ∑ i ∈ s, w i * (X i) ^ 4 ≤ 4 * V ^ 2) :
    (1 : ℝ) / 64 ≤ ∑ i ∈ s, if Real.sqrt V / 8 ≤ X i then w i else 0 := by
  let t : ℝ := Real.sqrt V
  let A : ℝ := ∑ i ∈ s, w i * |X i|
  let B : ℝ := ∑ i ∈ s, w i * |X i| ^ 3
  let C : ℝ := ∑ i ∈ s, w i * (X i)⁺
  let Tail : ℝ := ∑ i ∈ s, if t / 8 ≤ X i then w i * (X i)⁺ else 0
  let P : ℝ := ∑ i ∈ s, if t / 8 ≤ X i then w i else 0
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have ht : 0 < t := Real.sqrt_pos.2 hVpos
  have ht_sq : t ^ 2 = V := Real.sq_sqrt hVpos.le
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (abs_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i hi ↦
    mul_nonneg (hw i hi) (pow_nonneg (abs_nonneg _) _)
  have hVAB : V ^ 2 ≤ A * B := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun i ↦ w i * (X i) ^ 2)
      (f := fun i ↦ w i * |X i|)
      (g := fun i ↦ w i * |X i| ^ 3)
      (fun i hi ↦ mul_nonneg (hw i hi) (abs_nonneg _))
      (fun i hi ↦ mul_nonneg (hw i hi) (pow_nonneg (abs_nonneg _) _))
      (fun i hi ↦ by
        have hx : (X i) ^ 2 = |X i| ^ 2 := (sq_abs (X i)).symm
        rw [hx]
        ring_nf
        exact le_rfl)
    simpa only [hsecond, A, B] using hcs
  have hBsq : B ^ 2 ≤ V * (4 * V ^ 2) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun i ↦ w i * |X i| ^ 3)
      (f := fun i ↦ w i * (X i) ^ 2)
      (g := fun i ↦ w i * (X i) ^ 4)
      (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _))
      (fun i hi ↦ by
        have hx4 : 0 ≤ (X i) ^ 4 := by positivity
        exact mul_nonneg (hw i hi) hx4)
      (fun i hi ↦ by
        have hx : (X i) ^ 2 = |X i| ^ 2 := (sq_abs (X i)).symm
        have hx4 : (X i) ^ 4 = |X i| ^ 4 := by
          calc
            (X i) ^ 4 = ((X i) ^ 2) ^ 2 := by ring
            _ = (|X i| ^ 2) ^ 2 := by rw [hx]
            _ = |X i| ^ 4 := by ring
        rw [hx, hx4]
        ring_nf
        exact le_rfl)
    calc
      B ^ 2 ≤ (∑ i ∈ s, w i * (X i) ^ 2) * ∑ i ∈ s, w i * (X i) ^ 4 := by
        simpa only [B] using hcs
      _ ≤ V * (4 * V ^ 2) := by rw [hsecond]; gcongr
  have hB_le : B ≤ 2 * V * t := by
    apply (sq_le_sq₀ hB0 (by positivity : 0 ≤ 2 * V * t)).mp
    calc
      B ^ 2 ≤ V * (4 * V ^ 2) := hBsq
      _ = (2 * V * t) ^ 2 := by rw [← ht_sq]; ring
  have ht_le_two_A : t ≤ 2 * A := by
    have hmul : A * B ≤ A * (2 * V * t) := mul_le_mul_of_nonneg_left hB_le hA0
    have hcancel : (V * t) * t ≤ (V * t) * (2 * A) := by
      calc
        (V * t) * t = V ^ 2 := by rw [← ht_sq]; ring
        _ ≤ A * B := hVAB
        _ ≤ A * (2 * V * t) := hmul
        _ = (V * t) * (2 * A) := by ring
    exact le_of_mul_le_mul_left hcancel (mul_pos hVpos ht)
  have hC : A = 2 * C := by
    calc
      A = (∑ i ∈ s, w i * X i) + A := by rw [hmean, zero_add]
      _ = ∑ i ∈ s, (w i * X i + w i * |X i|) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ s, 2 * (w i * (X i)⁺) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_add, add_abs_eq_two_nsmul_posPart]
        simp only [nsmul_eq_mul]
        ring
      _ = 2 * C := by rw [Finset.mul_sum]
  have ht_four_le_C : t / 4 ≤ C := by nlinarith [ht_le_two_A]
  have hC_le : C ≤ t / 8 + Tail := by
    calc
      C ≤ ∑ i ∈ s, (w i * (t / 8) + if t / 8 ≤ X i then w i * (X i)⁺ else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hlarge : t / 8 ≤ X i
        · simp only [hlarge, if_true]
          exact le_add_of_nonneg_left (mul_nonneg (hw i hi) (by positivity))
        · simp only [hlarge, if_false, add_zero]
          apply mul_le_mul_of_nonneg_left _ (hw i hi)
          rw [posPart_def]
          exact max_le (le_of_not_ge hlarge) (by positivity)
      _ = t / 8 + Tail := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hwt, one_mul]
  have hTail_lower : t / 8 ≤ Tail := by linarith
  have hTail0 : 0 ≤ Tail := Finset.sum_nonneg fun i hi ↦ by
    split
    · exact mul_nonneg (hw i hi) (posPart_nonneg _)
    · exact le_rfl
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i hi ↦ by
    split
    · exact hw i hi
    · exact le_rfl
  have hposSecond : (∑ i ∈ s, w i * ((X i)⁺) ^ 2) ≤ V := by
    rw [← hsecond]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    by_cases hx : 0 ≤ X i
    · rw [posPart_eq_self.mpr hx]
    · rw [posPart_eq_zero.mpr (le_of_not_ge hx), zero_pow (by norm_num : 2 ≠ 0)]
      exact sq_nonneg _
  have hTail_sq : Tail ^ 2 ≤ V * P := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun i ↦ if t / 8 ≤ X i then w i * (X i)⁺ else 0)
      (f := fun i ↦ w i * ((X i)⁺) ^ 2)
      (g := fun i ↦ if t / 8 ≤ X i then w i else 0)
      (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _))
      (fun i hi ↦ by split <;> simp_all)
      (fun i hi ↦ by
        by_cases hlarge : t / 8 ≤ X i
        · simp only [hlarge, if_true]
          ring_nf
          exact le_rfl
        · simp [hlarge])
    calc
      Tail ^ 2 ≤ (∑ i ∈ s, w i * ((X i)⁺) ^ 2) * P := by
        simpa only [Tail, P] using hcs
      _ ≤ V * P := mul_le_mul_of_nonneg_right hposSecond hP0
  have hthreshold_sq : (t / 8) ^ 2 ≤ Tail ^ 2 :=
    (sq_le_sq₀ (by positivity) hTail0).2 hTail_lower
  have hVP : V / 64 ≤ V * P := by
    calc
      V / 64 = (t / 8) ^ 2 := by rw [← ht_sq]; ring
      _ ≤ Tail ^ 2 := hthreshold_sq
      _ ≤ V * P := hTail_sq
  have := le_of_mul_le_mul_left (show V * ((1 : ℝ) / 64) ≤ V * P by
    calc
      V * ((1 : ℝ) / 64) = V / 64 := by ring
      _ ≤ V * P := hVP) hVpos
  simpa only [P, t] using this

open Classical in
/-- Uniform one-sided crossing probability for a Bernoulli block whose variance is at least one. -/
theorem bernoulliSubsetMass_centeredSum_ge_sqrt_eighth {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p)
    (hq1 : ∀ p ∈ U, q p ≤ 1)
    (hV : 1 ≤ ∑ p ∈ U, q p * (1 - q p)) :
    (1 : ℝ) / 64 ≤ bernoulliSubsetMass U q
      {S | Real.sqrt (∑ p ∈ U, q p * (1 - q p)) / 8 ≤ bernoulliCenteredSum U q S} := by
  let V : ℝ := ∑ p ∈ U, q p * (1 - q p)
  have hfourth :
      bernoulliSubsetExpectation U q (fun S ↦ (bernoulliCenteredSum U q S) ^ 4) ≤
        4 * V ^ 2 := by
    have hbound := bernoulliSubset_centeredSum_fourthMoment_le U q hq0 hq1
    change bernoulliSubsetExpectation U q (fun S ↦ (bernoulliCenteredSum U q S) ^ 4) ≤
      4 * V ^ 2
    change bernoulliSubsetExpectation U q (fun S ↦ (bernoulliCenteredSum U q S) ^ 4) ≤
      3 * V ^ 2 + V at hbound
    have hV0 : 0 ≤ V := zero_le_one.trans hV
    nlinarith [sq_nonneg (V - 1)]
  have htail := finite_centered_fourth_upperTail U.powerset
    (fun S ↦ bernoulliSubsetWeight U S q) (bernoulliCenteredSum U q)
    (fun S hS ↦ bernoulliSubsetWeight_nonneg U S q hq0 hq1)
    (sum_bernoulliSubsetWeight U q)
    (bernoulliSubset_centeredSum_expectation U q)
    (bernoulliSubset_centeredSum_secondMoment U q) hV hfourth
  simpa only [V, bernoulliSubsetMass, Set.mem_ofPred_eq] using htail

open Classical in
/-- The one-sided block bound inside any larger Bernoulli universe. -/
theorem bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth {α : Type*} [DecidableEq α]
    (U B : Finset α) (hBU : B ⊆ U) (q : α → ℝ)
    (hq0 : ∀ p ∈ B, 0 ≤ q p) (hq1 : ∀ p ∈ B, q p ≤ 1)
    (hV : 1 ≤ ∑ p ∈ B, q p * (1 - q p)) :
    (1 : ℝ) / 64 ≤ bernoulliSubsetMass U q
      {S | Real.sqrt (∑ p ∈ B, q p * (1 - q p)) / 8 ≤ bernoulliCenteredSum B q S} := by
  let A : Set (Finset α) :=
    {S | Real.sqrt (∑ p ∈ B, q p * (1 - q p)) / 8 ≤ bernoulliCenteredSum B q S}
  calc
    (1 : ℝ) / 64 ≤ bernoulliSubsetMass B q A :=
      bernoulliSubsetMass_centeredSum_ge_sqrt_eighth B q hq0 hq1 hV
    _ = bernoulliSubsetMass U q {S | S ∩ B ∈ A} :=
      (bernoulliSubsetMass_inter U B hBU q A).symm
    _ = bernoulliSubsetMass U q
        {S | Real.sqrt (∑ p ∈ B, q p * (1 - q p)) / 8 ≤
          bernoulliCenteredSum B q S} := by
      congr 1
      ext S
      simp only [A, Set.mem_ofPred_eq]
      rw [bernoulliCenteredSum_inter]

open Classical in
/-- The exact fixed-block consequence of the one-block crossing estimate: on pairwise-disjoint
blocks of variance at least one, the probability that every centered increment misses its
`sqrt(V)/8` crossing is at most `(63/64)^#blocks`. -/
theorem bernoulliSubsetMass_all_blockCenteredSum_lt_sqrt_eighth_le {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hBU : ∀ i ∈ I, B i ⊆ U)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (q : α → ℝ) (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1)
    (hV : ∀ i ∈ I, 1 ≤ ∑ p ∈ B i, q p * (1 - q p)) :
    bernoulliSubsetMass U q
        {S | ∀ i ∈ I, bernoulliCenteredSum (B i) q S <
          Real.sqrt (∑ p ∈ B i, q p * (1 - q p)) / 8} ≤
      ((63 : ℝ) / 64) ^ I.card := by
  let A : ι → Set (Finset α) := fun i ↦
    {S | Real.sqrt (∑ p ∈ B i, q p * (1 - q p)) / 8 ≤
      bernoulliCenteredSum (B i) q S}
  have hAi : ∀ i ∈ I, (1 : ℝ) / 64 ≤
      bernoulliSubsetMass U q {S | S ∩ B i ∈ A i} := by
    intro i hi
    calc
      (1 : ℝ) / 64 ≤ bernoulliSubsetMass U q
          {S | Real.sqrt (∑ p ∈ B i, q p * (1 - q p)) / 8 ≤
            bernoulliCenteredSum (B i) q S} :=
        bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth U (B i) (hBU i hi) q
          (fun p hp ↦ hq0 p (hBU i hi hp)) (fun p hp ↦ hq1 p (hBU i hi hp)) (hV i hi)
      _ = bernoulliSubsetMass U q {S | S ∩ B i ∈ A i} := by
        congr 1
        ext S
        simp only [A, Set.mem_ofPred_eq]
        rw [bernoulliCenteredSum_inter]
  have hbound := bernoulliSubsetMass_cylinder_complements_le_pow
    U I B hBU hdisj q hq0 hq1 A ((1 : ℝ) / 64) hAi
  have hevent :
      {S | ∀ i ∈ I, S ∩ B i ∉ A i} =
        {S | ∀ i ∈ I, bernoulliCenteredSum (B i) q S <
          Real.sqrt (∑ p ∈ B i, q p * (1 - q p)) / 8} := by
    ext S
    simp only [A, Set.mem_setOf_eq, not_le]
    constructor <;> intro h i hi
    · simpa only [bernoulliCenteredSum_inter] using h i hi
    · simpa only [bernoulliCenteredSum_inter] using h i hi
  rw [hevent] at hbound
  norm_num at hbound ⊢
  exact hbound

end NormalNumbers.ErdosBorweinEndpointKub
