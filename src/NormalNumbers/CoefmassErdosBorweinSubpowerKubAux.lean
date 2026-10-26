/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Finite Bernoulli maximal inequality for the Kubilius model

This file proves the finite-product version of Doob's exponential maximal inequality directly on
the powerset model.  The recursive proof is a first-passage argument, so it avoids setting up a
measure-space filtration while retaining the sharp moment-generating-function bound.
-/

namespace NormalNumbers.ErdosBorweinSubpowerKub

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
/-- Finite distributivity: summing over all choices factors into local sums. -/
theorem sum_subsetChoiceWeight {α : Type*} [DecidableEq α]
    (U : Finset α) (f g : α → ℝ) :
    ∑ S ∈ U.powerset, subsetChoiceWeight U S f g = ∏ p ∈ U, (f p + g p) := by
  rw [Finset.prod_add f g U]
  apply Finset.sum_congr rfl
  intro S hS
  rw [subsetChoiceWeight_eq U S f g (Finset.mem_powerset.mp hS)]

open Classical in
/-- Mass of one subset under independent Bernoulli variables with parameters `q`. -/
noncomputable def bernoulliSubsetWeight {α : Type*} [DecidableEq α]
    (U S : Finset α) (q : α → ℝ) : ℝ :=
  ∏ p ∈ U, if p ∈ S then q p else 1 - q p

open Classical in
/-- Finite distributivity for Bernoulli subset weights. -/
theorem sum_bernoulliSubsetWeight {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) :
    ∑ S ∈ U.powerset, bernoulliSubsetWeight U S q = 1 := by
  change ∑ S ∈ U.powerset,
    subsetChoiceWeight U S q (fun p ↦ 1 - q p) = 1
  rw [sum_subsetChoiceWeight]
  simp

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
theorem bernoulliSubsetMass_congr {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) {A B : Set (Finset α)}
    (hAB : ∀ S ∈ U.powerset, S ∈ A ↔ S ∈ B) :
    bernoulliSubsetMass U q A = bernoulliSubsetMass U q B := by
  apply Finset.sum_congr rfl
  intro S hS
  rw [if_congr (hAB S hS) rfl rfl]

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
/-- Split an event after adjoining one independent Bernoulli coordinate. -/
theorem bernoulliSubsetMass_insert {α : Type*} [DecidableEq α]
    {U : Finset α} {p : α} (hp : p ∉ U) (q : α → ℝ) (A : Set (Finset α)) :
    bernoulliSubsetMass (insert p U) q A =
      (1 - q p) * bernoulliSubsetMass U q A +
        q p * bernoulliSubsetMass U q {S | insert p S ∈ A} := by
  unfold bernoulliSubsetMass
  rw [Finset.sum_powerset_insert hp]
  apply congrArg₂ (· + ·)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [bernoulliSubsetWeight_insert_absent q hp (Finset.mem_powerset.mp hS)]
    by_cases hSA : S ∈ A <;> simp [hSA]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [bernoulliSubsetWeight_insert_present q hp]
    by_cases hSA : insert p S ∈ A <;> simp [hSA]

/-- The centered Bernoulli walk, started at `z`, reaches `h` along one of the ordered prefixes.
The empty prefix is included. -/
def centeredBernoulliHit {α : Type*} [DecidableEq α] (q : α → ℝ) (h : ℝ) :
    ℝ → List α → Finset α → Prop
  | z, [], _ => h ≤ z
  | z, p :: l, S =>
      h ≤ z ∨ centeredBernoulliHit q h
        (z + if p ∈ S then 1 - q p else -q p) l S

/-- Centered sum along the first `k` coordinates of an ordered Bernoulli family. -/
noncomputable def centeredBernoulliPrefixSum {α : Type*} [DecidableEq α]
    (q : α → ℝ) (S : Finset α) (l : List α) (k : ℕ) : ℝ :=
  ((l.take k).map fun p ↦ if p ∈ S then 1 - q p else -q p).sum

@[simp]
theorem centeredBernoulliPrefixSum_zero {α : Type*} [DecidableEq α]
    (q : α → ℝ) (S : Finset α) (l : List α) :
    centeredBernoulliPrefixSum q S l 0 = 0 := by
  simp [centeredBernoulliPrefixSum]

@[simp]
theorem centeredBernoulliPrefixSum_succ_cons {α : Type*} [DecidableEq α]
    (q : α → ℝ) (S : Finset α) (p : α) (l : List α) (k : ℕ) :
    centeredBernoulliPrefixSum q S (p :: l) (k + 1) =
      (if p ∈ S then 1 - q p else -q p) + centeredBernoulliPrefixSum q S l k := by
  simp [centeredBernoulliPrefixSum]

/-- Extensional meaning of the recursive first-passage event. -/
theorem centeredBernoulliHit_iff_exists_prefix {α : Type*} [DecidableEq α]
    (q : α → ℝ) (h z : ℝ) (l : List α) (S : Finset α) :
    centeredBernoulliHit q h z l S ↔
      ∃ k ≤ l.length, h ≤ z + centeredBernoulliPrefixSum q S l k := by
  induction l generalizing z with
  | nil => simp [centeredBernoulliHit]
  | cons p l ih =>
      simp only [centeredBernoulliHit]
      constructor
      · rintro (hz | hrest)
        · exact ⟨0, by simp, by simpa using hz⟩
        · rw [ih] at hrest
          obtain ⟨k, hk, hsum⟩ := hrest
          refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
          rw [centeredBernoulliPrefixSum_succ_cons]
          linarith
      · rintro ⟨k, hk, hsum⟩
        cases k with
        | zero =>
            left
            simpa using hsum
        | succ k =>
            right
            rw [ih]
            refine ⟨k, by simp only [List.length_cons] at hk; omega, ?_⟩
            rw [centeredBernoulliPrefixSum_succ_cons] at hsum
            linarith

theorem centeredBernoulliHit_insert_invariant {α : Type*} [DecidableEq α]
    (q : α → ℝ) (h z : ℝ) (l : List α) {p : α} (hp : p ∉ l) (S : Finset α) :
    centeredBernoulliHit q h z l (insert p S) ↔ centeredBernoulliHit q h z l S := by
  induction l generalizing z with
  | nil => simp [centeredBernoulliHit]
  | cons a l ih =>
      have hap : a ≠ p := by
        intro hap
        subst a
        exact hp (by simp)
      have hpl : p ∉ l := by
        intro hpl
        exact hp (by simp [hpl])
      simp only [centeredBernoulliHit, Finset.mem_insert, hap, false_or]
      exact or_congr Iff.rfl (ih _ hpl)

/-- Recursive first-passage mass of a centered Bernoulli walk. -/
noncomputable def centeredBernoulliHitMass {α : Type*}
    (q : α → ℝ) (h : ℝ) : ℝ → List α → ℝ
  | z, [] => if h ≤ z then 1 else 0
  | z, p :: l =>
      if h ≤ z then 1
      else (1 - q p) * centeredBernoulliHitMass q h (z - q p) l +
        q p * centeredBernoulliHitMass q h (z + (1 - q p)) l

open Classical in
/-- The recursive first-passage mass is exactly the corresponding powerset event. -/
theorem bernoulliSubsetMass_centeredBernoulliHit_eq {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (q : α → ℝ) (h z : ℝ) :
    bernoulliSubsetMass l.toFinset q {S | centeredBernoulliHit q h z l S} =
      centeredBernoulliHitMass q h z l := by
  induction l generalizing z with
  | nil =>
      by_cases hz : h ≤ z
      · rw [show {S : Finset α | centeredBernoulliHit q h z [] S} = Set.univ by
            ext S
            simp [centeredBernoulliHit, hz]]
        simp [bernoulliSubsetMass_univ, centeredBernoulliHitMass, hz]
      · simp [bernoulliSubsetMass, centeredBernoulliHit,
          centeredBernoulliHitMass, hz]
  | cons p l ih =>
      obtain ⟨hp, hl⟩ := List.nodup_cons.mp hl
      have hpFin : p ∉ l.toFinset := by simpa using hp
      by_cases hz : h ≤ z
      · rw [show {S : Finset α | centeredBernoulliHit q h z (p :: l) S} = Set.univ by
            ext S
            simp [centeredBernoulliHit, hz]]
        simp [bernoulliSubsetMass_univ, centeredBernoulliHitMass, hz]
      · rw [List.toFinset_cons, bernoulliSubsetMass_insert hpFin]
        have habsent :
            bernoulliSubsetMass l.toFinset q
                {S | centeredBernoulliHit q h z (p :: l) S} =
              bernoulliSubsetMass l.toFinset q
                {S | centeredBernoulliHit q h (z - q p) l S} := by
          apply bernoulliSubsetMass_congr
          intro S hS
          have hpS : p ∉ S := by
            intro hpS
            exact hpFin (Finset.mem_powerset.mp hS hpS)
          simp only [Set.mem_ofPred_eq, centeredBernoulliHit, hz, false_or, hpS, if_false]
          rw [sub_eq_add_neg]
        have hpresent :
            bernoulliSubsetMass l.toFinset q
                {S | insert p S ∈ {S | centeredBernoulliHit q h z (p :: l) S}} =
              bernoulliSubsetMass l.toFinset q
                {S | centeredBernoulliHit q h (z + (1 - q p)) l S} := by
          apply bernoulliSubsetMass_congr
          intro S hS
          simp only [Set.mem_ofPred_eq, centeredBernoulliHit, hz, false_or,
            Finset.mem_insert]
          exact centeredBernoulliHit_insert_invariant q h (z + (1 - q p)) l hp S
        rw [habsent, hpresent, ih hl, ih hl]
        simp [centeredBernoulliHitMass, hz]

/-- One-step moment-generating function of a centered Bernoulli variable. -/
noncomputable def centeredBernoulliMGF {α : Type*} (q : α → ℝ) (θ : ℝ) (p : α) : ℝ :=
  (1 - q p) * Real.exp (-θ * q p) + q p * Real.exp (θ * (1 - q p))

/-- A centered Bernoulli moment-generating function is at least one. -/
theorem one_le_centeredBernoulliMGF {α : Type*} (q : α → ℝ) (θ : ℝ) (p : α)
    (hq0 : 0 ≤ q p) (hq1 : q p ≤ 1) :
    1 ≤ centeredBernoulliMGF q θ p := by
  have hcenter : (1 - q p) * (-θ * q p) + q p * (θ * (1 - q p)) = 0 := by ring
  calc
    1 = Real.exp ((1 - q p) * (-θ * q p) + q p * (θ * (1 - q p))) := by
      rw [hcenter, Real.exp_zero]
    _ ≤ (1 - q p) * Real.exp (-θ * q p) + q p * Real.exp (θ * (1 - q p)) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
        (sub_nonneg.mpr hq1) hq0 (by ring)
    _ = centeredBernoulliMGF q θ p := rfl

/-- The exact finite first-passage/Doob bound, before estimating the local moment-generating
functions. -/
theorem centeredBernoulliHitMass_le_mgfProduct {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (q : α → ℝ)
    (hq0 : ∀ p ∈ l, 0 ≤ q p) (hq1 : ∀ p ∈ l, q p ≤ 1)
    (θ h z : ℝ) (hθ : 0 ≤ θ) :
    centeredBernoulliHitMass q h z l ≤
      Real.exp (θ * (z - h)) * ∏ p ∈ l.toFinset, centeredBernoulliMGF q θ p := by
  induction l generalizing z with
  | nil =>
      by_cases hz : h ≤ z
      · simp only [centeredBernoulliHitMass, List.toFinset_nil, Finset.prod_empty, mul_one]
        rw [if_pos hz]
        exact Real.one_le_exp (mul_nonneg hθ (sub_nonneg.mpr hz))
      · rw [centeredBernoulliHitMass, if_neg hz]
        simp only [List.toFinset_nil, Finset.prod_empty, mul_one]
        exact (Real.exp_pos _).le
  | cons p l ih =>
      obtain ⟨hp, hl⟩ := List.nodup_cons.mp hl
      have hpFin : p ∉ l.toFinset := by simpa using hp
      have hqp0 : 0 ≤ q p := hq0 p (by simp)
      have hqp1 : q p ≤ 1 := hq1 p (by simp)
      have hql0 : ∀ x ∈ l, 0 ≤ q x := by
        intro x hx
        exact hq0 x (by simp [hx])
      have hql1 : ∀ x ∈ l, q x ≤ 1 := by
        intro x hx
        exact hq1 x (by simp [hx])
      by_cases hz : h ≤ z
      · rw [centeredBernoulliHitMass]
        simp only [hz, if_true, List.toFinset_cons, Finset.prod_insert hpFin]
        have hexp : 1 ≤ Real.exp (θ * (z - h)) :=
          Real.one_le_exp (mul_nonneg hθ (sub_nonneg.mpr hz))
        have hlocal : 1 ≤ centeredBernoulliMGF q θ p :=
          one_le_centeredBernoulliMGF q θ p hqp0 hqp1
        have htail : 1 ≤ ∏ x ∈ l.toFinset, centeredBernoulliMGF q θ x := by
          apply Finset.one_le_prod
          intro x hx
          exact one_le_centeredBernoulliMGF q θ x
            (hql0 x (by simpa using hx)) (hql1 x (by simpa using hx))
        exact one_le_mul_of_one_le_of_one_le hexp
          (one_le_mul_of_one_le_of_one_le hlocal htail)
      · have hzero := ih hl hql0 hql1 (z - q p)
        have hone := ih hl hql0 hql1 (z + (1 - q p))
        rw [centeredBernoulliHitMass]
        simp only [hz, if_false, List.toFinset_cons, Finset.prod_insert hpFin]
        calc
          (1 - q p) * centeredBernoulliHitMass q h (z - q p) l +
                q p * centeredBernoulliHitMass q h (z + (1 - q p)) l ≤
              (1 - q p) * (Real.exp (θ * (z - q p - h)) *
                ∏ x ∈ l.toFinset, centeredBernoulliMGF q θ x) +
              q p * (Real.exp (θ * (z + (1 - q p) - h)) *
                ∏ x ∈ l.toFinset, centeredBernoulliMGF q θ x) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hzero (sub_nonneg.mpr hqp1))
              (mul_le_mul_of_nonneg_left hone hqp0)
          _ = Real.exp (θ * (z - h)) *
                centeredBernoulliMGF q θ p *
                ∏ x ∈ l.toFinset, centeredBernoulliMGF q θ x := by
            have hezero : Real.exp (θ * (z - q p - h)) =
                Real.exp (θ * (z - h)) * Real.exp (-θ * q p) := by
              rw [← Real.exp_add]
              congr 1
              ring
            have heone : Real.exp (θ * (z + (1 - q p) - h)) =
                Real.exp (θ * (z - h)) * Real.exp (θ * (1 - q p)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [hezero, heone]
            unfold centeredBernoulliMGF
            ring
          _ = Real.exp (θ * (z - h)) *
                (centeredBernoulliMGF q θ p *
                  ∏ x ∈ l.toFinset, centeredBernoulliMGF q θ x) := by ring

/-- The centered Bernoulli moment-generating function has the standard Bennett upper bound. -/
theorem centeredBernoulliMGF_le_exp {α : Type*} (q : α → ℝ) (θ : ℝ) (p : α) :
    centeredBernoulliMGF q θ p ≤
      Real.exp ((Real.exp θ - 1 - θ) * q p) := by
  have he : Real.exp (θ * (1 - q p)) = Real.exp (-θ * q p) * Real.exp θ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor : centeredBernoulliMGF q θ p =
      Real.exp (-θ * q p) * (1 + q p * (Real.exp θ - 1)) := by
    unfold centeredBernoulliMGF
    rw [he]
    ring
  have hbase : 1 + q p * (Real.exp θ - 1) ≤
      Real.exp (q p * (Real.exp θ - 1)) := by
    simpa only [add_comm] using Real.add_one_le_exp (q p * (Real.exp θ - 1))
  calc
    centeredBernoulliMGF q θ p =
        Real.exp (-θ * q p) * (1 + q p * (Real.exp θ - 1)) := hfactor
    _ ≤ Real.exp (-θ * q p) * Real.exp (q p * (Real.exp θ - 1)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp ((Real.exp θ - 1 - θ) * q p) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Cubic Taylor bound in the exact form used by the geometric-block argument. -/
theorem exp_sub_one_sub_id_le_half_sq_add_cube {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.exp θ - 1 - θ ≤ θ ^ 2 / 2 + θ ^ 3 := by
  have h := Real.exp_bound' hθ0 hθ1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [sq_nonneg θ, mul_nonneg (sq_nonneg θ) hθ0]

/-- Product form of the Bennett estimate. -/
theorem prod_centeredBernoulliMGF_le_exp {α : Type*} [DecidableEq α]
    (U : Finset α) (q : α → ℝ) (θ : ℝ)
    (hq0 : ∀ p ∈ U, 0 ≤ q p) (hq1 : ∀ p ∈ U, q p ≤ 1) :
    (∏ p ∈ U, centeredBernoulliMGF q θ p) ≤
      Real.exp ((Real.exp θ - 1 - θ) * ∑ p ∈ U, q p) := by
  calc
    (∏ p ∈ U, centeredBernoulliMGF q θ p) ≤
        ∏ p ∈ U, Real.exp ((Real.exp θ - 1 - θ) * q p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact zero_le_one.trans
          (one_le_centeredBernoulliMGF q θ p (hq0 p hp) (hq1 p hp))
      · intro p hp
        exact centeredBernoulliMGF_le_exp q θ p
    _ = Real.exp (∑ p ∈ U, (Real.exp θ - 1 - θ) * q p) := by
      rw [Real.exp_sum]
    _ = Real.exp ((Real.exp θ - 1 - θ) * ∑ p ∈ U, q p) := by
      rw [Finset.mul_sum]

/-- Finite-product Doob/Ville inequality for a centered Bernoulli walk. -/
theorem bernoulliSubsetMass_centeredBernoulliHit_le_exp
    {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (q : α → ℝ)
    (hq0 : ∀ p ∈ l, 0 ≤ q p) (hq1 : ∀ p ∈ l, q p ≤ 1)
    (θ h : ℝ) (hθ : 0 ≤ θ) :
    bernoulliSubsetMass l.toFinset q {S | centeredBernoulliHit q h 0 l S} ≤
      Real.exp ((Real.exp θ - 1 - θ) * ∑ p ∈ l.toFinset, q p - θ * h) := by
  rw [bernoulliSubsetMass_centeredBernoulliHit_eq l hl q h 0]
  have hfirst := centeredBernoulliHitMass_le_mgfProduct l hl q hq0 hq1 θ h 0 hθ
  have hprod := prod_centeredBernoulliMGF_le_exp l.toFinset q θ
    (fun p hp ↦ hq0 p (by simpa using hp)) (fun p hp ↦ hq1 p (by simpa using hp))
  calc
    centeredBernoulliHitMass q h 0 l ≤
        Real.exp (θ * (0 - h)) *
          ∏ p ∈ l.toFinset, centeredBernoulliMGF q θ p := hfirst
    _ ≤ Real.exp (θ * (0 - h)) *
          Real.exp ((Real.exp θ - 1 - θ) * ∑ p ∈ l.toFinset, q p) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp ((Real.exp θ - 1 - θ) * ∑ p ∈ l.toFinset, q p - θ * h) := by
      rw [← Real.exp_add]
      congr 1
      ring

end NormalNumbers.ErdosBorweinSubpowerKub
