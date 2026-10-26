/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CoefmassErdosBorweinMultiShift

/-!
# Auxiliary finite second-moment tools for the pair-shift argument

This file contains only generic finite probability lemmas.  The packet-verbatim pair model and
headline remain in `CoefmassErdosBorweinPairShift`.
-/

namespace NormalNumbers.ErdosBorweinPairShift

open scoped BigOperators
open NormalNumbers.ErdosBorweinMultiShift

/-- Finite Chebyshev in the exact form needed for a zero-count event.  The sample mean is supplied
as an explicit parameter so later applications can rewrite it as a sum of event densities. -/
theorem card_filter_eq_zero_div_le_secondMoment
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (m : ℝ)
    (hS : S.Nonempty) (hm : (∑ x ∈ S, f x) / (S.card : ℝ) = m) (hm0 : 0 < m) :
    ((((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) / (S.card : ℝ)) ≤
      (((∑ x ∈ S, (f x) ^ 2) / (S.card : ℝ) - m ^ 2) / m ^ 2) := by
  classical
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hmeanSum : (∑ x ∈ S, f x) = (S.card : ℝ) * m := by
    rw [div_eq_iff (ne_of_gt hcard)] at hm
    simpa [mul_comm] using hm
  have hcentered : (∑ x ∈ S, (f x - m) ^ 2) =
      (∑ x ∈ S, (f x) ^ 2) - (S.card : ℝ) * m ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcross : (∑ x ∈ S, 2 * f x * m) = 2 * m * (∑ x ∈ S, f x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hcross, hmeanSum]
    ring
  have hzero : (((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) * m ^ 2 ≤
      ∑ x ∈ S, (f x - m) ^ 2 := by
    calc
      (((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) * m ^ 2 =
          ∑ _x ∈ (S.filter fun x ↦ f x = 0), m ^ 2 := by simp
      _ = ∑ x ∈ (S.filter fun x ↦ f x = 0), (f x - m) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hfx : f x = 0 := (Finset.mem_filter.mp hx).2
        rw [hfx]
        ring
      _ ≤ ∑ x ∈ S, (f x - m) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro x hxS hxnot
        positivity
  have hmSq : 0 < m ^ 2 := sq_pos_of_pos hm0
  rw [le_div_iff₀ hmSq]
  rw [div_mul_eq_mul_div]
  rw [show (∑ x ∈ S, (f x) ^ 2) / (S.card : ℝ) - m ^ 2 =
      ((∑ x ∈ S, (f x) ^ 2) - (S.card : ℝ) * m ^ 2) / (S.card : ℝ) by
    rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hcard)] ]
  exact (div_le_div_iff_of_pos_right hcard).2 (hcentered ▸ hzero)

open Classical in
/-- The real-valued number of events from `I` which occur at a sample point. -/
noncomputable def finiteEventCount {ι α : Type*} (I : Finset ι)
    (H : ι → α → Prop) (x : α) : ℝ :=
  ∑ i ∈ I, if H i x then 1 else 0

open Classical in
theorem finiteEventCount_eq_zero_of_forall_not {ι α : Type*} (I : Finset ι)
    (H : ι → α → Prop) (x : α) (hx : ∀ i ∈ I, ¬H i x) :
    finiteEventCount I H x = 0 := by
  classical
  unfold finiteEventCount
  apply Finset.sum_eq_zero
  intro i hi
  simp [hx i hi]

open Classical in
/-- First-moment expansion for a finite family of indicator events. -/
theorem sum_finiteEventCount {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (S : Finset α) (H : ι → α → Prop) :
    (∑ x ∈ S, finiteEventCount I H x) =
      ∑ i ∈ I, (((S.filter fun x ↦ H i x).card : ℕ) : ℝ) := by
  classical
  simp only [finiteEventCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.card_filter]
  push_cast
  rfl

open Classical in
/-- Second-moment expansion for a finite family of indicator events. -/
theorem sum_finiteEventCount_sq {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (S : Finset α) (H : ι → α → Prop) :
    (∑ x ∈ S, (finiteEventCount I H x) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I,
        (((S.filter fun x ↦ H i x ∧ H j x).card : ℕ) : ℝ) := by
  classical
  simp only [finiteEventCount, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hi : H i x <;> by_cases hj : H j x <;> simp [hi, hj]

/-- Under the fully independent prime-by-shift model, simultaneous heavy-column events factor. -/
theorem independentShiftProduct_all_heavy_factor {n J : ℕ} (q : Fin n → ℝ)
    (threshold : Fin J → ℕ) :
    finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i))
        {σ | ∀ j, threshold j ≤ (Finset.univ.filter fun i ↦ j ∈ σ i).card} =
      ∏ j, NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin n × Fin J)) (fun z ↦ q z.1)
        {S | threshold j ≤ (S ∩ shiftArrayColumn n J j).card} := by
  have hfactor := independentShiftProduct_columns_factor q
    (fun j ↦ {R : Finset (Fin n × Fin J) | threshold j ≤ R.card})
  simpa only [Set.mem_ofPred_eq, card_shiftArrayEquiv_inter_column] using hfactor

/-- Relabel the finite state space of every coordinate by an equivalence. -/
theorem finiteProductMass_relabel {n : ℕ} {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (e : β ≃ γ) (w : Fin n → β → ℝ)
    (A : Set (Fin n → γ)) :
    finiteProductMass (fun i y ↦ w i (e.symm y)) A =
      finiteProductMass w {σ | (fun i ↦ e (σ i)) ∈ A} := by
  apply finiteProductMass_pushforward e w (fun i y ↦ w i (e.symm y))
  intro i y
  classical
  calc
    (∑ x, if e x = y then w i x else 0) =
        (if e (e.symm y) = y then w i (e.symm y) else 0) := by
      apply Fintype.sum_eq_single (e.symm y)
      intro x hx
      have hne : e x ≠ y := by
        intro hxy
        apply hx
        rw [← hxy]
        simp
      simp [hne]
    _ = w i (e.symm y) := by simp

/-- Abstract coupling bound for an arbitrary categorical event.  If singleton clearing preserves
the event away from prime collisions, its categorical mass is at most the corresponding fully
independent mass plus twice the reciprocal-square collision budget. -/
theorem categoricalShiftProduct_event_le_independent
    {n J : ℕ} (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hJq : ∀ i, (J : ℝ) * q i ≤ 1)
    (C : Set (Fin n → Option (Fin J))) (R : Set (Fin n → Finset (Fin J)))
    (hpreserve : ∀ σ : Fin n → Finset (Fin J),
      (∀ i, (σ i).card ≤ 1) →
      (fun i ↦ singletonClearing (σ i)) ∈ C → σ ∈ R) :
    finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C ≤
      finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R +
        2 * ∑ i, (J : ℝ) * (J - 1 : ℕ) * (q i) ^ 2 := by
  classical
  let D : Set (Fin n → Finset (Fin J)) := {σ | ∃ i, 2 ≤ (σ i).card}
  let E : ℝ := ∑ i, (J : ℝ) * (J - 1 : ℕ) * (q i) ^ 2
  have hpreimage :
      {σ | (fun i ↦ singletonClearing (σ i)) ∈ C} ⊆ R ∪ D := by
    intro σ hσ
    by_cases hD : σ ∈ D
    · exact Set.mem_union_right R hD
    · apply Set.mem_union_left D
      apply hpreserve σ
      · intro i
        have hi : ¬2 ≤ (σ i).card := by
          intro hi
          exact hD ⟨i, hi⟩
        omega
      · exact hσ
  have hcleared :
      finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C ≤
        finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R + E := by
    rw [clearedProductMass_eq_independentClearedMass]
    calc
      finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i))
          {σ | (fun i ↦ singletonClearing (σ i)) ∈ C} ≤
          finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) (R ∪ D) :=
        finiteProductMass_mono _ hpreimage
          (fun i S ↦ independentShiftSubsetWeight_nonneg (hq0 i) (hq1 i) S)
      _ ≤ finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R +
          finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) D :=
        finiteProductMass_union_le _ R D
          (fun i S ↦ independentShiftSubsetWeight_nonneg (hq0 i) (hq1 i) S)
      _ ≤ finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R + E := by
        gcongr
        simpa only [D, E] using independentShiftProductCollisionMass_le q hq0 hq1
  have hcomparison := categorical_cleared_product_comparison q hq0 hq1 hJq C
  have hcat : finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C ≤
      finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C + E := by
    calc
      finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C =
          (finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C -
            finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C) +
              finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C := by ring
      _ ≤ |finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C -
            finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C| +
              finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C :=
        add_le_add_left (le_abs_self _) _
      _ ≤ E + finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C := by
        simpa only [E] using
          (add_le_add_left hcomparison
            (finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C))
      _ = finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C + E :=
        add_comm _ _
  change finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C ≤
    finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R + 2 * E
  calc
    finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C ≤
        finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C + E := hcat
    _ ≤ (finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R + E) + E :=
      by gcongr
    _ = finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R + 2 * E := by ring

/-- Two-sided form of `categoricalShiftProduct_event_le_independent`.  It applies when singleton
clearing identifies the categorical and independent events exactly away from collisions. -/
theorem abs_categoricalShiftProduct_event_sub_independent_le
    {n J : ℕ} (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hJq : ∀ i, (J : ℝ) * q i ≤ 1)
    (C : Set (Fin n → Option (Fin J))) (R : Set (Fin n → Finset (Fin J)))
    (hevent : ∀ σ : Fin n → Finset (Fin J),
      (∀ i, (σ i).card ≤ 1) →
      ((fun i ↦ singletonClearing (σ i)) ∈ C ↔ σ ∈ R)) :
    |finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C -
        finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R| ≤
      2 * ∑ i, (J : ℝ) * (J - 1 : ℕ) * (q i) ^ 2 := by
  classical
  let D : Set (Fin n → Finset (Fin J)) := {σ | ∃ i, 2 ≤ (σ i).card}
  let E : ℝ := ∑ i, (J : ℝ) * (J - 1 : ℕ) * (q i) ^ 2
  have hforward := categoricalShiftProduct_event_le_independent q hq0 hq1 hJq C R
    (fun σ hσ hC ↦ (hevent σ hσ).mp hC)
  have hreverseSubset :
      R ⊆ {σ | (fun i ↦ singletonClearing (σ i)) ∈ C} ∪ D := by
    intro σ hR
    by_cases hD : σ ∈ D
    · exact Set.mem_union_right _ hD
    · apply Set.mem_union_left D
      apply (hevent σ ?_).mpr hR
      intro i
      have hi : ¬2 ≤ (σ i).card := by
        intro hi
        exact hD ⟨i, hi⟩
      omega
  have hindToCleared :
      finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R ≤
        finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C + E := by
    rw [clearedProductMass_eq_independentClearedMass]
    calc
      finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R ≤
          finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i))
            ({σ | (fun i ↦ singletonClearing (σ i)) ∈ C} ∪ D) :=
        finiteProductMass_mono _ hreverseSubset
          (fun i S ↦ independentShiftSubsetWeight_nonneg (hq0 i) (hq1 i) S)
      _ ≤ finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i))
            {σ | (fun i ↦ singletonClearing (σ i)) ∈ C} +
          finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) D :=
        finiteProductMass_union_le _ _ D
          (fun i S ↦ independentShiftSubsetWeight_nonneg (hq0 i) (hq1 i) S)
      _ ≤ finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i))
            {σ | (fun i ↦ singletonClearing (σ i)) ∈ C} + E := by
        gcongr
        simpa only [D, E] using independentShiftProductCollisionMass_le q hq0 hq1
  have hcomparison := categorical_cleared_product_comparison q hq0 hq1 hJq C
  have hclearedToCat :
      finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C ≤
        finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C + E := by
    calc
      finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C =
          (finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C -
            finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C) +
              finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C := by ring
      _ ≤ |finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C -
            finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C| +
              finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C := by
        rw [abs_sub_comm]
        exact add_le_add_left (le_abs_self _) _
      _ ≤ E + finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C := by
        simpa only [E] using
          (add_le_add_left hcomparison
            (finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C))
      _ = finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C + E :=
        add_comm _ _
  rw [abs_le]
  constructor
  · have hreverse : finiteProductMass (fun i ↦ independentShiftSubsetWeight J (q i)) R ≤
        finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C + 2 * E := by
      calc
        _ ≤ finiteProductMass (fun i ↦ clearedIndependentShiftWeight J (q i)) C + E :=
          hindToCleared
        _ ≤ (finiteProductMass (fun i ↦ categoricalShiftWeight J (q i)) C + E) + E := by
          gcongr
        _ = _ := by ring
    change -(2 * E) ≤ _ - _
    linarith
  · change _ - _ ≤ 2 * E
    apply sub_le_iff_le_add.mpr
    rw [add_comm]
    simpa only [E] using hforward

/-- One-coordinate law of the frozen Bool-indexed pair model. -/
noncomputable def pairBoolWeight (q : ℝ) : Option Bool → ℝ
  | none => 1 - 2 * q
  | some _ => q

/-- Abstract Bool-indexed pair-model mass of two simultaneous cardinality tails. -/
noncomputable def pairBoolCountMass {n : ℕ} (q : Fin n → ℝ) (t₀ t₁ : ℕ) : ℝ :=
  finiteProductMass (fun i ↦ pairBoolWeight (q i))
    {σ | t₀ ≤ (Finset.univ.filter fun i ↦ σ i = some false).card ∧
      t₁ ≤ (Finset.univ.filter fun i ↦ σ i = some true).card}

/-- The Bool-indexed categorical pair model differs from two independent Bernoulli columns only
by the explicit prime-collision budget. -/
theorem abs_pairBoolCountMass_sub_independent_le {n : ℕ} (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (h2q : ∀ i, 2 * q i ≤ 1)
    (t₀ t₁ : ℕ) :
    |pairBoolCountMass q t₀ t₁ -
        (NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
          (Finset.univ : Finset (Fin n × Fin 2)) (fun z ↦ q z.1)
          {S | t₀ ≤ (S ∩ shiftArrayColumn n 2 0).card}) *
        (NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
          (Finset.univ : Finset (Fin n × Fin 2)) (fun z ↦ q z.1)
          {S | t₁ ≤ (S ∩ shiftArrayColumn n 2 1).card})| ≤
      4 * ∑ i, (q i) ^ 2 := by
  classical
  let e : Option (Fin 2) ≃ Option Bool := Equiv.optionCongr finTwoEquiv
  let C : Set (Fin n → Option (Fin 2)) :=
    {τ | t₀ ≤ (Finset.univ.filter fun i ↦ τ i = some 0).card ∧
      t₁ ≤ (Finset.univ.filter fun i ↦ τ i = some 1).card}
  let R : Set (Fin n → Finset (Fin 2)) :=
    {σ | t₀ ≤ (Finset.univ.filter fun i ↦ (0 : Fin 2) ∈ σ i).card ∧
      t₁ ≤ (Finset.univ.filter fun i ↦ (1 : Fin 2) ∈ σ i).card}
  have hpair : pairBoolCountMass q t₀ t₁ =
      finiteProductMass (fun i ↦ categoricalShiftWeight 2 (q i)) C := by
    have hrelabel := finiteProductMass_relabel e
      (fun i ↦ categoricalShiftWeight 2 (q i))
      {σ : Fin n → Option Bool |
        t₀ ≤ (Finset.univ.filter fun i ↦ σ i = some false).card ∧
        t₁ ≤ (Finset.univ.filter fun i ↦ σ i = some true).card}
    have hweight :
        (fun i y ↦ categoricalShiftWeight 2 (q i) (e.symm y)) =
          (fun i ↦ pairBoolWeight (q i)) := by
      funext i y
      cases y with
      | none => rfl
      | some b => cases b <;> rfl
    rw [hweight] at hrelabel
    simpa [pairBoolCountMass, C, e, finTwoEquiv] using hrelabel
  have hevent : ∀ σ : Fin n → Finset (Fin 2),
      (∀ i, (σ i).card ≤ 1) →
      ((fun i ↦ singletonClearing (σ i)) ∈ C ↔ σ ∈ R) := by
    intro σ hσ
    have hzero := singletonClearing_column_eq σ hσ (0 : Fin 2)
    have hone := singletonClearing_column_eq σ hσ (1 : Fin 2)
    simp only [C, R, Set.mem_ofPred_eq]
    rw [hzero, hone]
  have hcouple := abs_categoricalShiftProduct_event_sub_independent_le q hq0 hq1 h2q C R hevent
  let threshold : Fin 2 → ℕ := ![t₀, t₁]
  have hR : R = {σ | ∀ j, threshold j ≤
      (Finset.univ.filter fun i ↦ j ∈ σ i).card} := by
    ext σ
    simp only [R, threshold, Set.mem_ofPred_eq]
    rw [Fin.forall_fin_two]
    rfl
  have hind := independentShiftProduct_all_heavy_factor q threshold
  rw [hR] at hcouple
  rw [hind] at hcouple
  rw [hpair]
  simp only [threshold, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two] at hcouple
  calc
    _ ≤ 2 * ∑ i, (2 : ℝ) * (2 - 1 : ℕ) * q i ^ 2 := hcouple
    _ = 4 * ∑ i, q i ^ 2 := by
      rw [Finset.mul_sum]
      rw [show 4 * ∑ i, q i ^ 2 = ∑ i, 4 * q i ^ 2 by rw [Finset.mul_sum]]
      apply Fintype.sum_congr
      intro i
      ring

end NormalNumbers.ErdosBorweinPairShift
