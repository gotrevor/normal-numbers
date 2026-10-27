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
open NormalNumbers.ErdosBorweinEndpoint
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

/-- Finite second moment centered at an arbitrary positive comparison value.  Unlike
`card_filter_eq_zero_div_le_secondMoment`, this does not require the comparison value to be the
empirical mean.  This is the convenient form when a sieve supplies termwise approximations to a
model mean. -/
theorem card_filter_eq_zero_div_le_centeredSecondMoment
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (Q : ℝ)
    (hS : S.Nonempty) (hQ : 0 < Q) :
    ((((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) / (S.card : ℝ)) ≤
      ((∑ x ∈ S, (f x - Q) ^ 2) / (S.card : ℝ)) / Q ^ 2 := by
  classical
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hzero : (((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) * Q ^ 2 ≤
      ∑ x ∈ S, (f x - Q) ^ 2 := by
    calc
      (((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) * Q ^ 2 =
          ∑ _x ∈ (S.filter fun x ↦ f x = 0), Q ^ 2 := by simp
      _ = ∑ x ∈ (S.filter fun x ↦ f x = 0), (f x - Q) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hfx : f x = 0 := (Finset.mem_filter.mp hx).2
        rw [hfx]
        ring
      _ ≤ ∑ x ∈ S, (f x - Q) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro x hxS hxnot
        positivity
  have hQsq : 0 < Q ^ 2 := sq_pos_of_pos hQ
  rw [le_div_iff₀ hQsq]
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hcard).2 hzero

/-- A theoretical-mean version of finite Chebyshev.  If the empirical first moment is at least
`Q - r` and the empirical second moment is at most `Q² + Q + d`, the zero set has the displayed
upper bound.  Pairwise sieve errors will be collected into `r` and `d` by the caller. -/
theorem card_filter_eq_zero_div_le_of_moments
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ)
    (Q r d : ℝ) (hS : S.Nonempty) (hQ : 0 < Q) (hr : 0 ≤ r)
    (hfirst : Q - r ≤ (∑ x ∈ S, f x) / (S.card : ℝ))
    (hsecond : (∑ x ∈ S, (f x) ^ 2) / (S.card : ℝ) ≤ Q ^ 2 + Q + d) :
    ((((S.filter fun x ↦ f x = 0).card : ℕ) : ℝ) / (S.card : ℝ)) ≤
      (Q + d + 2 * Q * r) / Q ^ 2 := by
  classical
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hcentered :
      (∑ x ∈ S, (f x - Q) ^ 2) / (S.card : ℝ) =
        (∑ x ∈ S, (f x) ^ 2) / (S.card : ℝ) -
          2 * Q * ((∑ x ∈ S, f x) / (S.card : ℝ)) + Q ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcross : (∑ x ∈ S, 2 * f x * Q) = 2 * Q * (∑ x ∈ S, f x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hcross]
    field_simp
  have hcenteredUpper :
      (∑ x ∈ S, (f x - Q) ^ 2) / (S.card : ℝ) ≤ Q + d + 2 * Q * r := by
    rw [hcentered]
    have hQ0 : 0 ≤ Q := hQ.le
    nlinarith
  exact (card_filter_eq_zero_div_le_centeredSecondMoment S f Q hS hQ).trans
    (div_le_div_of_nonneg_right hcenteredUpper (sq_nonneg Q))

/-- Sum diagonal and off-diagonal pair bounds without losing the sharp single copy of the first
moment.  This is the algebraic adapter between pairwise sieve estimates and
`card_filter_eq_zero_div_le_of_moments`. -/
theorem sum_pair_le_sq_add
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (q : ι → ℝ) (p : ι → ι → ℝ)
    (e d : ℝ) (hq0 : ∀ i ∈ I, 0 ≤ q i) (hd : ∀ i ∈ I, p i i ≤ q i + e)
    (hoff : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → p i j ≤ q i * q j + d) :
    (∑ i ∈ I, ∑ j ∈ I, p i j) ≤
      (∑ i ∈ I, q i) ^ 2 + (∑ i ∈ I, q i) +
        (I.card : ℝ) * e + (I.card : ℝ) * (I.card - 1 : ℕ) * d := by
  classical
  have hsplit : (∑ i ∈ I, ∑ j ∈ I, p i j) =
      (∑ i ∈ I, p i i) + ∑ i ∈ I, ∑ j ∈ I.erase i, p i j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_comm, Finset.sum_erase_add _ _ hi]
  have hdiag : (∑ i ∈ I, p i i) ≤ ∑ i ∈ I, (q i + e) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hd i hi
  have hoffsum : (∑ i ∈ I, ∑ j ∈ I.erase i, p i j) ≤
      ∑ i ∈ I, ∑ j ∈ I.erase i, (q i * q j + d) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hoff i hi j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm
  have hoffprod : (∑ i ∈ I, ∑ j ∈ I.erase i, q i * q j) ≤
      ∑ i ∈ I, ∑ j ∈ I, q i * q j := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun j hj hnot ↦ mul_nonneg (hq0 i hi) (hq0 j hj))
  rw [hsplit]
  calc
    (∑ i ∈ I, p i i) + ∑ i ∈ I, ∑ j ∈ I.erase i, p i j ≤
        (∑ i ∈ I, (q i + e)) +
          ∑ i ∈ I, ∑ j ∈ I.erase i, (q i * q j + d) :=
      add_le_add hdiag hoffsum
    _ = (∑ i ∈ I, q i) + (I.card : ℝ) * e +
          (∑ i ∈ I, ∑ j ∈ I.erase i, q i * q j) +
          (I.card : ℝ) * (I.card - 1 : ℕ) * d := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have herr : (∑ i ∈ I, ((I.erase i).card : ℝ) * d) =
          (I.card : ℝ) * (I.card - 1 : ℕ) * d := by
        calc
          (∑ i ∈ I, ((I.erase i).card : ℝ) * d) =
              ∑ _i ∈ I, (((I.card - 1 : ℕ) : ℝ) * d) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.card_erase_of_mem hi]
          _ = (I.card : ℝ) * (I.card - 1 : ℕ) * d := by simp; ring
      rw [herr]
      ring
    _ ≤ (∑ i ∈ I, q i) + (I.card : ℝ) * e +
          (∑ i ∈ I, ∑ j ∈ I, q i * q j) +
          (I.card : ℝ) * (I.card - 1 : ℕ) * d := by
      linarith
    _ = (∑ i ∈ I, q i) ^ 2 + (∑ i ∈ I, q i) +
          (I.card : ℝ) * e + (I.card : ℝ) * (I.card - 1 : ℕ) * d := by
      have hprod : (∑ i ∈ I, ∑ j ∈ I, q i * q j) =
          (∑ i ∈ I, q i) ^ 2 := by
        calc
          (∑ i ∈ I, ∑ j ∈ I, q i * q j) =
              ∑ i ∈ I, q i * (∑ j ∈ I, q j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = (∑ i ∈ I, q i) ^ 2 := by
            rw [← Finset.sum_mul]
            ring
      rw [hprod]
      ring

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

/-- Bernoulli subset mass is invariant under relabeling its finite coordinate space. -/
theorem bernoulliSubsetMass_relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (U : Finset α) (q : α → ℝ) (A : Set (Finset β)) :
    NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (U.map e.toEmbedding) (fun y ↦ q (e.symm y)) A =
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        U q {S | e.finsetCongr S ∈ A} := by
  classical
  unfold NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
  symm
  apply Finset.sum_equiv e.finsetCongr
  · intro S
    simp [Equiv.finsetCongr_apply]
  · intro S hS
    simp only [Set.mem_ofPred_eq]
    by_cases hA : e.finsetCongr S ∈ A
    · rw [if_pos hA, if_pos hA]
      unfold NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetWeight
      apply Finset.prod_equiv e
      · intro x
        simp [Equiv.finsetCongr_apply]
      · intro x hx
        simp
    · rw [if_neg hA, if_neg hA]

/-- The two columns in the independent Bool-indexed pair model have the same cardinality-tail
mass. -/
theorem pairIndependentColumnMass_zero_eq_one {n : ℕ} (q : Fin n → ℝ) (t : ℕ) :
    NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin n × Fin 2)) (fun z ↦ q z.1)
        {S | t ≤ (S ∩ shiftArrayColumn n 2 0).card} =
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin n × Fin 2)) (fun z ↦ q z.1)
        {S | t ≤ (S ∩ shiftArrayColumn n 2 1).card} := by
  classical
  let swap : Equiv.Perm (Fin n × Fin 2) :=
    Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.swap 0 1)
  have h := bernoulliSubsetMass_relabel swap
    (Finset.univ : Finset (Fin n × Fin 2)) (fun z ↦ q z.1)
    {S | t ≤ (S ∩ shiftArrayColumn n 2 1).card}
  have hcard (S : Finset (Fin n × Fin 2)) :
      (Finset.map swap.toEmbedding S ∩ shiftArrayColumn n 2 1).card =
        (S ∩ shiftArrayColumn n 2 0).card := by
    rw [← Finset.card_map (s := S ∩ shiftArrayColumn n 2 0) swap.toEmbedding]
    congr 1
    ext z
    rcases z with ⟨i, k⟩
    fin_cases k <;> simp [swap, shiftArrayColumn]
  have h' :
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
          (Finset.univ : Finset (Fin n × Fin 2)) (fun z ↦ q z.1)
          {S | t ≤ (S ∩ shiftArrayColumn n 2 1).card} =
        NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass Finset.univ
          (fun z ↦ q z.1)
          {S | t ≤ (Finset.map swap.toEmbedding S ∩ shiftArrayColumn n 2 1).card} := by
    simpa [swap, Equiv.finsetCongr_apply] using h
  calc
    _ = NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass Finset.univ
          (fun z ↦ q z.1)
          {S | t ≤ (Finset.map swap.toEmbedding S ∩ shiftArrayColumn n 2 1).card} := by
      congr 1
      ext S
      simp only [Set.mem_ofPred_eq]
      rw [hcard]
    _ = _ := h'.symm

/-- The independent heavy-event probability for one scheduled threshold in the fixed pair
model. -/
noncomputable def pairScheduledColumnMass
    (c A : ℝ) (b N : ℕ) (j : Fin (multiShiftScheduleJ N)) : ℝ :=
  NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
    (Finset.univ : Finset
      (Fin (Fintype.card (primesIoc (collisionCutoff N) (multiShiftCutoffY N))) × Fin 2))
    (fun z ↦ 1 / (((primeIndexEquiv (collisionCutoff N)
      (multiShiftCutoffY N)) z.1 : ℕ) : ℝ))
    {S | multiShiftThreshold c A b N j.val ≤
      (S ∩ shiftArrayColumn
        (Fintype.card (primesIoc (collisionCutoff N) (multiShiftCutoffY N))) 2 1).card}

theorem pairScheduledColumnMass_nonneg (c A : ℝ) (b N : ℕ)
    (j : Fin (multiShiftScheduleJ N)) : 0 ≤ pairScheduledColumnMass c A b N j := by
  classical
  rw [pairScheduledColumnMass]
  apply NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_nonneg
  · intro z hz
    positivity
  · intro z hz
    have hp : Nat.Prime ((primeIndexEquiv (collisionCutoff N)
        (multiShiftCutoffY N)) z.1 : ℕ) :=
      (Finset.mem_filter.mp ((primeIndexEquiv (collisionCutoff N)
        (multiShiftCutoffY N)) z.1).property).2
    exact (div_le_one (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_le)

theorem pairScheduledColumnMass_le_one (c A : ℝ) (b N : ℕ)
    (j : Fin (multiShiftScheduleJ N)) : pairScheduledColumnMass c A b N j ≤ 1 := by
  classical
  rw [pairScheduledColumnMass]
  apply NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_le_one
  · intro z hz
    positivity
  · intro z hz
    have hp : Nat.Prime ((primeIndexEquiv (collisionCutoff N)
        (multiShiftCutoffY N)) z.1 : ℕ) :=
      (Finset.mem_filter.mp ((primeIndexEquiv (collisionCutoff N)
        (multiShiftCutoffY N)) z.1).property).2
    exact (div_le_one (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_le)

/-- The scheduled moderate-deviation lower bound in one column of the fixed two-column
independent model.  This is the pair-model analogue of
`eventually_multiShiftColumnMass_ge_deviation`; the threshold still ranges over the full scheduled
set of shifts, but the probability space has only the two coordinates needed by the pair sieve. -/
theorem eventually_pairColumnMass_ge_deviation
    (c A eps eta : ℝ) (hc : c < 1) (hA : 0 ≤ A) (b : ℕ) (hb : 2 ≤ b)
    (heps : 0 < eps) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 100)
    (hetaEps : 80 * eta ≤ eps) (hlargeA : 6 ≤ eta ^ 2 * A ^ 2)
    (habsorbA : 4 * Real.log 2 ≤ eps * A ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ j : Fin (multiShiftScheduleJ N),
      Real.exp (-((1 + eps) * multiShiftDeviation c A b N j.val ^ 2 /
          (2 * multiShiftPrimeMean N))) ≤ pairScheduledColumnMass c A b N j := by
  classical
  have hLTop : Filter.Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_multiShiftModerateSideConditions c A hc hA b hb eta heta0,
      eventually_multiShiftCutoffY_bounds, eventually_multiShiftLogBlock_bounds,
      hLTop.eventually_ge_atTop 2] with N hsides hcut hblock hL
  intro j
  let P : ℕ := collisionCutoff N
  let y : ℕ := multiShiftCutoffY N
  let mean : ℝ := multiShiftPrimeMean N
  let x : ℝ := multiShiftDeviation c A b N j.val
  have hside := hsides j
  change 0 < mean ∧ 0 < x ∧ (P : ℝ)⁻¹ ≤ eta * mean ∧
    (1 + 4 * eta) * x / mean ≤ eta ∧ A ^ 2 * mean ≤ x ^ 2 at hside
  have hP2 : 2 ≤ P := by simpa only [P] using hblock.1
  have hPy : P ≤ y := by simpa only [P, y] using hcut.1
  have hmoderate := multiShiftColumnMass_ge_moderate_of_baseline
    (P := P) (y := y) (J := 2) (1 : Fin 2) hP2 hPy
    heps heta0 heta1 hetaEps hside.1 hside.2.1 hside.2.2.1 hside.2.2.2.1
    hside.2.2.2.2 hlargeA habsorbA
  calc
    Real.exp (-((1 + eps) * multiShiftDeviation c A b N j.val ^ 2 /
        (2 * multiShiftPrimeMean N))) ≤
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin (Fintype.card (primesIoc P y)) × Fin 2))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | mean + x ≤
          ((S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) 2 1).card : ℝ)} := by
      simpa only [P, y, mean, x, multiShiftPrimeMean] using hmoderate
    _ ≤ NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin (Fintype.card (primesIoc P y)) × Fin 2))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | multiShiftThreshold c A b N j.val ≤
          (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) 2 1).card} := by
      apply NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_mono
      · intro S hS
        have hL0 : 0 < Real.log (Real.log (N : ℝ)) := by linarith
        have hlogL0 : 0 ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
          Real.log_nonneg (by linarith)
        have hshift0 : 0 ≤
            (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) := by
          have : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
          positivity
        have harg0 : 0 ≤ multiShiftPrimeMean N + multiShiftSubpowerPenalty c N +
            A * Real.sqrt (multiShiftPrimeMean N) +
            (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) +
            8 * Real.log (Real.log (Real.log N)) := by
          have hpenalty0 : 0 ≤ multiShiftSubpowerPenalty c N := by
            simp only [multiShiftSubpowerPenalty]
            positivity
          have hbaseline0 : 0 ≤ A * Real.sqrt (multiShiftPrimeMean N) :=
            mul_nonneg hA (Real.sqrt_nonneg _)
          have hmeanN : 0 < multiShiftPrimeMean N := by simpa only [mean] using hside.1
          nlinarith
        have hceil := Nat.ceil_lt_add_one harg0
        have hthreshold : (multiShiftThreshold c A b N j.val : ℝ) < mean + x := by
          dsimp only [mean, x, multiShiftDeviation]
          rw [multiShiftThreshold]
          exact hceil.trans_eq (by ring)
        change multiShiftThreshold c A b N j.val ≤
          (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) 2 1).card
        have hreal : (multiShiftThreshold c A b N j.val : ℝ) ≤
            ((S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) 2 1).card : ℝ) :=
          hthreshold.le.trans hS
        exact_mod_cast hreal
      · intro z hz
        positivity
      · intro z hz
        have hp : Nat.Prime ((primeIndexEquiv P y) z.1 : ℕ) :=
          (Finset.mem_filter.mp ((primeIndexEquiv P y) z.1).property).2
        exact (div_le_one (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_le)
    _ = pairScheduledColumnMass c A b N j := by rfl

/-- The sum of the active fixed-pair column masses diverges. -/
theorem tendsto_pairActiveColumnMassSum
    (c A eps eta alpha : ℝ) (hc : c < 1) (hA : 0 ≤ A)
    (heps : 0 < eps) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 100)
    (hetaEps : 80 * eta ≤ eps) (hlargeA : 6 ≤ eta ^ 2 * A ^ 2)
    (habsorbA : 4 * Real.log 2 ≤ eps * A ^ 2)
    (halpha : (1 + eps) * max c 0 / 2 < alpha) (halphaHalf : alpha < 1 / 2)
    (b : ℕ) (hb : 2 ≤ b) (j₀ : ℕ) :
    Filter.Tendsto (fun N : ℕ ↦
      ∑ j : Fin (multiShiftScheduleJ N) with j₀ ≤ j.val + 1,
        pairScheduledColumnMass c A b N j) Filter.atTop Filter.atTop := by
  have hlower := tendsto_multiShiftActiveExpColumnSum
    c A eps alpha hA heps.le halpha halphaHalf b hb j₀
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hlower
  filter_upwards [eventually_pairColumnMass_ge_deviation
      c A eps eta hc hA b hb heps heta0 heta1 hetaEps hlargeA habsorbA] with N hcolumn
  apply Finset.sum_le_sum
  intro j hj
  exact hcolumn j

/-! ### Scheduled pair-sieve errors -/

/-- The fixed-dimensional exponential sieve error still vanishes after multiplying by the square
of the number of scheduled shifts.  The extra decay comes from the schedule's depth inequality,
not merely from `tendsto_multiShiftSieveExpError`. -/
theorem tendsto_pairSieveExpError_sq (C : ℝ) (hC : 0 < C) :
    Filter.Tendsto (fun N : ℕ ↦
      (multiShiftScheduleJ N : ℝ) ^ 2 *
        Real.exp (-(Real.log N / Real.log (multiShiftCutoffY N) / C)))
      Filter.atTop (nhds 0) := by
  have hmajor : Filter.Tendsto
      (fun N : ℕ ↦ 1 / (multiShiftScheduleJ N : ℝ)) Filter.atTop (nhds 0) := by
    have hraw := tendsto_multiShiftScheduleJ.inv_tendsto_atTop
    apply hraw.congr'
    exact Filter.Eventually.of_forall fun N ↦ by simp only [one_div, Pi.inv_apply]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ by positivity) ?_ hmajor
  filter_upwards [eventually_multiShiftSieveDepth (2 * C) (by positivity),
      tendsto_multiShiftScheduleJ.eventually_ge_atTop 2] with N hdepth hJ
  let J : ℝ := multiShiftScheduleJ N
  let R : ℝ := Real.log N / Real.log (multiShiftCutoffY N)
  have hJ0 : 0 < J := by dsimp only [J]; linarith
  have hlogJ0 : 0 ≤ Real.log J := Real.log_nonneg (by linarith)
  have hlogJplus0 : 0 ≤ Real.log (J + 2) := Real.log_nonneg (by linarith)
  have hlogMono : Real.log J ≤ Real.log (J + 2) :=
    Real.log_le_log hJ0 (by linarith)
  have hratio : 2 * J * Real.log (J + 2) ≤ R / C := by
    rw [le_div_iff₀ hC]
    calc
      (2 * J * Real.log (J + 2)) * C =
          (2 * C) * J * Real.log (J + 2) := by ring
      _ ≤ R := by simpa only [J, R] using hdepth
  have hthree : 3 * Real.log J ≤ 2 * J * Real.log (J + 2) := by
    calc
      3 * Real.log J ≤ 3 * Real.log (J + 2) :=
        mul_le_mul_of_nonneg_left hlogMono (by norm_num)
      _ ≤ 2 * J * Real.log (J + 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogJplus0
  have hexp : Real.exp (-(R / C)) ≤ Real.exp (-(3 * Real.log J)) :=
    Real.exp_le_exp.mpr (neg_le_neg (hthree.trans hratio))
  calc
    (multiShiftScheduleJ N : ℝ) ^ 2 *
        Real.exp (-(Real.log N / Real.log (multiShiftCutoffY N) / C)) =
        J ^ 2 * Real.exp (-(R / C)) := by rfl
    _ ≤ J ^ 2 * Real.exp (-(3 * Real.log J)) :=
      mul_le_mul_of_nonneg_left hexp (sq_nonneg J)
    _ = 1 / J := by
      rw [Real.exp_neg, show 3 * Real.log J = Real.log (J ^ 3) by
        rw [Real.log_pow]
        norm_num, Real.exp_log (pow_pos hJ0 3)]
      field_simp
    _ = 1 / (multiShiftScheduleJ N : ℝ) := by rfl

/-- The fixed power remainder `(log N)^2 / sqrt N` vanishes after multiplication by the square of
the number of scheduled shifts. -/
theorem tendsto_pairSievePowerError_sq :
    Filter.Tendsto (fun N : ℕ ↦
      (multiShiftScheduleJ N : ℝ) ^ 2 * Real.log N ^ 2 / Real.sqrt N)
      Filter.atTop (nhds 0) := by
  have htTop : Filter.Tendsto (fun N : ℕ ↦ Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ by positivity) ?_
    tendsto_multiShiftSievePowerError
  filter_upwards [tendsto_multiShiftScheduleJ.eventually_ge_atTop 4,
      eventually_multiShiftScheduleJ_le_log_log,
      htTop.eventually_ge_atTop 1] with N hJ4 hJL ht
  let J : ℝ := multiShiftScheduleJ N
  let t : ℝ := Real.log N
  have ht0 : 0 < t := by dsimp only [t]; linarith
  have hlogt : Real.log t ≤ t :=
    (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hJt : J ≤ t := by
    change (multiShiftScheduleJ N : ℝ) ≤ Real.log N
    exact hJL.trans (by simpa only [t] using hlogt)
  have hJ4nat : 4 ≤ multiShiftScheduleJ N := by exact_mod_cast hJ4
  have hnum : J ^ 2 * t ^ 2 ≤ t ^ multiShiftScheduleJ N := by
    calc
      J ^ 2 * t ^ 2 ≤ t ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hJt 2) (sq_nonneg t)
      _ = t ^ 4 := by ring
      _ ≤ t ^ multiShiftScheduleJ N := pow_le_pow_right₀ ht hJ4nat
  change J ^ 2 * t ^ 2 / Real.sqrt N ≤ t ^ multiShiftScheduleJ N / Real.sqrt N
  exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)

/-- The one-pair total-variation loss from the frozen sieve hypothesis. -/
noncomputable def pairShiftSieveError (C : ℝ) (N : ℕ) : ℝ :=
  C * (Real.exp (-(Real.log N / Real.log (multiShiftCutoffY N) / C)) +
    Real.log N ^ 2 / Real.sqrt N)

/-- All ordered pair sieve losses vanish after summing over the scheduled square. -/
theorem tendsto_pairShiftSieveError_sq (C : ℝ) (hC : 0 < C) :
    Filter.Tendsto (fun N : ℕ ↦
      (multiShiftScheduleJ N : ℝ) ^ 2 * pairShiftSieveError C N)
      Filter.atTop (nhds 0) := by
  have h := ((tendsto_pairSieveExpError_sq C hC).add
    tendsto_pairSievePowerError_sq).const_mul C
  have hzero : C * (0 + 0) = 0 := by ring
  rw [hzero] at h
  convert h using 1
  ext N
  simp only [pairShiftSieveError]
  ring

/-- The accumulated marginal sieve loss vanishes. -/
theorem tendsto_pairShiftFirstError (C : ℝ) (hC : 0 < C) :
    Filter.Tendsto (fun N : ℕ ↦
      (multiShiftScheduleJ N : ℝ) * pairShiftSieveError C N)
      Filter.atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_pairShiftSieveError_sq C hC)
  · exact Filter.Eventually.of_forall fun N ↦ by
      apply mul_nonneg (by positivity)
      rw [pairShiftSieveError]
      exact mul_nonneg hC.le (by positivity)
  · filter_upwards [tendsto_multiShiftScheduleJ.eventually_ge_atTop 1] with N hJ
    have herr0 : 0 ≤ pairShiftSieveError C N := by
      apply mul_nonneg hC.le
      positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hJ) herr0]

/-- The pair-model collision budget vanishes even with a square (rather than `J(J-1)`) of the
scheduled shift count. -/
theorem tendsto_pairShiftCollisionError_sq :
    Filter.Tendsto (fun N : ℕ ↦
      4 * (multiShiftScheduleJ N : ℝ) ^ 2 * (collisionCutoff N : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
  have hmajor := tendsto_multiShiftCollisionError.const_mul (4 : ℝ)
  have hzero : (4 : ℝ) * 0 = 0 := by ring
  rw [hzero] at hmajor
  refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ by positivity) ?_ hmajor
  filter_upwards [tendsto_multiShiftScheduleJ.eventually_ge_atTop 2] with N hJ
  let J : ℝ := multiShiftScheduleJ N
  let K : ℝ := (multiShiftScheduleJ N - 1 : ℕ)
  have hJ0 : 0 ≤ J := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hJK : J ≤ 2 * K := by
    have hJnat : 1 ≤ multiShiftScheduleJ N := by
      exact_mod_cast (show (1 : ℝ) ≤ (multiShiftScheduleJ N : ℝ) by linarith)
    dsimp only [K]
    rw [Nat.cast_sub hJnat]
    dsimp only [J]
    norm_num
    linarith
  have hdiff : 0 ≤
      4 * (2 * J * K * (collisionCutoff N : ℝ)⁻¹) -
        4 * J ^ 2 * (collisionCutoff N : ℝ)⁻¹ := by
    rw [show 4 * (2 * J * K * (collisionCutoff N : ℝ)⁻¹) -
        4 * J ^ 2 * (collisionCutoff N : ℝ)⁻¹ =
      4 * J * (2 * K - J) * (collisionCutoff N : ℝ)⁻¹ by ring]
    positivity
  change 4 * J ^ 2 * (collisionCutoff N : ℝ)⁻¹ ≤
    4 * (2 * J * K * (collisionCutoff N : ℝ)⁻¹)
  linarith

/-- The complete aggregate second-moment error: one sieve loss per ordered pair and the
categorical-to-independent collision loss on the off-diagonal. -/
noncomputable def pairShiftSecondError (C : ℝ) (N : ℕ) : ℝ :=
  (multiShiftScheduleJ N : ℝ) ^ 2 * pairShiftSieveError C N +
    4 * (multiShiftScheduleJ N : ℝ) ^ 2 * (collisionCutoff N : ℝ)⁻¹

theorem tendsto_pairShiftSecondError (C : ℝ) (hC : 0 < C) :
    Filter.Tendsto (pairShiftSecondError C) Filter.atTop (nhds 0) := by
  have h := (tendsto_pairShiftSieveError_sq C hC).add
    tendsto_pairShiftCollisionError_sq
  have hzero : (0 : ℝ) + 0 = 0 := by ring
  rw [hzero] at h
  convert h using 1
  ext N
  simp only [pairShiftSecondError]

/-- The algebraic final step in theoretical-mean Chebyshev: a diverging mean and vanishing first-
and second-moment errors force the displayed upper bound to zero. -/
theorem tendsto_pairChebyshevBound
    (Q r d : ℕ → ℝ) (hQ : Filter.Tendsto Q Filter.atTop Filter.atTop)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hd : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N ↦ (Q N + d N + 2 * Q N * r N) / Q N ^ 2)
      Filter.atTop (nhds 0) := by
  have hInv : Filter.Tendsto (fun N ↦ (Q N)⁻¹) Filter.atTop (nhds 0) :=
    hQ.inv_tendsto_atTop
  have hlim : Filter.Tendsto
      (fun N ↦ (Q N)⁻¹ + d N * (Q N)⁻¹ ^ 2 + 2 * r N * (Q N)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := hInv.add (hd.mul (hInv.pow 2)) |>.add ((hr.mul hInv).const_mul 2)
    have hzero : (0 : ℝ) + 0 * 0 ^ 2 + 2 * (0 * 0) = 0 := by ring
    rw [hzero] at h
    convert h using 1
    ext N
    ring
  apply hlim.congr'
  filter_upwards [hQ.eventually_gt_atTop 0] with N hQN
  field_simp

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

/-- Concrete reciprocal-cutoff form of the Bool pair coupling bound. -/
theorem abs_pairBoolCountMass_sub_independent_le_inv {P y : ℕ}
    (hP : 2 ≤ P) (hPy : P ≤ y) (t₀ t₁ : ℕ) :
    |pairBoolCountMass
          (fun i : Fin (Fintype.card (primesIoc P y)) ↦
            1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) t₀ t₁ -
        (NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
          (Finset.univ : Finset
            (Fin (Fintype.card (primesIoc P y)) × Fin 2))
          (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
          {S | t₀ ≤ (S ∩ shiftArrayColumn
            (Fintype.card (primesIoc P y)) 2 0).card}) *
        (NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
          (Finset.univ : Finset
            (Fin (Fintype.card (primesIoc P y)) × Fin 2))
          (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
          {S | t₁ ≤ (S ∩ shiftArrayColumn
            (Fintype.card (primesIoc P y)) 2 1).card})| ≤
      4 * (P : ℝ)⁻¹ := by
  let q : Fin (Fintype.card (primesIoc P y)) → ℝ := fun i ↦
    1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)
  have hprime : ∀ i, Nat.Prime ((primeIndexEquiv P y) i : ℕ) := by
    intro i
    exact (Finset.mem_filter.mp ((primeIndexEquiv P y) i).property).2
  have hlarge : ∀ i, P < ((primeIndexEquiv P y) i : ℕ) := by
    intro i
    exact Finset.mem_Ioc.mp
      (Finset.mem_filter.mp ((primeIndexEquiv P y) i).property).1 |>.1
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    dsimp only [q]
    positivity
  have hq1 : ∀ i, q i ≤ 1 := by
    intro i
    dsimp only [q]
    have hpR : (0 : ℝ) < (((primeIndexEquiv P y) i : ℕ) : ℝ) := by
      exact_mod_cast (hprime i).pos
    apply (div_le_one hpR).2
    exact_mod_cast (hprime i).one_le
  have h2q : ∀ i, 2 * q i ≤ 1 := by
    intro i
    dsimp only [q]
    rw [mul_one_div]
    have hpR : (0 : ℝ) < (((primeIndexEquiv P y) i : ℕ) : ℝ) := by
      exact_mod_cast (hprime i).pos
    apply (div_le_one hpR).2
    exact_mod_cast (show 2 ≤ ((primeIndexEquiv P y) i : ℕ) by
      exact hP.trans (hlarge i).le)
  have hcouple := abs_pairBoolCountMass_sub_independent_le q hq0 hq1 h2q t₀ t₁
  change |_ - _ * _| ≤ 4 * (P : ℝ)⁻¹
  exact hcouple.trans
    (mul_le_mul_of_nonneg_left (sum_primeIndex_inv_sq_le (by omega) hPy) (by norm_num))

end NormalNumbers.ErdosBorweinPairShift
