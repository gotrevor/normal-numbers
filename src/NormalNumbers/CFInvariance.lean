/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDensity

/-!
# W3 — invariance of the Gauss measure (Track B flag B1)

`γ(T⁻¹S) = γ(S)` for the Gauss measure `dγ = dx/((1+x) log 2)`.

Method: split `(0,1) ∩ T⁻¹A` over the first digit (up to the null
rationals), realize each piece as a branch image `y ↦ 1/(b+y)` of `A`
(`branch_inter_ae`), change variables in the Lebesgue-integral sense
(`lintegral_image_eq_lintegral_abs_deriv_mul`), and telescope the branch
densities: `Σ_b 1/((b+y)(b+1+y)) = 1/(1+y)` — the weight identity
`hasSum_stepWeight` already proved for the transfer operator.
-/

namespace NormalNumbers

open MeasureTheory

/-- The density of the Gauss measure, in `ℝ≥0∞` form. -/
noncomputable def gaussDensity (x : ℝ) : ENNReal :=
  ENNReal.ofReal (((1 + x) * Real.log 2)⁻¹)

lemma gaussMeasure_apply {S : Set ℝ} (hS : MeasurableSet S) :
    gaussMeasure S = ∫⁻ x in S ∩ Set.Ioo 0 1, gaussDensity x := by
  rw [gaussMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
  rfl

/-- Change of variables for the Gauss density through one inverse branch:
`∫⁻_{br_b''A} dγ/dx = ∫⁻_A 1/((b+y)(b+1+y) log 2)`. -/
lemma lintegral_gaussDensity_branch (b : ℕ) (hb : 1 ≤ b) {A : Set ℝ}
    (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    ∫⁻ y in branchMap b '' A, gaussDensity y =
      ∫⁻ y in A, ENNReal.ofReal
        ((((b : ℝ) + y) * ((b : ℝ) + 1 + y) * Real.log 2)⁻¹) := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hderiv : ∀ y ∈ A, HasDerivWithinAt (branchMap b)
      (-(((b : ℝ) + y) ^ 2)⁻¹) A y := by
    intro y hy
    have hy0 := (hA1 hy).1
    have hne : (b : ℝ) + y ≠ 0 := by positivity
    have h1 : HasDerivAt (fun z : ℝ => (b : ℝ) + z) 1 y := by
      simpa using (hasDerivAt_id y).const_add (b : ℝ)
    have h2 := h1.inv hne
    have h3 : -(1 : ℝ) / ((b : ℝ) + y) ^ 2 = -(((b : ℝ) + y) ^ 2)⁻¹ := by
      ring
    rw [h3] at h2
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (branchMap b) A := by
    intro y1 h1 y2 h2 heq
    have := inv_injective heq
    linarith [this]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hA hderiv hinj]
  apply setLIntegral_congr_fun hA
  intro y hy
  obtain ⟨hy0, hy1⟩ := hA1 hy
  have hby : (0 : ℝ) < (b : ℝ) + y := by positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  simp only [gaussDensity, branchMap]
  rw [abs_neg, abs_inv,
    abs_of_pos (by positivity : (0 : ℝ) < ((b : ℝ) + y) ^ 2),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : 1 + ((b : ℝ) + y)⁻¹ = ((b : ℝ) + y + 1) / ((b : ℝ) + y) := by
    field_simp
  rw [h1]
  rw [show (b : ℝ) + 1 + y = (b : ℝ) + y + 1 by ring]
  field_simp

/-- First-digit splitting of a preimage, up to the rationals:
`(0,1) ∩ T⁻¹A` agrees with `⋃_j (I_{[j+1]} ∩ T⁻¹A)` on irrationals. -/
lemma inter_preimage_ae_iUnion (A : Set ℝ) :
    (Set.Ioo (0 : ℝ) 1 ∩ gaussMap ⁻¹' A : Set ℝ) =ᵐ[volume]
      ⋃ j : ℕ, (cfCylinder [j + 1] ∩ gaussMap ⁻¹' A : Set ℝ) := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  constructor
  · rintro ⟨hx, hTA⟩
    have hd := one_le_cfDigit x hirr hx 0
    refine Set.mem_iUnion.mpr ⟨cfDigit x 0 - 1, ?_, hTA⟩
    have hd' : cfDigit x 0 - 1 + 1 = cfDigit x 0 := Nat.succ_pred_eq_of_pos hd
    rw [hd']
    exact mem_cfCylinder_singleton.mpr ⟨hx, rfl⟩
  · intro hx
    obtain ⟨j, hcyl, hTA⟩ := Set.mem_iUnion.mp hx
    exact ⟨hcyl.1, hTA⟩

/-- **The branch telescope**: for measurable `A ⊆ (0,1)`,
`∫⁻_{(0,1) ∩ T⁻¹A} dγ/dx = ∫⁻_A dγ/dx`. -/
lemma lintegral_gaussDensity_preimage {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    ∫⁻ y in Set.Ioo (0 : ℝ) 1 ∩ gaussMap ⁻¹' A, gaussDensity y =
      ∫⁻ y in A, gaussDensity y := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set s : ℕ → Set ℝ :=
    fun j => (cfCylinder [j + 1] ∩ gaussMap ⁻¹' A : Set ℝ) with hs
  have hsmeas : ∀ j, MeasurableSet (s j) := fun j =>
    (measurableSet_cfCylinder [j + 1]).inter (measurable_gaussMap hA)
  have hsdisj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
    have hi := (mem_cfCylinder_singleton.mp hxi).2
    have hj := (mem_cfCylinder_singleton.mp hxj).2
    exact hij (by omega)
  rw [setLIntegral_congr (inter_preimage_ae_iUnion A),
    lintegral_iUnion hsmeas hsdisj]
  have hpiece : ∀ j : ℕ, ∫⁻ y in s j, gaussDensity y =
      ∫⁻ y in A, ENNReal.ofReal
        ((((j : ℝ) + 1 + y) * ((j : ℝ) + 2 + y) * Real.log 2)⁻¹) := by
    intro j
    have hj1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
    rw [setLIntegral_congr (branch_inter_ae (j + 1) hj1 A hA1),
      lintegral_gaussDensity_branch (j + 1) hj1 hA hA1]
    apply setLIntegral_congr_fun hA
    intro y _
    congr 2
    push_cast
    ring
  simp only [hpiece]
  rw [← lintegral_tsum (fun j => (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable)]
  apply setLIntegral_congr_fun hA
  intro y hy
  obtain ⟨hy0, hy1⟩ := hA1 hy
  have hsum : HasSum (fun j : ℕ =>
      (((j : ℝ) + 1 + y) * ((j : ℝ) + 2 + y) * Real.log 2)⁻¹)
      (((1 + y) * Real.log 2)⁻¹) := by
    have h := (hasSum_stepWeight hy0.le).mul_right (((1 + y) * Real.log 2)⁻¹)
    rw [one_mul] at h
    have hfun : (fun j : ℕ =>
        (((j : ℝ) + 1 + y) * ((j : ℝ) + 2 + y) * Real.log 2)⁻¹) =
        fun j : ℕ => stepWeight y j * ((1 + y) * Real.log 2)⁻¹ := by
      funext j
      unfold stepWeight
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 + y := by positivity
      have hj2 : (0 : ℝ) < (j : ℝ) + 2 + y := by positivity
      have h1y : (0 : ℝ) < 1 + y := by linarith
      field_simp
    rw [hfun]
    exact h
  show (∑' j : ℕ, ENNReal.ofReal
      ((((j : ℝ) + 1 + y) * ((j : ℝ) + 2 + y) * Real.log 2)⁻¹)) =
    gaussDensity y
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum.summable,
    hsum.tsum_eq]
  rfl

/-- **Gauss invariance on sets**: `γ(T⁻¹S) = γ(S)` for every measurable
`S` (Gauss, 1812). -/
theorem gaussMeasure_preimage {S : Set ℝ} (hS : MeasurableSet S) :
    gaussMeasure (gaussMap ⁻¹' S) = gaussMeasure S := by
  rw [gaussMeasure_apply (measurable_gaussMap hS), gaussMeasure_apply hS]
  have hae : (gaussMap ⁻¹' S ∩ Set.Ioo 0 1 : Set ℝ) =ᵐ[volume]
      (Set.Ioo (0 : ℝ) 1 ∩ gaussMap ⁻¹' (S ∩ Set.Ioo 0 1) : Set ℝ) := by
    apply ae_eq_of_irrational_iff
    intro x hirr
    constructor
    · rintro ⟨hTS, hx⟩
      have horb := irrational_orbit x hirr hx 1
      simp only [Function.iterate_one] at horb
      exact ⟨hx, hTS, horb.2⟩
    · rintro ⟨hx, hTS, -⟩
      exact ⟨hTS, hx⟩
  rw [setLIntegral_congr hae,
    lintegral_gaussDensity_preimage (hS.inter measurableSet_Ioo)
      Set.inter_subset_right]

end NormalNumbers
