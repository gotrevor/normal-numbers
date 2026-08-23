/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDensity

/-!
# W3 — the transfer-operator recursion (route step 2, part 1)

For measurable `A ⊆ (0,1)` set `B_k := (0,1) ∩ T^{-k}A` and
`G_k(t) := ∫_{B_k} h_t` (`h_t = tailDensity t`).  This file proves the
two facts that feed `cylinder_mixing`:

* `volume_inter_preimage_horizon` — the conditional volume at horizon
  `|w| + k` is `G_k(t(w))·|I_w|` (splice `volume_inter_preimage_aux`
  through the orbit).
* `horizonIntegral_succ` — **the recursion** `G_{k+1} = stepOp G_k` on
  `[0,1]`: partition `B_{k+1}` over the first digit and apply the
  single-branch substitution kernel to each piece.

Together with `stepOp_lipschitz` (`CFContraction`), `G_k` is
`(9/10)ᵏ·Lip(G_0)`-Lipschitz; the remaining input for `cylinder_mixing`
is the mean pin `∫ G_k dγ = γ(A)` (Gauss invariance).
-/

namespace NormalNumbers

open MeasureTheory

/-- `B_k = (0,1) ∩ T^{-k}(A)`: the horizon set. -/
def horizonSet (A : Set ℝ) (k : ℕ) : Set ℝ :=
  Set.Ioo 0 1 ∩ (gaussMap^[k]) ⁻¹' A

lemma measurableSet_horizonSet {A : Set ℝ} (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet (horizonSet A k) :=
  measurableSet_Ioo.inter ((measurable_gaussMap.iterate k) hA)

lemma horizonSet_subset (A : Set ℝ) (k : ℕ) :
    horizonSet A k ⊆ Set.Ioo (0 : ℝ) 1 :=
  Set.inter_subset_left

/-- `G_k(t) = ∫_{B_k} h_t`: the conditional mass of the horizon set. -/
noncomputable def horizonIntegral (A : Set ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ y in horizonSet A k, tailDensity t y

/-- `h_t` is integrable on `(0,1)` (continuous on the compact `[0,1]`). -/
lemma integrableOn_tailDensity {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (tailDensity t) (Set.Ioo (0 : ℝ) 1) volume := by
  have hcont : ContinuousOn (tailDensity t) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact ((continuous_const.add
        (continuous_const.mul continuous_id)).pow 2).continuousOn
    · intro y hy
      have hy0 := hy.1
      have : (0 : ℝ) < 1 + t * y := by nlinarith
      positivity
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- **Conditional volume at horizon `|w| + k`**:
`|I_w ∩ T^{-(|w|+k)}A| = G_k(t(w))·|I_w|`. -/
theorem volume_inter_preimage_horizon (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a)
    (k : ℕ) (A : Set ℝ) (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    volume (cfCylinder w ∩ (gaussMap^[w.length + k]) ⁻¹' A) =
      ENNReal.ofReal (horizonIntegral A k (tParam w)) *
        volume (cfCylinder w) := by
  have hae : (cfCylinder w ∩ (gaussMap^[w.length + k]) ⁻¹' A : Set ℝ)
      =ᵐ[volume]
      (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹' horizonSet A k : Set ℝ) := by
    apply ae_eq_of_irrational_iff
    intro x hirr
    have hsplit : ∀ z : ℝ, gaussMap^[w.length + k] z =
        gaussMap^[k] (gaussMap^[w.length] z) := by
      intro z
      rw [Nat.add_comm, Function.iterate_add_apply]
    constructor
    · rintro ⟨hcyl, hTA⟩
      have horb := irrational_orbit x hirr hcyl.1 w.length
      refine ⟨hcyl, ?_⟩
      rw [Set.mem_preimage]
      refine ⟨horb.2, ?_⟩
      rw [Set.mem_preimage, ← hsplit]
      exact hTA
    · rintro ⟨hcyl, hTB⟩
      rw [Set.mem_preimage] at hTB
      refine ⟨hcyl, ?_⟩
      rw [Set.mem_preimage, hsplit]
      exact hTB.2
  rw [measure_congr hae, horizonIntegral]
  exact volume_inter_preimage_aux w hpos (horizonSet A k)
    (measurableSet_horizonSet hA k) (horizonSet_subset A k)

/-- The horizon set at step `k+1` splits over the first digit, up to the
rationals: `B_{k+1}` agrees with `⋃_j (I_{[j+1]} ∩ T⁻¹B_k)` on
irrationals. -/
lemma horizonSet_succ_ae (A : Set ℝ) (k : ℕ) :
    (horizonSet A (k + 1) : Set ℝ) =ᵐ[volume]
      ⋃ j : ℕ, (cfCylinder [j + 1] ∩ gaussMap ⁻¹' horizonSet A k : Set ℝ) := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  constructor
  · rintro ⟨hx, hTA⟩
    rw [Set.mem_preimage] at hTA
    have horb := irrational_orbit x hirr hx 1
    simp only [Function.iterate_one] at horb
    have hd := one_le_cfDigit x hirr hx 0
    refine Set.mem_iUnion.mpr ⟨cfDigit x 0 - 1, ?_⟩
    have hd' : cfDigit x 0 - 1 + 1 = cfDigit x 0 := Nat.succ_pred_eq_of_pos hd
    constructor
    · rw [hd']
      exact mem_cfCylinder_singleton.mpr ⟨hx, rfl⟩
    · rw [Set.mem_preimage]
      refine ⟨horb.2, ?_⟩
      rw [Set.mem_preimage, ← Function.iterate_succ_apply]
      exact hTA
  · intro hx
    obtain ⟨j, hcyl, hTB⟩ := Set.mem_iUnion.mp hx
    rw [Set.mem_preimage] at hTB
    refine ⟨hcyl.1, ?_⟩
    rw [Set.mem_preimage, Function.iterate_succ_apply]
    exact hTB.2

/-- **The transfer-operator recursion** (route step 2, part 1):
`G_{k+1}(t) = (stepOp G_k)(t)` for `t ∈ [0,1]`. -/
theorem horizonIntegral_succ (A : Set ℝ) (hA : MeasurableSet A)
    (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    horizonIntegral A (k + 1) t = stepOp (horizonIntegral A k) t := by
  set B : Set ℝ := horizonSet A k with hB
  have hBmeas : MeasurableSet B := measurableSet_horizonSet hA k
  have hB1 : B ⊆ Set.Ioo (0 : ℝ) 1 := horizonSet_subset A k
  -- the pieces of the first-digit partition
  set s : ℕ → Set ℝ :=
    fun j => (cfCylinder [j + 1] ∩ gaussMap ⁻¹' B : Set ℝ) with hs
  have hsmeas : ∀ j, MeasurableSet (s j) := fun j =>
    (measurableSet_cfCylinder [j + 1]).inter (measurable_gaussMap hBmeas)
  have hsdisj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
    have hi := (mem_cfCylinder_singleton.mp hxi).2
    have hj := (mem_cfCylinder_singleton.mp hxj).2
    exact hij (by omega)
  have hint : IntegrableOn (tailDensity t) (⋃ j, s j) volume := by
    apply (integrableOn_tailDensity ht.1).mono_set
    refine Set.iUnion_subset fun j x hx => ?_
    exact hx.1.1
  -- switch the integral to the partition, then sum piecewise
  rw [horizonIntegral, setIntegral_congr_set (horizonSet_succ_ae A k),
    integral_iUnion hsmeas hsdisj hint, stepOp]
  apply tsum_congr
  intro j
  have hj1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
  have hpiece : ∫ y in s j, tailDensity t y =
      ∫ y in branchMap (j + 1) '' B, tailDensity t y :=
    setIntegral_congr_set (branch_inter_ae (j + 1) hj1 B hB1)
  rw [hpiece, setIntegral_tailDensity_branch (j + 1) hj1 hBmeas hB1 ht]
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [stepWeight, stepPt, horizonIntegral, hcast]
  congr 1
  · congr 1
    ring
  · congr 2
    rw [one_div]

end NormalNumbers
