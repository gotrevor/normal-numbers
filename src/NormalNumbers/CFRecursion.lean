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

/-! ## Lipschitz control of `G_k` -/

/-- `t ↦ h_t(y)` is `2`-Lipschitz on `[0,1]`, uniformly in `y ∈ [0,1]`. -/
lemma tailDensity_lipschitz {t t' y : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ht' : t' ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailDensity t y - tailDensity t' y| ≤ 2 * |t - t'| := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨ht0', ht1'⟩ := ht'
  obtain ⟨hy0, hy1⟩ := hy
  have hv : (1 : ℝ) ≤ 1 + t * y := by nlinarith
  have hu : (1 : ℝ) ≤ 1 + t' * y := by nlinarith
  have hv2 : 1 + t * y ≤ 2 := by nlinarith
  have hu2 : 1 + t' * y ≤ 2 := by nlinarith
  have key : tailDensity t y - tailDensity t' y =
      (t - t') * ((1 + t * y) * (1 - y) - (1 + t) * (1 + t' * y) * y) /
        ((1 + t * y) ^ 2 * (1 + t' * y) ^ 2) := by
    unfold tailDensity
    field_simp
    ring
  rw [key, abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + t * y) ^ 2 * (1 + t' * y) ^ 2),
    div_le_iff₀ (by positivity)]
  have hM : |(1 + t * y) * (1 - y) - (1 + t) * (1 + t' * y) * y| ≤
      2 * ((1 + t * y) ^ 2 * (1 + t' * y) ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (t * y), sq_nonneg (t' * y),
      sq_nonneg (1 + t * y), sq_nonneg (1 + t' * y),
      mul_nonneg hy0 ht0, mul_nonneg hy0 ht0']
  calc |t - t'| * |(1 + t * y) * (1 - y) - (1 + t) * (1 + t' * y) * y|
      ≤ |t - t'| * (2 * ((1 + t * y) ^ 2 * (1 + t' * y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hM (abs_nonneg _)
    _ = 2 * |t - t'| * ((1 + t * y) ^ 2 * (1 + t' * y) ^ 2) := by ring

/-- `G_0` is `2·|A|`-Lipschitz on `[0,1]`. -/
lemma horizonIntegral_zero_lipschitz {A : Set ℝ} (_hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |horizonIntegral A 0 t - horizonIntegral A 0 t'| ≤
      2 * (volume A).toReal * |t - t'| := by
  have hB0 : horizonSet A 0 = A := by
    rw [horizonSet, Function.iterate_zero, Set.preimage_id,
      Set.inter_eq_self_of_subset_right hA1]
  have hAfin : volume A < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hA1) ?_
    simp [Real.volume_Ioo]
  have hint : IntegrableOn (tailDensity t) A volume :=
    (integrableOn_tailDensity ht.1).mono_set hA1
  have hint' : IntegrableOn (tailDensity t') A volume :=
    (integrableOn_tailDensity ht'.1).mono_set hA1
  rw [horizonIntegral, horizonIntegral, hB0, ← integral_sub hint hint']
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := A) (C := 2 * |t - t'|) hAfin (fun y hy => by
      rw [Real.norm_eq_abs]
      exact tailDensity_lipschitz ht ht'
        (Set.Icc_subset_Icc (le_refl _) (le_refl _)
          (Set.Ioo_subset_Icc_self (hA1 hy))))
  rw [Real.norm_eq_abs] at h
  calc |∫ y in A, (tailDensity t y - tailDensity t' y)| ≤
      2 * |t - t'| * volume.real A := h
    _ = 2 * (volume A).toReal * |t - t'| := by
        rw [measureReal_def]; ring

/-- **Geometric Lipschitz decay**: `G_k` is `(9/10)ᵏ·2|A|`-Lipschitz on
`[0,1]` (iterate `stepOp_lipschitz` through the recursion). -/
theorem horizonIntegral_lipschitz {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |horizonIntegral A k t - horizonIntegral A k t'| ≤
      (9 / 10) ^ k * (2 * (volume A).toReal) * |t - t'| := by
  induction k generalizing t t' with
  | zero =>
      simpa using horizonIntegral_zero_lipschitz hA hA1 ht ht'
  | succ m ih =>
      rw [horizonIntegral_succ A hA m ht, horizonIntegral_succ A hA m ht']
      have hL : (0 : ℝ) ≤ (9 / 10) ^ m * (2 * (volume A).toReal) := by
        have := ENNReal.toReal_nonneg (a := volume A)
        positivity
      have h := stepOp_lipschitz hL (fun x hx y hy => ih hx hy) ht ht'
      calc |stepOp (horizonIntegral A m) t - stepOp (horizonIntegral A m) t'| ≤
          9 / 10 * ((9 / 10) ^ m * (2 * (volume A).toReal)) * |t - t'| := h
        _ = (9 / 10) ^ (m + 1) * (2 * (volume A).toReal) * |t - t'| := by
            rw [pow_succ]; ring

end NormalNumbers
