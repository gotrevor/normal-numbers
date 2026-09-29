/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CS: the cluster set's Gauss mass — the measure half of `ClassFreqBound`

S7-CL factors the predictor through the FIXED sets `clusterSet t w κ = t.mob ⁻¹' (κ-thickening of
`I_w ∩ (0,1)`) ∩ (0,1)`, one per net centre `t`.  `ClassFreqBound` asks that the orbit hit those
sets no more often than their mass; this module supplies the mass.

* `cthickening_subset_Icc` — thickening an interval-contained set stays in the interval grown by
  `κ` on each side (`Real.closedBall_eq_Icc` + `cthickening_closedBall`).
* `gaussMeasure_clusterSet_le` — `γ(clusterSet t w κ) ≤ pullLip t · (2γ(I_w) + 2κ/log 2)`,
  unconditionally, using S7-PM's `MapState` pullback bound and `cfCylinder_subset_Icc_length`.
* `gaussMeasure_clusterSet_le_width` — with S7-Box's `denRatio` band this reads
  `≤ (K/η)·(2γ(I_w) + 2κ/log 2)` on states of width `≥ η`: exactly the `Cp·γ/η` shape that S7-MD
  consumes, plus the net-precision error `κ`, which is chosen after `η`.
-/
import NormalNumbers.VandeheyS7PullMap
import NormalNumbers.VandeheyS7Class

namespace NormalNumbers.VandeheyS7

open Set Filter Metric MeasureTheory NormalNumbers

/-- Thickening a set inside `Icc a c` keeps it inside `Icc (a−κ) (c+κ)`. -/
theorem cthickening_subset_Icc {a c κ : ℝ} (hac : a ≤ c) (hκ : 0 ≤ κ) {S : Set ℝ}
    (hS : S ⊆ Set.Icc a c) :
    Metric.cthickening κ S ⊆ Set.Icc (a - κ) (c + κ) := by
  have hball : Set.Icc a c = Metric.closedBall ((a + c) / 2) ((c - a) / 2) := by
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> ring
  have hr : (0:ℝ) ≤ (c - a) / 2 := by linarith
  calc Metric.cthickening κ S ⊆ Metric.cthickening κ (Set.Icc a c) :=
        Metric.cthickening_subset_of_subset κ hS
    _ = Metric.closedBall ((a + c) / 2) (κ + (c - a) / 2) := by
        rw [hball, cthickening_closedBall hκ hr]
    _ = Set.Icc (a - κ) (c + κ) := by
        rw [Real.closedBall_eq_Icc]
        congr 1 <;> ring

namespace MapState

/-- **S7-CS.**  The cluster set's Gauss mass is at most the pullback constant times the target's,
plus the thickening error. -/
theorem gaussMeasure_clusterSet_le (t : MapState) (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) {κ : ℝ} (hκ : 0 ≤ κ) :
    (gaussMeasure (clusterSet t w κ)).toReal
      ≤ t.pullLip * (2 * (gaussMeasure (cfCylinder w)).toReal + 2 * κ / Real.log 2) := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLip : 0 < t.pullLip := t.pullLip_pos
  obtain ⟨a, c, hsub, hlen⟩ := cfCylinder_subset_Icc_length w hw hpos
  have hvolcyl : (0:ℝ) ≤ (volume (cfCylinder w)).toReal := by positivity
  have hac : a ≤ c := by linarith [hlen, hvolcyl]
  -- the thickened target sits in a short interval
  have hth : Metric.cthickening κ (cfCylinder w ∩ Set.Ioo (0:ℝ) 1)
      ⊆ Set.Icc (a - κ) (c + κ) :=
    cthickening_subset_Icc hac hκ (le_trans Set.inter_subset_left hsub)
  have hvolth : volume (Metric.cthickening κ (cfCylinder w ∩ Set.Ioo (0:ℝ) 1))
      ≤ ENNReal.ofReal ((volume (cfCylinder w)).toReal + 2 * κ) := by
    refine le_trans (measure_mono hth) ?_
    rw [Real.volume_Icc]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [hlen]
  -- pull it back
  have hpull := t.volume_preimage_le (Metric.cthickening κ (cfCylinder w ∩ Set.Ioo (0:ℝ) 1))
  have hmeasCl : MeasurableSet (clusterSet t w κ) := by
    refine MeasurableSet.inter ?_ measurableSet_Ioo
    exact (Metric.isClosed_cthickening.measurableSet).preimage t.measurable_mob
  have hγ : gaussMeasure (clusterSet t w κ)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal t.pullLip
          * ENNReal.ofReal ((volume (cfCylinder w)).toReal + 2 * κ)) := by
    refine le_trans (gaussMeasure_le_volume _ hmeasCl) ?_
    gcongr
    exact le_trans hpull (by gcongr)
  -- to reals
  have hfin : ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal t.pullLip
      * ENNReal.ofReal ((volume (cfCylinder w)).toReal + 2 * κ)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono hfin hγ
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hLip.le, ENNReal.toReal_ofReal (by positivity)] at hreal
  -- and the cylinder's Lebesgue measure against its Gauss measure
  have hcylγ : (volume (cfCylinder w)).toReal
      ≤ 2 * Real.log 2 * (gaussMeasure (cfCylinder w)).toReal := by
    have h := volume_le_ofReal_mul_gaussMeasure (cfCylinder w) (measurableSet_cfCylinder w)
      (cfCylinder_subset_Ioo w)
    have h' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
  have hkey : (Real.log 2)⁻¹ * (t.pullLip * ((volume (cfCylinder w)).toReal + 2 * κ))
      ≤ t.pullLip * (2 * (gaussMeasure (cfCylinder w)).toReal + 2 * κ / Real.log 2) := by
    rw [← sub_nonneg]
    have hexp : t.pullLip * (2 * (gaussMeasure (cfCylinder w)).toReal + 2 * κ / Real.log 2)
        - (Real.log 2)⁻¹ * (t.pullLip * ((volume (cfCylinder w)).toReal + 2 * κ))
        = t.pullLip * (Real.log 2)⁻¹
            * (2 * Real.log 2 * (gaussMeasure (cfCylinder w)).toReal
                - (volume (cfCylinder w)).toReal) := by
      field_simp
      ring
    rw [hexp]
    have hnn : 0 ≤ 2 * Real.log 2 * (gaussMeasure (cfCylinder w)).toReal
        - (volume (cfCylinder w)).toReal := by linarith
    positivity
  linarith

/-- The `width` form: on a state of width `≥ η` whose denominator ratio lies in `[1/K, K]`. -/
theorem gaussMeasure_clusterSet_le_width (t : MapState) (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) {κ η K : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) (hK : 1 ≤ K)
    (hwidth : η ≤ t.width) (hlow : 1 / K ≤ t.denRatio) (hhigh : t.denRatio ≤ K) :
    (gaussMeasure (clusterSet t w κ)).toReal
      ≤ (K / η) * (2 * (gaussMeasure (cfCylinder w)).toReal + 2 * κ / Real.log 2) := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := gaussMeasure_clusterSet_le t w hw hpos hκ
  have hL : t.pullLip ≤ K / η := by
    refine le_trans (t.pullLip_le_of_denRatio hK hlow hhigh) ?_
    have hwpos := t.width_pos
    rw [div_le_div_iff₀ hwpos hη]
    nlinarith [hK]
  have hnn : 0 ≤ 2 * (gaussMeasure (cfCylinder w)).toReal + 2 * κ / Real.log 2 := by positivity
  nlinarith [h, mul_le_mul_of_nonneg_right hL hnn]

end MapState

section Audit

#print axioms cthickening_subset_Icc
#print axioms MapState.gaussMeasure_clusterSet_le
#print axioms MapState.gaussMeasure_clusterSet_le_width

end Audit

end NormalNumbers.VandeheyS7
