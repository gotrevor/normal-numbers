/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-PM: the pullback bound for `MapState` — the shape the §7 front actually needs

S7-PB proved the pullback bound for `MobState`, whose sign convention (`0 ≤ a`, `0 ≤ c`) S7-NE
already showed is too narrow for the transducer's reduced states: a `MapState` only knows
`0 < d`, `0 < c + d` and the endpoint conditions.  Since the whole front (S7-CL/S7-FT/S7-MD) is
stated for `MapState`, the per-cell input needs the `MapState` version, which is this module.

* `denMax s = max d (c+d)` — the largest value of the denominator on `[0,1]`, by convexity
  (`den_le_denMax`); no sign hypothesis on `c` is used.
* `pullLip s = denMax s ^ 2 / |det s|` — the inverse's Lipschitz constant on the image
  (`abs_sub_le_pullLip`), directly from the increment formula.
* `volume_preimage_le` / `gaussMeasure_preimage_le` — the pullback bounds, with `pullLip` in
  place of `distortion / width`.
* `pullLip_le_of_denRatio` — `pullLip s ≤ K / width s` whenever `denRatio ∈ [1/K, K]`, so along a
  run S7-Box's absolute band `denRatio ∈ (1/2, 6]` gives the uniform constant `K = 6`: the
  `1/η` of `S7-MD`.
-/
import NormalNumbers.VandeheyS7Box
import NormalNumbers.VandeheyS7Pull

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

/-- The largest value of the denominator on `[0,1]`. -/
noncomputable def denMax (s : MapState) : ℝ := max s.d (s.c + s.d)

lemma denMax_pos (s : MapState) : 0 < s.denMax :=
  lt_of_lt_of_le s.hd (le_max_left _ _)

/-- The denominator is at most `denMax` on `[0,1]` — convexity, no sign condition on `c`. -/
lemma den_le_denMax (s : MapState) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    s.c * z + s.d ≤ s.denMax := by
  have h : s.c * z + s.d = (1 - z) * s.d + z * (s.c + s.d) := by ring
  have h1 : s.d ≤ s.denMax := le_max_left _ _
  have h2 : s.c + s.d ≤ s.denMax := le_max_right _ _
  rw [h]
  nlinarith [hz.1, hz.2]

/-- The increment formula. -/
theorem mob_sub (s : MapState) {u v : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    s.mob v - s.mob u = s.det * (v - u) / ((s.c * v + s.d) * (s.c * u + s.d)) := by
  have hpu := s.den_pos hu
  have hpv := s.den_pos hv
  simp only [mob, det]
  rw [div_sub_div _ _ hpv.ne' hpu.ne', div_eq_div_iff (mul_ne_zero hpv.ne' hpu.ne')
    (mul_ne_zero hpv.ne' hpu.ne')]
  ring

/-- The Lipschitz constant of the inverse map on the image. -/
noncomputable def pullLip (s : MapState) : ℝ := s.denMax ^ 2 / |s.det|

lemma pullLip_pos (s : MapState) : 0 < s.pullLip := by
  have h := s.denMax_pos
  have hdet : (0:ℝ) < |s.det| := abs_pos.mpr s.hdet
  rw [pullLip]; positivity

/-- **The expansion bound.**  The map is injective on `[0,1]` with an inverse of Lipschitz
constant `pullLip`. -/
theorem abs_sub_le_pullLip (s : MapState) {u v : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1)
    (hv : v ∈ Set.Icc (0:ℝ) 1) : |v - u| ≤ s.pullLip * |s.mob v - s.mob u| := by
  have hpu := s.den_pos hu
  have hpv := s.den_pos hv
  have hdet : (0:ℝ) < |s.det| := abs_pos.mpr s.hdet
  have hsub := s.mob_sub hu hv
  have habs : |s.mob v - s.mob u| = |s.det| * |v - u| / ((s.c * v + s.d) * (s.c * u + s.d)) := by
    rw [hsub, abs_div, abs_mul, abs_of_pos (mul_pos hpv hpu)]
  have hden : (s.c * v + s.d) * (s.c * u + s.d) ≤ s.denMax ^ 2 := by
    have h1 := s.den_le_denMax hv
    have h2 := s.den_le_denMax hu
    nlinarith [hpu, hpv, s.denMax_pos]
  rw [habs, pullLip]
  have hP : (0:ℝ) < (s.c * v + s.d) * (s.c * u + s.d) := mul_pos hpv hpu
  have hEq : s.denMax ^ 2 / |s.det| * (|s.det| * |v - u| / ((s.c * v + s.d) * (s.c * u + s.d)))
      = (s.denMax ^ 2 / ((s.c * v + s.d) * (s.c * u + s.d))) * |v - u| := by
    field_simp
  rw [hEq]
  have hge : (1:ℝ) ≤ s.denMax ^ 2 / ((s.c * v + s.d) * (s.c * u + s.d)) := by
    rw [le_div_iff₀ hP]; linarith [hden]
  nlinarith [abs_nonneg (v - u)]

theorem injOn_Icc (s : MapState) : Set.InjOn s.mob (Set.Icc (0:ℝ) 1) := by
  intro u hu v hv heq
  have h := s.abs_sub_le_pullLip hu hv
  rw [heq] at h
  simp at h
  linarith

theorem injOn_Ioo (s : MapState) : Set.InjOn s.mob (Set.Ioo (0:ℝ) 1) :=
  s.injOn_Icc.mono Set.Ioo_subset_Icc_self

theorem measurable_mob (s : MapState) : Measurable s.mob :=
  ((measurable_id.const_mul s.a).add_const s.b).div ((measurable_id.const_mul s.c).add_const s.d)

/-- **The pullback bound for a `MapState`**, for an arbitrary target set. -/
theorem volume_preimage_le (s : MapState) (A : Set ℝ) :
    volume (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal s.pullLip * volume A := by
  classical
  set S : Set ℝ := s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1 with hSdef
  have hSsub : S ⊆ Set.Ioo (0:ℝ) 1 := by rw [hSdef]; exact Set.inter_subset_right
  have hinj : Set.InjOn s.mob S := (s.injOn_Ioo).mono hSsub
  have hKpos : 0 < s.pullLip := s.pullLip_pos
  have hlip : LipschitzOnWith s.pullLip.toNNReal (Function.invFunOn s.mob S) (s.mob '' S) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro y₁ ⟨u, hu, rfl⟩ y₂ ⟨v, hv, rfl⟩
    have hue : Function.invFunOn s.mob S (s.mob u) = u := hinj.leftInvOn_invFunOn hu
    have hve : Function.invFunOn s.mob S (s.mob v) = v := hinj.leftInvOn_invFunOn hv
    rw [hue, hve, Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hKpos.le]
    have hu' := hSsub hu
    have hv' := hSsub hv
    have h := s.abs_sub_le_pullLip (u := v) (v := u) ⟨hv'.1.le, hv'.2.le⟩ ⟨hu'.1.le, hu'.2.le⟩
    exact h
  have himg : Function.invFunOn s.mob S '' (s.mob '' S) = S :=
    hinj.invFunOn_image (Set.Subset.refl S)
  have hH := hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1)
  rw [himg, ENNReal.rpow_one, MeasureTheory.hausdorffMeasure_real] at hH
  refine le_trans hH ?_
  have hcoe : ((s.pullLip.toNNReal : NNReal) : ENNReal) = ENNReal.ofReal s.pullLip := rfl
  rw [hcoe]
  gcongr
  rintro y ⟨t, ht, rfl⟩
  rw [hSdef] at ht
  exact ht.1

/-- **The Gauss pullback bound for a `MapState`.** -/
theorem gaussMeasure_preimage_le (s : MapState) {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (0:ℝ) 1) :
    gaussMeasure (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal (2 * s.pullLip) * gaussMeasure A := by
  have hKpos : 0 < s.pullLip := s.pullLip_pos
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmeas : MeasurableSet (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1) :=
    (hA.preimage s.measurable_mob).inter measurableSet_Ioo
  calc gaussMeasure (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1) :=
        gaussMeasure_le_volume _ hmeas
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal s.pullLip * volume A) := by
        gcongr
        exact s.volume_preimage_le A
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal s.pullLip
          * (ENNReal.ofReal (2 * Real.log 2) * gaussMeasure A)) := by
        gcongr
        exact volume_le_ofReal_mul_gaussMeasure A hA hAsub
    _ = ENNReal.ofReal (2 * s.pullLip) * gaussMeasure A := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-! ## The constant, in terms of the width -/

/-- **`pullLip ≤ K / width`** whenever the denominator ratio lies in `[1/K, K]`.  Along a run
S7-Box gives `denRatio ∈ (1/2, 6]`, hence the absolute `K = 6`. -/
theorem pullLip_le_of_denRatio (s : MapState) {K : ℝ} (hK : 1 ≤ K)
    (hlow : 1 / K ≤ s.denRatio) (hhigh : s.denRatio ≤ K) :
    s.pullLip ≤ K / s.width := by
  have hd := s.hd
  have hcd := s.hcd
  have hdet : (0:ℝ) < |s.det| := abs_pos.mpr s.hdet
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hwe : s.width = |s.det| / (s.d * (s.c + s.d)) := s.width_eq
  have hratio : s.denRatio = (s.c + s.d) / s.d := rfl
  have hcdK : s.c + s.d ≤ K * s.d := by
    rw [hratio, div_le_iff₀ hd] at hhigh; linarith
  have hdK : s.d ≤ K * (s.c + s.d) := by
    rw [hratio, div_le_div_iff₀ hKpos hd] at hlow; linarith
  have hsq : s.denMax ^ 2 ≤ K * (s.d * (s.c + s.d)) := by
    rcases max_cases s.d (s.c + s.d) with ⟨heq, hle⟩ | ⟨heq, hle⟩
    · rw [denMax, heq]; nlinarith [hdK, hd, hcd]
    · rw [denMax, heq]; nlinarith [hcdK, hd, hcd]
  have hKw : K / s.width = K * (s.d * (s.c + s.d)) / |s.det| := by
    rw [hwe]; field_simp
  rw [pullLip, hKw, div_le_div_iff₀ hdet hdet]
  nlinarith [hsq, hdet]

end MapState

section Audit

#print axioms MapState.den_le_denMax
#print axioms MapState.abs_sub_le_pullLip
#print axioms MapState.volume_preimage_le
#print axioms MapState.gaussMeasure_preimage_le
#print axioms MapState.pullLip_le_of_denRatio

end Audit

end NormalNumbers.VandeheyS7
