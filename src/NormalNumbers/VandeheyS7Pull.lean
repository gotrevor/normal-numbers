/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Width
import NormalNumbers.VandeheyS7Reduce
import NormalNumbers.TBrick

/-!
# S7-PB: the state pullback is bounded on *every* measurable set, and the tower is free

The crux `OrbitWordBound` asks that the image expansion of a CF-normal `x` never over-represent a
finite word `w`.  The transducer turns an occurrence of `w` at output time `t` into the event
`Gⁿx ∈ sₜ⁻¹(I_w)` at the matched input time `n`, so the crux's *measure-theoretic* half is:

> how much Gauss mass can a state's pullback of a target of mass `γ(I_w)` have?

Up to lap 73 the repo answered this only for **intervals** (`sub_le_of_image_le`, lap 65): a
sub-interval of `[0,1]` whose image is short is itself short.  That is not enough, because the
target an emitted *block* presents is not an interval.  While the input point is frozen the
transducer emits `L` forced digits, and those `L` digits are the first `L` digits of the single
point `z = s(Gⁿx)`; the event "the block contains `w` at offset `j`" is `Gⁿx ∈ s⁻¹(G^{-j} I_w)`,
and `G^{-j} I_w` is a countable union of cylinders, not an interval.

This module removes the interval restriction and draws the consequence.

## Results

* `MobState.expand_le` / `MobState.contract_le` — the two-sided derivative bound, algebraic:
  `(width / distortion)·|u−v| ≤ |mob u − mob v| ≤ (width · distortion)·|u−v|` on `[0,1]`.
* `MobState.volume_preimage_le` — **for an arbitrary set `A`**,
  `|mob⁻¹(A) ∩ (0,1)| ≤ (distortion / width) · |A|`.  No measurability and no interval structure:
  the state's inverse is Lipschitz on the image, and a Lipschitz map cannot increase
  `μH[1] = volume` by more than its constant.
* `MobState.gaussMeasure_preimage_le` — the Gauss form,
  `γ(mob⁻¹ A ∩ (0,1)) ≤ (2·distortion/width)·γ(A)`.
* `MobState.gaussMeasure_preimage_tower_le` — **the tower is free.**  For every `j`,
  `γ(mob⁻¹(G^{-j} I_w ∩ (0,1)) ∩ (0,1)) ≤ (2K/η)·γ(I_w)`, with a bound *independent of `j`*,
  because `γ` is `gaussMap`-invariant (`gaussMeasure_preimage_iterate`).
* `blockPullback_sum_le` — hence the whole emitted block of length `L` pulls back to input sets of
  total Gauss mass at most `(2K/η)·L·γ(I_w)`: **linear in the block length, with exactly the
  density the crux demands**, and with no loss accumulating along the block.

That last statement is the operator's sentence made precise — "an output word `w` pulls back,
state by state, to input sets whose Gauss mass is comparable to `γ(I_w)` by bounded distortion" —
and it is unconditional.  What the crux still needs on top of it is (i) an absolute width floor
`η` and (ii) the passage from these *masses* to *empirical frequencies* along the orbit of one
CF-normal `x`; (ii) is the predictable-set obstruction, directive fact (α).

The point of doing the estimate for the whole block at once is that the naive per-output-time
estimate loses the invariance: `γ(s⁻¹ I_w) ≤ (2K/η) γ(I_w)` at each of the `L` times would need
the `L` targets to be the *same* `I_w`, whereas the honest target at offset `j` is `G^{-j} I_w`.
Gauss invariance says that costs nothing, so the block bound has the same constant as one step.

## Guard rule

Content locator: the bound is trivial at `L = 0`, and for an `A` disjoint from the image it is
`0 ≤ …`; all the content is the *uniformity in `j`*, i.e. that the tower costs nothing beyond one
step.  The `1/width` is not an artefact — `one_le_volume_preimage_image` shows the state's own
image is a target whose pullback is all of `(0,1)`, so no bound with a constant `o(1/width)` holds.
Degenerate cases: `distortion = 1`, `width = 1` (an isometry of `(0,1)`) gives the constant `2`,
which is the Gauss/Lebesgue comparison and is the best this route gives without using the density;
`s.hdet` forbids the constant map, for which no pullback bound could hold at all.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

namespace MobState

/-- `|det| = width · (c+d) · d`. -/
theorem abs_det_eq (s : MobState) :
    |s.a * s.d - s.b * s.c| = s.width * ((s.c + s.d) * s.d) := by
  have hd : 0 < s.d := s.hd
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  rw [width_eq]
  field_simp

/-- The absolute difference, in closed form. -/
theorem abs_mob_sub (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |s.mob u - s.mob v|
      = |s.a * s.d - s.b * s.c| * |u - v| / ((s.c * u + s.d) * (s.c * v + s.d)) := by
  have h1 := s.den_pos hu
  have h2 := s.den_pos hv
  rw [mob_sub s hv hu, abs_div, abs_mul, abs_of_pos (mul_pos h1 h2)]

/-- **Expansion.**  The state expands by at least `width / distortion` on `[0,1]`. -/
theorem expand_le (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v)
    (hv1 : v ≤ 1) : s.width / s.distortion * |u - v| ≤ |s.mob u - s.mob v| := by
  have hd : 0 < s.d := s.hd
  have hdne : s.d ≠ 0 := hd.ne'
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  have hcdne : s.c + s.d ≠ 0 := hcd.ne'
  have h1 := s.den_pos hu
  have h2 := s.den_pos hv
  have hD : 0 < |s.a * s.d - s.b * s.c| := abs_pos.2 s.hdet
  have hwd : s.width / s.distortion
      = |s.a * s.d - s.b * s.c| / ((s.c + s.d) * (s.c + s.d)) := by
    rw [width_eq, distortion]
    field_simp
    try ring
  have hle : (s.c * u + s.d) * (s.c * v + s.d) ≤ (s.c + s.d) * (s.c + s.d) := by
    have ha : s.c * u + s.d ≤ s.c + s.d := by nlinarith [s.hc]
    have hb : s.c * v + s.d ≤ s.c + s.d := by nlinarith [s.hc]
    exact mul_le_mul ha hb h2.le hcd.le
  rw [abs_mob_sub s hu hv, hwd, div_mul_eq_mul_div,
    div_le_div_iff₀ (by positivity) (mul_pos h1 h2)]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **Contraction.**  The state contracts by at most `width · distortion` on `[0,1]`. -/
theorem contract_le (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v)
    (hv1 : v ≤ 1) : |s.mob u - s.mob v| ≤ s.width * s.distortion * |u - v| := by
  have hd : 0 < s.d := s.hd
  have hdne : s.d ≠ 0 := hd.ne'
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  have hcdne : s.c + s.d ≠ 0 := hcd.ne'
  have h1 := s.den_pos hu
  have h2 := s.den_pos hv
  have hwd : s.width * s.distortion = |s.a * s.d - s.b * s.c| / (s.d * s.d) := by
    rw [width_eq, distortion]
    field_simp
    try ring
  have hge : s.d * s.d ≤ (s.c * u + s.d) * (s.c * v + s.d) := by
    have ha : s.d ≤ s.c * u + s.d := by nlinarith [s.hc]
    have hb : s.d ≤ s.c * v + s.d := by nlinarith [s.hc]
    exact mul_le_mul ha hb hd.le h1.le
  rw [abs_mob_sub s hu hv, hwd, div_mul_eq_mul_div,
    div_le_div_iff₀ (mul_pos h1 h2) (by positivity)]
  exact mul_le_mul_of_nonneg_left hge (by positivity)

/-- The state is injective on `(0,1)`. -/
theorem injOn_Ioo (s : MobState) : Set.InjOn s.mob (Set.Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  have hw := s.width_pos
  have hdist := s.distortion_pos
  have hc : 0 < s.width / s.distortion := div_pos hw hdist
  have h := s.expand_le hu.1.le hu.2.le hv.1.le hv.2.le
  rw [huv, sub_self, abs_zero] at h
  by_contra hne
  have hpos : 0 < |u - v| := abs_pos.2 (sub_ne_zero.2 hne)
  nlinarith

theorem measurable_mob (s : MobState) : Measurable s.mob :=
  ((measurable_id.const_mul s.a).add_const s.b).div ((measurable_id.const_mul s.c).add_const s.d)

/-- **The pullback bound, for an arbitrary target set.**  The state's inverse is
`distortion / width`-Lipschitz on the image, and a Lipschitz map cannot increase
`μH[1] = volume` by more than its constant. -/
theorem volume_preimage_le (s : MobState) (A : Set ℝ) :
    volume (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal (s.distortion / s.width) * volume A := by
  classical
  set S : Set ℝ := s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1 with hSdef
  have hSsub : S ⊆ Set.Ioo (0:ℝ) 1 := by rw [hSdef]; exact Set.inter_subset_right
  have hinj : Set.InjOn s.mob S := (s.injOn_Ioo).mono hSsub
  have hw := s.width_pos
  have hdist := s.distortion_pos
  set K : ℝ := s.distortion / s.width with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hlip : LipschitzOnWith K.toNNReal (Function.invFunOn s.mob S) (s.mob '' S) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro y₁ ⟨u, hu, rfl⟩ y₂ ⟨v, hv, rfl⟩
    have hue : Function.invFunOn s.mob S (s.mob u) = u := hinj.leftInvOn_invFunOn hu
    have hve : Function.invFunOn s.mob S (s.mob v) = v := hinj.leftInvOn_invFunOn hv
    rw [hue, hve, Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hKpos.le, hK]
    have hu' := hSsub hu
    have hv' := hSsub hv
    have h := s.expand_le hu'.1.le hu'.2.le hv'.1.le hv'.2.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    calc |u - v| * s.width = s.width / s.distortion * |u - v| * s.distortion := by
          field_simp
          try ring
      _ ≤ |s.mob u - s.mob v| * s.distortion := mul_le_mul_of_nonneg_right h hdist.le
      _ = s.distortion * |s.mob u - s.mob v| := by ring
  have himg : Function.invFunOn s.mob S '' (s.mob '' S) = S :=
    hinj.invFunOn_image (Set.Subset.refl S)
  have hH := hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1)
  rw [himg, ENNReal.rpow_one, MeasureTheory.hausdorffMeasure_real] at hH
  refine le_trans hH ?_
  have hcoe : ((K.toNNReal : NNReal) : ENNReal) = ENNReal.ofReal K := rfl
  rw [hcoe]
  gcongr
  rintro y ⟨t, ht, rfl⟩
  rw [hSdef] at ht
  exact ht.1

/-- The image of `(0,1)` is short: at most `width · distortion`. -/
theorem volume_image_Ioo_le (s : MobState) :
    volume (s.mob '' Set.Ioo (0:ℝ) 1) ≤ ENNReal.ofReal (s.width * s.distortion) := by
  have hw := s.width_pos
  have hdist := s.distortion_pos
  have hlip : LipschitzOnWith (s.width * s.distortion).toNNReal s.mob (Set.Ioo (0:ℝ) 1) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact s.contract_le hu.1.le hu.2.le hv.1.le hv.2.le
  have hH := hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1)
  rw [ENNReal.rpow_one, MeasureTheory.hausdorffMeasure_real] at hH
  refine le_trans hH ?_
  have hcoe : (((s.width * s.distortion).toNNReal : NNReal) : ENNReal)
      = ENNReal.ofReal (s.width * s.distortion) := rfl
  rw [hcoe, Real.volume_Ioo]
  simp

/-- **The content locator.**  The `1/width` in `volume_preimage_le` is real: the state's own image
is a target whose pullback is all of `(0,1)`, so the ratio is at least `1/(width · distortion)`. -/
theorem one_le_volume_preimage_image (s : MobState) :
    (1 : ENNReal) ≤ ENNReal.ofReal (s.distortion / s.width)
      * ENNReal.ofReal (s.width * s.distortion) := by
  have hkey := s.volume_preimage_le (s.mob '' Set.Ioo (0:ℝ) 1)
  have heq : s.mob ⁻¹' (s.mob '' Set.Ioo (0:ℝ) 1) ∩ Set.Ioo (0:ℝ) 1 = Set.Ioo (0:ℝ) 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, and_iff_right_iff_imp]
    intro ht
    exact Set.mem_image_of_mem _ ht
  rw [heq, Real.volume_Ioo] at hkey
  simp only [sub_zero, ENNReal.ofReal_one] at hkey
  refine le_trans hkey ?_
  gcongr
  exact s.volume_image_Ioo_le

end MobState

/-! ## The Gauss form -/

/-- `γ` only sees `(0,1)`. -/
theorem gaussMeasure_inter_Ioo {S : Set ℝ} (hS : MeasurableSet S) :
    gaussMeasure (S ∩ Set.Ioo (0:ℝ) 1) = gaussMeasure S := by
  rw [gaussMeasure_apply (hS.inter measurableSet_Ioo), gaussMeasure_apply hS]
  congr 1
  rw [Set.inter_assoc, Set.inter_self]

/-- **Gauss invariance along the tower**: `γ(G^{-j} S) = γ(S)` for every `j`. -/
theorem gaussMeasure_preimage_iterate (j : ℕ) :
    ∀ {S : Set ℝ}, MeasurableSet S → gaussMeasure (gaussMap^[j] ⁻¹' S) = gaussMeasure S := by
  induction j with
  | zero => intro S _; simp
  | succ n ih =>
    intro S hS
    have hmeas : MeasurableSet (gaussMap^[n] ⁻¹' S) :=
      hS.preimage (measurable_gaussMap.iterate n)
    rw [Function.iterate_succ, Set.preimage_comp, gaussMeasure_preimage hmeas]
    exact ih hS

namespace MobState

/-- **The Gauss pullback bound**, for a measurable target inside `(0,1)`. -/
theorem gaussMeasure_preimage_le (s : MobState) {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (0:ℝ) 1) :
    gaussMeasure (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal (2 * s.distortion / s.width) * gaussMeasure A := by
  have hw := s.width_pos
  have hdist := s.distortion_pos
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmeas : MeasurableSet (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1) :=
    (hA.preimage s.measurable_mob).inter measurableSet_Ioo
  calc gaussMeasure (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume (s.mob ⁻¹' A ∩ Set.Ioo (0:ℝ) 1) :=
        gaussMeasure_le_volume _ hmeas
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹
          * (ENNReal.ofReal (s.distortion / s.width) * volume A) := by
        gcongr
        exact s.volume_preimage_le A
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * (ENNReal.ofReal (s.distortion / s.width)
          * (ENNReal.ofReal (2 * Real.log 2) * gaussMeasure A)) := by
        gcongr
        exact volume_le_ofReal_mul_gaussMeasure A hA hAsub
    _ = ENNReal.ofReal (2 * s.distortion / s.width) * gaussMeasure A := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        try ring

/-- **The tower is free.**  Pulling back the `j`-th preimage of a cylinder costs the same as
pulling back the cylinder, uniformly in `j`. -/
theorem gaussMeasure_preimage_tower_le (s : MobState) {η K : ℝ} (hη : 0 < η)
    (hwidth : η ≤ s.width) (hK : s.distortion ≤ K) (w : List ℕ) (j : ℕ) :
    gaussMeasure (s.mob ⁻¹' (gaussMap^[j] ⁻¹' cfCylinder w ∩ Set.Ioo (0:ℝ) 1)
        ∩ Set.Ioo (0:ℝ) 1)
      ≤ ENNReal.ofReal (2 * K / η) * gaussMeasure (cfCylinder w) := by
  have hw := s.width_pos
  have hdist := s.distortion_pos
  have hcyl : MeasurableSet (gaussMap^[j] ⁻¹' cfCylinder w) :=
    (measurableSet_cfCylinder w).preimage (measurable_gaussMap.iterate j)
  have h1 := s.gaussMeasure_preimage_le (hcyl.inter measurableSet_Ioo) Set.inter_subset_right
  have h2 : gaussMeasure (gaussMap^[j] ⁻¹' cfCylinder w ∩ Set.Ioo (0:ℝ) 1)
      = gaussMeasure (cfCylinder w) := by
    rw [gaussMeasure_inter_Ioo hcyl]
    exact gaussMeasure_preimage_iterate j (measurableSet_cfCylinder w)
  rw [h2] at h1
  have hKpos : 0 < K := lt_of_lt_of_le hdist hK
  refine le_trans h1 ?_
  gcongr <;> first
    | linarith
    | (rw [div_le_div_iff₀ hw hη]; nlinarith)

/-- **The block bound.**  The whole emitted block of length `L` pulls back to input sets of total
Gauss mass at most `(2K/η)·L·γ(I_w)` — linear in `L`, with no loss along the block. -/
theorem blockPullback_sum_le (s : MobState) {η K : ℝ} (hη : 0 < η)
    (hwidth : η ≤ s.width) (hK : s.distortion ≤ K) (w : List ℕ) (L : ℕ) :
    ∑ j ∈ Finset.range L,
        (gaussMeasure (s.mob ⁻¹' (gaussMap^[j] ⁻¹' cfCylinder w ∩ Set.Ioo (0:ℝ) 1)
          ∩ Set.Ioo (0:ℝ) 1)).toReal
      ≤ 2 * K / η * L * (gaussMeasure (cfCylinder w)).toReal := by
  have hdist := s.distortion_pos
  have hKpos : 0 < K := lt_of_lt_of_le hdist hK
  have hc : (0:ℝ) ≤ 2 * K / η := by positivity
  have hterm : ∀ j ∈ Finset.range L,
      (gaussMeasure (s.mob ⁻¹' (gaussMap^[j] ⁻¹' cfCylinder w ∩ Set.Ioo (0:ℝ) 1)
        ∩ Set.Ioo (0:ℝ) 1)).toReal
        ≤ 2 * K / η * (gaussMeasure (cfCylinder w)).toReal := by
    intro j _
    have h := s.gaussMeasure_preimage_tower_le hη hwidth hK w j
    have hfin : ENNReal.ofReal (2 * K / η) * gaussMeasure (cfCylinder w) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have h' := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h'
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

end MobState

section Audit

#print axioms MobState.expand_le
#print axioms MobState.contract_le
#print axioms MobState.volume_preimage_le
#print axioms MobState.one_le_volume_preimage_image
#print axioms gaussMeasure_preimage_iterate
#print axioms MobState.gaussMeasure_preimage_le
#print axioms MobState.gaussMeasure_preimage_tower_le
#print axioms MobState.blockPullback_sum_le

end Audit

end NormalNumbers.VandeheyS7
