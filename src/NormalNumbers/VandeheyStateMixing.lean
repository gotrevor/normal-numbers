/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyStatePin

/-!
# The bridge: a transfer-operator pin becomes ψ-mixing against cylinders

`VandeheyState.stateHorizonIntegral_pin` controls the *transfer-operator* quantity
`F_n(d,s)(τ) = ∫_{y : Tⁿy ∈ A, runState δ d (W_n y) = s} h_τ`, uniformly in the tail parameter
`τ ∈ [0,1]`.  That uniformity is the whole point: the CF past enters the future **only** through
`τ`, by the conditional-density identity `setIntegral_inter_preimage`

> `∫_{I_v ∩ T^{-|v|}B} h_s = (∫_B h_{tChain s v}) · (∫_{I_v} h_s)`,

and `tChain s v ∈ [0,1]` whenever `s ∈ [0,1]` (`tChain_mem_Icc`).  Composing that identity with
the Gauss-measure mixture `γ = ∫₀¹ (h_s · Leb) dλ(s)` (`integral_gaussDensityReal_eq_mix`) turns
*any* uniform pin on `τ ↦ ∫_B h_τ` into a ψ-mixing statement for `γ` against **every** genuine
cylinder, with no gap and no loss in the rate.

The main brick is `abs_gaussMeasure_cylinder_inter_sub_le`, stated for an arbitrary measurable
future set `B ⊆ (0,1)` and an arbitrary pin constant, so it serves the state-refined pin, the
unrefined pin (`CFPsiPin.horizonIntegral_pin_geom`) and anything later.  The two corollaries
`gaussMeasure_cylinder_state_mixing` (state-refined) and `gaussMeasure_cylinder_horizon_mixing`
(unrefined, in the same normalisation) are the pair the two-point correlation estimate needs.

Everything here is unconditional.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut

/-! ## `τ ↦ ∫_B h_τ` is Lipschitz, hence continuous -/

/-- `τ ↦ ∫_B h_τ` is `2|B|`-Lipschitz on `[0,1]`, for any `B ⊆ (0,1)`.  This is
`horizonIntegral_zero_lipschitz` with the horizon bookkeeping stripped out. -/
lemma abs_setIntegral_tailDensity_sub_le {B : Set ℝ} (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1)
    {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ y in B, tailDensity t y) - ∫ y in B, tailDensity t' y|
      ≤ 2 * (volume B).toReal * |t - t'| := by
  have hBfin : volume B < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hB1) ?_
    simp [Real.volume_Ioo]
  have hint : IntegrableOn (tailDensity t) B volume :=
    (integrableOn_tailDensity ht.1).mono_set hB1
  have hint' : IntegrableOn (tailDensity t') B volume :=
    (integrableOn_tailDensity ht'.1).mono_set hB1
  rw [← integral_sub hint hint']
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := B) (C := 2 * |t - t'|) hBfin (fun y hy => by
      rw [Real.norm_eq_abs]
      exact tailDensity_lipschitz ht ht' (Set.Ioo_subset_Icc_self (hB1 hy)))
  rw [Real.norm_eq_abs] at h
  calc |∫ y in B, (tailDensity t y - tailDensity t' y)|
      ≤ 2 * |t - t'| * volume.real B := h
    _ = 2 * (volume B).toReal * |t - t'| := by rw [measureReal_def]; ring

/-- `τ ↦ ∫_B h_τ` is continuous on `[0,1]`. -/
lemma continuousOn_setIntegral_tailDensity {B : Set ℝ} (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (fun τ => ∫ y in B, tailDensity τ y) (Set.Icc (0 : ℝ) 1) := by
  set L : ℝ := 2 * (volume B).toReal with hL
  have hL0 : 0 ≤ L := by
    have := ENNReal.toReal_nonneg (a := volume B)
    positivity
  apply LipschitzOnWith.continuousOn (K := Real.toNNReal L)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq]
  calc |(∫ z in B, tailDensity x z) - ∫ z in B, tailDensity y z|
      ≤ L * |x - y| := abs_setIntegral_tailDensity_sub_le hB1 hx hy
    _ = (Real.toNNReal L : ℝ) * |x - y| := by rw [Real.coe_toNNReal L hL0]

/-! ## The mixture brick -/

/-- **A uniform pin on the transfer-operator integral becomes ψ-mixing against cylinders.**

If `|∫_B h_τ − c| ≤ E` for every `τ ∈ [0,1]`, then for every genuine word `v`

> `|γ(I_v ∩ T^{-|v|}B) − c · γ(I_v)| ≤ E · γ(I_v)`.

No gap is inserted between `I_v` and `B`: the conditional-density identity is exact, so the
"adjacency obstruction" that kills `gaussMeasure_cylinder_psi_mixing` at gap `0` simply does
not arise.  The rate is inherited verbatim from the pin. -/
theorem abs_gaussMeasure_cylinder_inter_sub_le
    {B : Set ℝ} (hB : MeasurableSet B) (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1)
    {c E : ℝ} (hpin : ∀ τ ∈ Set.Icc (0 : ℝ) 1, |(∫ y in B, tailDensity τ y) - c| ≤ E)
    (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) :
    |(gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' B)).toReal
        - c * (gaussMeasure (cfCylinder v)).toReal|
      ≤ E * (gaussMeasure (cfCylinder v)).toReal := by
  set X : Set ℝ := cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' B with hX
  have hXmeas : MeasurableSet X :=
    (measurableSet_cfCylinder v).inter ((measurable_gaussMap.iterate v.length) hB)
  have hX1 : X ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx => hx.1.1
  have hVmeas : MeasurableSet (cfCylinder v) := measurableSet_cfCylinder v
  have hV1 := cfCylinder_subset_Ioo v
  set F : ℝ → ℝ := fun τ => ∫ y in B, tailDensity τ y with hF
  set Mf : ℝ → ℝ := fun s => ∫ y in cfCylinder v, tailDensity s y with hMf
  set τf : ℝ → ℝ := fun s => tChain s v with hτf
  -- the two mixture representations
  have hmixX : (gaussMeasure X).toReal =
      ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * ∫ y in X, tailDensity s y := by
    rw [gaussMeasure_toReal_eq hXmeas hX1, integral_gaussDensityReal_eq_mix hXmeas hX1]
  have hmixV : (gaussMeasure (cfCylinder v)).toReal =
      ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * Mf s := by
    rw [gaussMeasure_toReal_eq hVmeas hV1, integral_gaussDensityReal_eq_mix hVmeas hV1]
  -- the conditional factorization
  have hfact : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∫ y in X, tailDensity s y = F (τf s) * Mf s := by
    intro s hs
    rw [hX, setIntegral_inter_preimage v hpos hs B hB hB1]
  -- continuity ingredients
  have hcontw : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have hcontM : ContinuousOn Mf (Set.Icc (0 : ℝ) 1) :=
    continuousOn_setIntegral_tailDensity hV1
  have hcontτ : ContinuousOn τf (Set.Icc (0 : ℝ) 1) := continuousOn_tChain v hpos
  have hτmap : Set.MapsTo τf (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => tChain_mem_Icc hs v hpos
  have hcontF : ContinuousOn (fun s => F (τf s)) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_setIntegral_tailDensity hB1).comp hcontτ hτmap
  have hint1 : IntegrableOn (fun s => gaussDensityReal s * (F (τf s) * Mf s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    (((hcontw.mul (hcontF.mul hcontM))).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun s => c * (gaussDensityReal s * Mf s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    ((continuousOn_const.mul (hcontw.mul hcontM)).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  -- the difference as one integral
  have hdiff : (gaussMeasure X).toReal - c * (gaussMeasure (cfCylinder v)).toReal =
      ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * Mf s * (F (τf s) - c) := by
    rw [hmixX, hmixV]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun s hs => by
      rw [hfact s (Set.Ioo_subset_Icc_self hs)])]
    rw [show c * (∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * Mf s) =
        ∫ s in Set.Ioo (0 : ℝ) 1, c * (gaussDensityReal s * Mf s) by
      rw [integral_const_mul]]
    rw [← integral_sub hint1 hint2]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s _
    ring
  -- nonnegativity of the weights
  have hMnn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Mf s := by
    intro s hs
    apply setIntegral_nonneg hVmeas
    intro y hy
    have h1 := (hV1 hy).1
    have h2 := (hV1 hy).2
    rw [tailDensity]
    have hden : (0 : ℝ) < 1 + s * y := by nlinarith [hs.1, hs.2]
    apply div_nonneg (by linarith [hs.1]) (by positivity)
  have hwnn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ gaussDensityReal s := by
    intro s hs
    rw [gaussDensityReal]
    have := hs.1
    positivity
  have habs : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      |gaussDensityReal s * Mf s * (F (τf s) - c)| ≤ E * (gaussDensityReal s * Mf s) := by
    intro s hs
    have hs' := Set.Ioo_subset_Icc_self hs
    have h := hpin (τf s) (hτmap hs')
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hwnn s hs') (hMnn s hs'))]
    calc gaussDensityReal s * Mf s * |F (τf s) - c|
        ≤ gaussDensityReal s * Mf s * E :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (hwnn s hs') (hMnn s hs'))
      _ = E * (gaussDensityReal s * Mf s) := by ring
  have hintabs : IntegrableOn (fun s => |gaussDensityReal s * Mf s * (F (τf s) - c)|)
      (Set.Ioo (0 : ℝ) 1) volume := by
    have hc : ContinuousOn (fun s => |gaussDensityReal s * Mf s * (F (τf s) - c)|)
        (Set.Icc (0 : ℝ) 1) := ((hcontw.mul hcontM).mul (hcontF.sub continuousOn_const)).abs
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hintwM : IntegrableOn (fun s => E * (gaussDensityReal s * Mf s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    ((continuousOn_const.mul (hcontw.mul hcontM)).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  rw [hdiff]
  calc |∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * Mf s * (F (τf s) - c)|
      ≤ ∫ s in Set.Ioo (0 : ℝ) 1, |gaussDensityReal s * Mf s * (F (τf s) - c)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
          (fun s => gaussDensityReal s * Mf s * (F (τf s) - c))
    _ ≤ ∫ s in Set.Ioo (0 : ℝ) 1, E * (gaussDensityReal s * Mf s) :=
        setIntegral_mono_on hintabs hintwM measurableSet_Ioo habs
    _ = E * (gaussMeasure (cfCylinder v)).toReal := by rw [integral_const_mul, hmixV]

/-! ## The countable-family version -/

open VandeheyMix

/-- **The family form of the mixture brick.**  The multiplicative error survives countable
summation: for a countable family `𝒮` of genuine words of a common length `m`,

> `|γ(familySetC 𝒮 ∩ T^{-m}B) − c·γ(familySetC 𝒮)| ≤ E·γ(familySetC 𝒮)`.

This is the shape every "past event" in a two-point correlation has: a countable union of
same-length cylinders. -/
theorem abs_gaussMeasure_familySetC_inter_sub_le {𝒮 : Set (List ℕ)} (hct : 𝒮.Countable)
    {m : ℕ} (hlen : ∀ w ∈ 𝒮, w.length = m) (hposw : ∀ w ∈ 𝒮, ∀ a ∈ w, 1 ≤ a)
    {B : Set ℝ} (hB : MeasurableSet B) (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1)
    {c E : ℝ}
    (hpin : ∀ τ ∈ Set.Icc (0 : ℝ) 1, |(∫ y in B, tailDensity τ y) - c| ≤ E) :
    |(gaussMeasure (familySetC 𝒮 ∩ (gaussMap^[m]) ⁻¹' B)).toReal
        - c * (gaussMeasure (familySetC 𝒮)).toReal|
      ≤ E * (gaussMeasure (familySetC 𝒮)).toReal := by
  classical
  set P : Set ℝ := (gaussMap^[m]) ⁻¹' B with hP
  have hPmeas : MeasurableSet P := (measurable_gaussMap.iterate m) hB
  set b : 𝒮 → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ))).toReal with hbdef
  set a : 𝒮 → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ) ∩ P)).toReal with hadef
  have hb0 : ∀ w, 0 ≤ b w := fun w => ENNReal.toReal_nonneg
  have htotb : (gaussMeasure (familySetC 𝒮)).toReal = ∑' w : 𝒮, b w := by
    rw [gaussMeasure_familySetC hct hlen, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have htota : (gaussMeasure (familySetC 𝒮 ∩ P)).toReal = ∑' w : 𝒮, a w := by
    rw [gaussMeasure_familySetC_inter hct hlen hPmeas,
      ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have hsumb : Summable b := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC hct hlen]
    exact measure_ne_top _ _
  have hsuma : Summable a := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC_inter hct hlen hPmeas]
    exact measure_ne_top _ _
  have hterm : ∀ w : 𝒮, |a w - c * b w| ≤ E * b w := by
    intro w
    have h := abs_gaussMeasure_cylinder_inter_sub_le hB hB1 hpin (w : List ℕ) (hposw _ w.2)
    rw [hlen _ w.2] at h
    exact h
  have hsumdiff : Summable fun w : 𝒮 => a w - c * b w := hsuma.sub (hsumb.mul_left _)
  have hsumbnd : Summable fun w : 𝒮 => E * b w := hsumb.mul_left _
  have habs : Summable fun w : 𝒮 => ‖a w - c * b w‖ := by
    simpa [Real.norm_eq_abs] using hsumdiff.abs
  have hstep₁ : |∑' w : 𝒮, (a w - c * b w)| ≤ ∑' w : 𝒮, |a w - c * b w| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun w : 𝒮 => a w - c * b w) habs
  have hstep₂ : (∑' w : 𝒮, |a w - c * b w|) ≤ ∑' w : 𝒮, E * b w :=
    Summable.tsum_le_tsum hterm hsumdiff.abs hsumbnd
  rw [htota, htotb, ← tsum_mul_left, ← Summable.tsum_sub hsuma (hsumb.mul_left _), ← tsum_mul_left]
  exact le_trans hstep₁ hstep₂

/-- **The brick with a past-dependent future.**  The pin is uniform in the automaton's initial
state, so the future set attached to a past cylinder `I_w` is allowed to *depend on* `w` — only
the pin constant `c` and the error `E` must be common.  This is what removes the need to
partition a past family by the state it leaves the automaton in. -/
theorem abs_gaussMeasure_biUnion_cylinder_inter_sub_le {𝒮 : Set (List ℕ)} (hct : 𝒮.Countable)
    {m : ℕ} (hlen : ∀ w ∈ 𝒮, w.length = m) (hposw : ∀ w ∈ 𝒮, ∀ a ∈ w, 1 ≤ a)
    (B : List ℕ → Set ℝ) (hB : ∀ w, MeasurableSet (B w))
    (hB1 : ∀ w, B w ⊆ Set.Ioo (0 : ℝ) 1) {c E : ℝ}
    (hpin : ∀ w ∈ 𝒮, ∀ τ ∈ Set.Icc (0 : ℝ) 1, |(∫ y in B w, tailDensity τ y) - c| ≤ E) :
    |(gaussMeasure (⋃ w ∈ 𝒮, cfCylinder w ∩ (gaussMap^[m]) ⁻¹' B w)).toReal
        - c * (gaussMeasure (familySetC 𝒮)).toReal|
      ≤ E * (gaussMeasure (familySetC 𝒮)).toReal := by
  classical
  set Y : Set ℝ := ⋃ w ∈ 𝒮, cfCylinder w ∩ (gaussMap^[m]) ⁻¹' B w with hY
  have hdisj : 𝒮.PairwiseDisjoint (fun w => cfCylinder w ∩ (gaussMap^[m]) ⁻¹' B w) := by
    intro w hw w' hw' hne
    exact (cfCylinder_disjoint (by rw [hlen w hw, hlen w' hw']) hne).mono
      Set.inter_subset_left Set.inter_subset_left
  have hYsum : gaussMeasure Y
      = ∑' w : 𝒮, gaussMeasure (cfCylinder (w : List ℕ) ∩ (gaussMap^[m]) ⁻¹' B w) :=
    measure_biUnion hct hdisj
      (fun w _ => (measurableSet_cfCylinder w).inter ((measurable_gaussMap.iterate m) (hB w)))
  set b : 𝒮 → ℝ := fun w => (gaussMeasure (cfCylinder (w : List ℕ))).toReal with hbdef
  set a : 𝒮 → ℝ := fun w =>
    (gaussMeasure (cfCylinder (w : List ℕ) ∩ (gaussMap^[m]) ⁻¹' B w)).toReal with hadef
  have htotb : (gaussMeasure (familySetC 𝒮)).toReal = ∑' w : 𝒮, b w := by
    rw [gaussMeasure_familySetC hct hlen, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have htota : (gaussMeasure Y).toReal = ∑' w : 𝒮, a w := by
    rw [hYsum, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have hsumb : Summable b := by
    refine ENNReal.summable_toReal ?_
    rw [← gaussMeasure_familySetC hct hlen]
    exact measure_ne_top _ _
  have hsuma : Summable a := by
    refine ENNReal.summable_toReal ?_
    rw [← hYsum]
    exact measure_ne_top _ _
  have hterm : ∀ w : 𝒮, |a w - c * b w| ≤ E * b w := by
    intro w
    have h := abs_gaussMeasure_cylinder_inter_sub_le (hB (w : List ℕ)) (hB1 (w : List ℕ))
      (hpin (w : List ℕ) w.2) (w : List ℕ) (hposw _ w.2)
    rw [hlen _ w.2] at h
    exact h
  have hsumdiff : Summable fun w : 𝒮 => a w - c * b w := hsuma.sub (hsumb.mul_left _)
  have hsumbnd : Summable fun w : 𝒮 => E * b w := hsumb.mul_left _
  have habs : Summable fun w : 𝒮 => ‖a w - c * b w‖ := by
    simpa [Real.norm_eq_abs] using hsumdiff.abs
  have hstep₁ : |∑' w : 𝒮, (a w - c * b w)| ≤ ∑' w : 𝒮, |a w - c * b w| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun w : 𝒮 => a w - c * b w) habs
  have hstep₂ : (∑' w : 𝒮, |a w - c * b w|) ≤ ∑' w : 𝒮, E * b w :=
    Summable.tsum_le_tsum hterm hsumdiff.abs hsumbnd
  rw [htota, htotb, ← tsum_mul_left, ← Summable.tsum_sub hsuma (hsumb.mul_left _), ← tsum_mul_left]
  exact le_trans hstep₁ hstep₂

/-! ## The two corollaries the correlation estimate needs -/

/-- The unrefined pin, in cylinder form: `|γ(I_v ∩ T^{-|v|}(horizonSet A n)) − γ(A)γ(I_v)|
≤ (79/100)ⁿ γ(A) γ(I_v)`.  (`gaussMeasure_cylinder_psi_mixing` in the normalisation the
two-point estimate uses: the future event is already a horizon set.) -/
theorem abs_gaussMeasure_cylinder_horizon_sub_le {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (n : ℕ) (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) :
    |(gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' horizonSet A n)).toReal
        - (gaussMeasure A).toReal * (gaussMeasure (cfCylinder v)).toReal|
      ≤ (79 / 100) ^ n * (gaussMeasure A).toReal * (gaussMeasure (cfCylinder v)).toReal := by
  have h := abs_gaussMeasure_cylinder_inter_sub_le (measurableSet_horizonSet hA n)
    (horizonSet_subset A n)
    (c := (gaussMeasure A).toReal) (E := (79 / 100) ^ n * (gaussMeasure A).toReal)
    (fun τ hτ => horizonIntegral_pin_geom hA hA1 n hτ) v hpos
  calc |(gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' horizonSet A n)).toReal
          - (gaussMeasure A).toReal * (gaussMeasure (cfCylinder v)).toReal| ≤
      (79 / 100) ^ n * (gaussMeasure A).toReal * (gaussMeasure (cfCylinder v)).toReal := h

namespace VandeheyState

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **State-refined ψ-mixing at gap zero.**  The pin on the state-refined transfer operator
becomes, verbatim, a mixing statement for `γ` against every genuine cylinder:

> `|γ(I_v ∩ T^{-|v|}{Tⁿ· ∈ A, state = t}) − c·γ(A)·γ(I_v)| ≤ Cθⁿ γ(A) γ(I_v)`.

The initial state of the automaton after the past word `v` is a free parameter `e`, so this is
exactly the conditional statement a two-point correlation needs.  Feed it
`stateHorizonIntegral_pin` with `c = (card S)⁻¹`. -/
theorem abs_gaussMeasure_cylinder_state_sub_le (δ : S → ℕ → S) {A : Set ℝ}
    (hA : MeasurableSet A) (t : S) {c C θ : ℝ}
    (hpin : ∀ (n : ℕ) (d : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ A n d t τ - c * (gaussMeasure A).toReal|
        ≤ C * θ ^ n * (gaussMeasure A).toReal)
    (n : ℕ) (e : S) (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) :
    |(gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹'
          stateHorizonSet δ A n e t)).toReal
        - c * (gaussMeasure A).toReal * (gaussMeasure (cfCylinder v)).toReal|
      ≤ C * θ ^ n * (gaussMeasure A).toReal * (gaussMeasure (cfCylinder v)).toReal :=
  abs_gaussMeasure_cylinder_inter_sub_le (measurableSet_stateHorizonSet hA δ n e t)
    (stateHorizonSet_subset δ A n e t)
    (c := c * (gaussMeasure A).toReal) (E := C * θ ^ n * (gaussMeasure A).toReal)
    (fun τ hτ => hpin n e τ hτ) v hpos

/-- The family form of `abs_gaussMeasure_cylinder_state_sub_le`. -/
theorem abs_gaussMeasure_familySetC_state_sub_le (δ : S → ℕ → S) {A : Set ℝ}
    (hA : MeasurableSet A) (t : S) {c C θ : ℝ}
    (hpin : ∀ (n : ℕ) (d : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ A n d t τ - c * (gaussMeasure A).toReal|
        ≤ C * θ ^ n * (gaussMeasure A).toReal)
    (n : ℕ) (e : S) {𝒮 : Set (List ℕ)} (hct : 𝒮.Countable) {m : ℕ}
    (hlen : ∀ w ∈ 𝒮, w.length = m) (hposw : ∀ w ∈ 𝒮, ∀ a ∈ w, 1 ≤ a) :
    |(gaussMeasure (familySetC 𝒮 ∩ (gaussMap^[m]) ⁻¹' stateHorizonSet δ A n e t)).toReal
        - c * (gaussMeasure A).toReal * (gaussMeasure (familySetC 𝒮)).toReal|
      ≤ C * θ ^ n * (gaussMeasure A).toReal * (gaussMeasure (familySetC 𝒮)).toReal := by
  exact abs_gaussMeasure_familySetC_inter_sub_le hct hlen hposw
    (measurableSet_stateHorizonSet hA δ n e t) (stateHorizonSet_subset δ A n e t)
    (fun τ hτ => hpin n e τ hτ)

/-- The shape the two-point correlation actually uses: a countable past family `𝒱` of genuine
length-`m` words, each cylinder paired with the future event **read from the state the automaton
reaches after that very word**.  The pin's uniformity in the initial state makes the `v`-dependence
free of charge. -/
theorem abs_gaussMeasure_biUnion_state_sub_le (δ : S → ℕ → S) {A : Set ℝ}
    (hA : MeasurableSet A) (t : S) {c C θ : ℝ}
    (hpin : ∀ (n : ℕ) (e : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ A n e t τ - c * (gaussMeasure A).toReal|
        ≤ C * θ ^ n * (gaussMeasure A).toReal)
    (n : ℕ) (d : S) {𝒱 : Set (List ℕ)} (hct : 𝒱.Countable) {m : ℕ}
    (hlen : ∀ w ∈ 𝒱, w.length = m) (hposw : ∀ w ∈ 𝒱, ∀ a ∈ w, 1 ≤ a) :
    |(gaussMeasure (⋃ v ∈ 𝒱, cfCylinder v ∩ (gaussMap^[m]) ⁻¹'
          stateHorizonSet δ A n (runState δ d v) t)).toReal
        - c * (gaussMeasure A).toReal * (gaussMeasure (familySetC 𝒱)).toReal|
      ≤ C * θ ^ n * (gaussMeasure A).toReal * (gaussMeasure (familySetC 𝒱)).toReal :=
  abs_gaussMeasure_biUnion_cylinder_inter_sub_le hct hlen hposw
    (fun v => stateHorizonSet δ A n (runState δ d v) t)
    (fun _ => measurableSet_stateHorizonSet hA δ n _ t)
    (fun _ => stateHorizonSet_subset δ A n _ t)
    (fun v _ τ hτ => hpin n (runState δ d v) τ hτ)

end VandeheyState

end NormalNumbers
