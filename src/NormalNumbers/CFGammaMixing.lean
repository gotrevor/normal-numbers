/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFPin

/-!
# W4 groundwork — γ-mixing for cylinders (the KPW-Lemma-6 substitute)

The W4 Chebyshev assembly needs correlation decay *under the Gauss
measure*: `|γ(I_v ∩ T^{-(|v|+g)}A) − γ(I_v)γ(A)| ≤ ε(g)·γ(I_v)` with
`ε` summable.  The Lebesgue machinery gives this for free once the
conditional-density identity is generalized from the uniform start
(`h_0 = 1`, `volume_inter_preimage_aux`) to an arbitrary start
`h_s`, `s ∈ [0,1]`:

  `∫_{I_w ∩ T^{-|w|}B} h_s = (∫_B h_{tChain s w}) · (∫_{I_w} h_s)`,

where `tChain s w` runs the Euler tail-parameter recursion
`t ↦ 1/(b+t)` from `s` instead of `0`.  Then, writing
`γ = ∫₀¹ (h_s·Leb) dλ(s)` (the mixture Fubini of `CFPin`) and using the
pin `|G_g(t) − γ(A)| ≤ 4|A|·(9/10)^g` — which is uniform in `t ∈ [0,1]`,
hence applies at `t = tChain s v` — the γ-correlation bound falls out
with the same geometric rate.
-/

namespace NormalNumbers

open MeasureTheory

lemma cfCylinder_subset_Ioo (w : List ℕ) :
    cfCylinder w ⊆ Set.Ioo (0 : ℝ) 1 := fun _ hx => hx.1

/-! ## The started tail parameter -/

/-- The tail parameter of the word `w` started at `s`:
`tChain s [] = s`, `tChain s (w ++ [b]) = 1/(b + tChain s w)`.
`tChain 0 = tParam` on nonempty words. -/
noncomputable def tChain (s : ℝ) (w : List ℕ) : ℝ :=
  w.foldl (fun t b => ((b : ℝ) + t)⁻¹) s

@[simp] lemma tChain_nil (s : ℝ) : tChain s [] = s := rfl

lemma tChain_concat (s : ℝ) (w : List ℕ) (b : ℕ) :
    tChain s (w ++ [b]) = ((b : ℝ) + tChain s w)⁻¹ := by
  simp [tChain, List.foldl_append]

lemma tChain_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (w : List ℕ)
    (hpos : ∀ a ∈ w, 1 ≤ a) : tChain s w ∈ Set.Icc (0 : ℝ) 1 := by
  induction w using List.reverseRecOn with
  | nil => simpa using hs
  | append_singleton u b ih =>
      have hb : 1 ≤ b := hpos b (by simp)
      have hu := ih fun a ha => hpos a (by simp [ha])
      have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      rw [tChain_concat]
      have hden : (1 : ℝ) ≤ (b : ℝ) + tChain s u := by
        have := hu.1
        linarith
      constructor
      · positivity
      · rw [inv_le_one_iff₀]
        right
        linarith

/-! ## `h_t` is a probability density on `(0,1)` -/

/-- `∫₀¹ h_t = 1` for `t ≥ 0` (antiderivative `(1+t)y/(1+ty)` — no
singularity at `t = 0`). -/
lemma setIntegral_tailDensity_one {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Set.Ioo (0 : ℝ) 1, tailDensity t y = 1 := by
  have hpos : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → (0 : ℝ) < 1 + t * y := by
    intro y hy
    nlinarith [hy.1, hy.2]
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => (1 + t) * u / (1 + t * u)) (tailDensity t y) y := by
    intro y hy
    have hne := (hpos y hy).ne'
    have h1 : HasDerivAt (fun u : ℝ => (1 + t) * u) (1 + t) y := by
      simpa using (hasDerivAt_id y).const_mul (1 + t)
    have h2 : HasDerivAt (fun u : ℝ => 1 + t * u) t y := by
      simpa using ((hasDerivAt_id y).const_mul t).const_add 1
    have h3 := h1.div h2 hne
    have heq : ((1 + t) * (1 + t * y) - (1 + t) * y * t) / (1 + t * y) ^ 2 =
        tailDensity t y := by
      rw [tailDensity]
      congr 1
      ring
    rw [heq] at h3
    exact h3
  have hcont : ContinuousOn (tailDensity t) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact ((continuous_const.add
        (continuous_const.mul continuous_id)).pow 2).continuousOn
    · intro y hy
      exact (pow_pos (hpos y hy) 2).ne'
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (huIcc ▸ hy))
      (hcont.mono huIcc.subset).intervalIntegrable]
  have h1 : (0 : ℝ) < 1 + t := by linarith
  field_simp
  ring

/-! ## The started conditional density identity -/

/-- Orbit containment junk: `I_w ∩ T^{-|w|}((0,1)) =ᵐ I_w`. -/
lemma cylinder_inter_preimage_Ioo_ae (w : List ℕ) :
    (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹' Set.Ioo (0 : ℝ) 1 : Set ℝ)
      =ᵐ[volume] cfCylinder w := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  constructor
  · rintro ⟨hcyl, -⟩
    exact hcyl
  · intro hcyl
    exact ⟨hcyl, (irrational_orbit x hirr hcyl.1 w.length).2⟩

/-- **The `s`-started conditional density identity**: for `s ∈ [0,1]`
and measurable `B ⊆ (0,1)`,
`∫_{I_w ∩ T^{-|w|}B} h_s = (∫_B h_{tChain s w}) · (∫_{I_w} h_s)`.
`s = 0` recovers `volume_inter_preimage_aux` (`h_0 = 1`). -/
theorem setIntegral_inter_preimage (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (B : Set ℝ) (hB : MeasurableSet B)
    (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1) :
    ∫ y in cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹' B, tailDensity s y =
      (∫ y in B, tailDensity (tChain s w) y) *
        ∫ y in cfCylinder w, tailDensity s y := by
  induction w using List.reverseRecOn generalizing B with
  | nil =>
      rw [cfCylinder_nil, List.length_nil, Function.iterate_zero,
        Set.preimage_id, Set.inter_eq_self_of_subset_right hB1, tChain_nil,
        setIntegral_tailDensity_one hs.1, mul_one]
  | append_singleton w b ih =>
      have hb : 1 ≤ b := hpos b (by simp)
      have hposw : ∀ a ∈ w, 1 ≤ a := fun a ha => hpos a (by simp [ha])
      have ht' := tChain_mem_Icc hs w hposw
      set A' : Set ℝ := cfCylinder [b] ∩ gaussMap ⁻¹' B with hA'
      have hA'meas : MeasurableSet A' :=
        (measurableSet_cfCylinder [b]).inter (measurable_gaussMap hB)
      have hA'1 : A' ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx => hx.1.1
      have hlen : (w ++ [b]).length = w.length + 1 := by simp
      -- the conditional integral over the extended word, any target set
      have hmain : ∀ B' : Set ℝ, MeasurableSet B' → B' ⊆ Set.Ioo (0 : ℝ) 1 →
          ∫ y in cfCylinder (w ++ [b]) ∩
            (gaussMap^[w.length + 1]) ⁻¹' B', tailDensity s y =
          ((1 + tChain s w) /
              (((b : ℝ) + tChain s w) * ((b : ℝ) + 1 + tChain s w)) *
            ∫ y in B', tailDensity (tChain s (w ++ [b])) y) *
            ∫ y in cfCylinder w, tailDensity s y := by
        intro B' hB' hB'1
        rw [setIntegral_congr_set (concat_inter_ae w b B'),
          ih hposw (cfCylinder [b] ∩ gaussMap ⁻¹' B')
            ((measurableSet_cfCylinder [b]).inter (measurable_gaussMap hB'))
            (fun x hx => hx.1.1)]
        congr 1
        rw [setIntegral_congr_set (branch_inter_ae b hb B' hB'1),
          setIntegral_tailDensity_branch b hb hB' hB'1 ht',
          tChain_concat]
      -- the cylinder mass of the extended word (`B' = (0,1)`)
      have hmass : ∫ y in cfCylinder (w ++ [b]), tailDensity s y =
          (1 + tChain s w) /
              (((b : ℝ) + tChain s w) * ((b : ℝ) + 1 + tChain s w)) *
            ∫ y in cfCylinder w, tailDensity s y := by
        calc ∫ y in cfCylinder (w ++ [b]), tailDensity s y
            = ∫ y in cfCylinder (w ++ [b]) ∩
                (gaussMap^[w.length + 1]) ⁻¹' Set.Ioo (0 : ℝ) 1,
                tailDensity s y := by
              have hae := cylinder_inter_preimage_Ioo_ae (w ++ [b])
              rw [hlen] at hae
              exact (setIntegral_congr_set hae).symm
          _ = ((1 + tChain s w) /
                (((b : ℝ) + tChain s w) * ((b : ℝ) + 1 + tChain s w)) *
                ∫ y in Set.Ioo (0 : ℝ) 1,
                  tailDensity (tChain s (w ++ [b])) y) *
                ∫ y in cfCylinder w, tailDensity s y :=
              hmain (Set.Ioo 0 1) measurableSet_Ioo (le_refl _)
          _ = (1 + tChain s w) /
                (((b : ℝ) + tChain s w) * ((b : ℝ) + 1 + tChain s w)) *
                ∫ y in cfCylinder w, tailDensity s y := by
              rw [setIntegral_tailDensity_one
                (tChain_mem_Icc hs (w ++ [b]) hpos).1, mul_one]
      rw [hlen, hmain B hB hB1, hmass]
      ring

/-! ## γ-mixing -/

lemma continuousOn_tChain (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) :
    ContinuousOn (fun s => tChain s v) (Set.Icc (0 : ℝ) 1) := by
  induction v using List.reverseRecOn with
  | nil => simpa [tChain] using continuous_id'.continuousOn
  | append_singleton u b ih =>
      have hb : 1 ≤ b := hpos b (by simp)
      have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hposu : ∀ a ∈ u, 1 ≤ a := fun a ha => hpos a (by simp [ha])
      simp only [tChain_concat]
      apply ContinuousOn.inv₀ (continuousOn_const.add (ih hposu))
      intro s hs
      have h0 := (tChain_mem_Icc hs u hposu).1
      have hgt : (0 : ℝ) < (b : ℝ) + tChain s u := by linarith
      exact hgt.ne'

/-- Splitting the horizon inside a cylinder, up to the rationals. -/
lemma cylinder_preimage_horizon_ae (v : List ℕ) (g : ℕ) (A : Set ℝ) :
    (cfCylinder v ∩ (gaussMap^[v.length + g]) ⁻¹' A : Set ℝ) =ᵐ[volume]
      (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' horizonSet A g : Set ℝ) := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  have hsplit : ∀ z : ℝ, gaussMap^[v.length + g] z =
      gaussMap^[g] (gaussMap^[v.length] z) := by
    intro z
    rw [Nat.add_comm, Function.iterate_add_apply]
  constructor
  · rintro ⟨hcyl, hTA⟩
    have horb := irrational_orbit x hirr hcyl.1 v.length
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

/-- **γ-mixing for cylinders** (the KPW Lemma-6 / correlation-decay
substitute, geometric rate): for any digit word `v` and measurable
`A ⊆ (0,1)`,

`|γ(I_v ∩ T^{-(|v|+g)}A) − γ(I_v)·γ(A)| ≤ (9/10)^g·4|A|·γ(I_v)`. -/
theorem gaussMeasure_cylinder_mixing (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a)
    (g : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    |(gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length + g]) ⁻¹' A)).toReal -
        (gaussMeasure (cfCylinder v)).toReal * (gaussMeasure A).toReal| ≤
      (9 / 10) ^ g * (4 * (volume A).toReal) *
        (gaussMeasure (cfCylinder v)).toReal := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set X : Set ℝ := cfCylinder v ∩ (gaussMap^[v.length + g]) ⁻¹' A with hX
  have hXmeas : MeasurableSet X :=
    (measurableSet_cfCylinder v).inter
      ((measurable_gaussMap.iterate (v.length + g)) hA)
  have hX1 : X ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx => hx.1.1
  have hVmeas : MeasurableSet (cfCylinder v) := measurableSet_cfCylinder v
  have hV1 := cfCylinder_subset_Ioo v
  set E : ℝ := (9 / 10) ^ g * (4 * (volume A).toReal) with hE
  have hE0 : 0 ≤ E := by
    have := ENNReal.toReal_nonneg (a := volume A)
    positivity
  -- notation
  set τ : ℝ → ℝ := fun s => tChain s v with hτ
  set M : ℝ → ℝ := fun s => ∫ y in cfCylinder v, tailDensity s y with hM
  set G : ℝ → ℝ := horizonIntegral A g with hGdef
  set gA : ℝ := (gaussMeasure A).toReal with hgA
  -- the two mixture representations
  have hmixX : (gaussMeasure X).toReal =
      ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * ∫ y in X, tailDensity s y :=
    by rw [gaussMeasure_toReal_eq hXmeas hX1,
      integral_gaussDensityReal_eq_mix hXmeas hX1]
  have hmixV : (gaussMeasure (cfCylinder v)).toReal =
      ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * M s :=
    by rw [gaussMeasure_toReal_eq hVmeas hV1,
      integral_gaussDensityReal_eq_mix hVmeas hV1]
  -- the conditional factorization of the inner integral
  have hfact : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∫ y in X, tailDensity s y = G (τ s) * M s := by
    intro s hs
    rw [hX, setIntegral_congr_set (cylinder_preimage_horizon_ae v g A),
      setIntegral_inter_preimage v hpos hs (horizonSet A g)
        (measurableSet_horizonSet hA g) (horizonSet_subset A g)]
    rfl
  -- continuity ingredients
  have hcontw : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have hcontM : ContinuousOn M (Set.Icc (0 : ℝ) 1) := by
    have h := continuousOn_horizonIntegral hVmeas hV1 0
    have hB0 : horizonSet (cfCylinder v) 0 = cfCylinder v := by
      rw [horizonSet, Function.iterate_zero, Set.preimage_id,
        Set.inter_eq_self_of_subset_right hV1]
    have heq : M = horizonIntegral (cfCylinder v) 0 := by
      funext s
      rw [hM, horizonIntegral, hB0]
    rw [heq]
    exact h
  have hcontτ := continuousOn_tChain v hpos
  have hτmap : Set.MapsTo τ (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => tChain_mem_Icc hs v hpos
  have hcontG : ContinuousOn (fun s => G (τ s)) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_horizonIntegral hA hA1 g).comp hcontτ hτmap
  have hcont1 : ContinuousOn (fun s => gaussDensityReal s * (G (τ s) * M s))
      (Set.Icc (0 : ℝ) 1) := hcontw.mul (hcontG.mul hcontM)
  have hcont2 : ContinuousOn (fun s => gA * (gaussDensityReal s * M s))
      (Set.Icc (0 : ℝ) 1) := continuousOn_const.mul (hcontw.mul hcontM)
  have hint1 : IntegrableOn (fun s => gaussDensityReal s * (G (τ s) * M s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    (hcont1.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun s => gA * (gaussDensityReal s * M s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    (hcont2.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  -- the difference as one integral
  have hdiff : (gaussMeasure X).toReal -
      (gaussMeasure (cfCylinder v)).toReal * gA =
      ∫ s in Set.Ioo (0 : ℝ) 1,
        gaussDensityReal s * M s * (G (τ s) - gA) := by
    rw [hmixX, hmixV]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun s hs => by
      rw [hfact s (Set.Ioo_subset_Icc_self hs)])]
    rw [show (∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * M s) * gA =
        ∫ s in Set.Ioo (0 : ℝ) 1, gA * (gaussDensityReal s * M s) by
      rw [integral_const_mul]; ring]
    rw [← integral_sub hint1 hint2]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s _
    ring
  -- bound the integrand by `E · (w·M)` and integrate
  have hMnn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M s := by
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
      |gaussDensityReal s * M s * (G (τ s) - gA)| ≤
        E * (gaussDensityReal s * M s) := by
    intro s hs
    have hs' := Set.Ioo_subset_Icc_self hs
    have hpin := abs_horizonIntegral_sub_gauss hA hA1 g (hτmap hs')
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hwnn s hs') (hMnn s hs'))]
    calc gaussDensityReal s * M s * |G (τ s) - gA| ≤
        gaussDensityReal s * M s * E := by
          apply mul_le_mul_of_nonneg_left hpin
            (mul_nonneg (hwnn s hs') (hMnn s hs'))
      _ = E * (gaussDensityReal s * M s) := by ring
  have hintabs : IntegrableOn
      (fun s => |gaussDensityReal s * M s * (G (τ s) - gA)|)
      (Set.Ioo (0 : ℝ) 1) volume := by
    have : ContinuousOn
        (fun s => |gaussDensityReal s * M s * (G (τ s) - gA)|)
        (Set.Icc (0 : ℝ) 1) :=
      (hcontw.mul hcontM |>.mul (hcontG.sub continuousOn_const)).abs
    exact (this.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hintwM : IntegrableOn (fun s => E * (gaussDensityReal s * M s))
      (Set.Ioo (0 : ℝ) 1) volume :=
    ((continuousOn_const.mul (hcontw.mul hcontM)).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  rw [hdiff]
  calc |∫ s in Set.Ioo (0 : ℝ) 1,
        gaussDensityReal s * M s * (G (τ s) - gA)| ≤
      ∫ s in Set.Ioo (0 : ℝ) 1,
        |gaussDensityReal s * M s * (G (τ s) - gA)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
          (fun s => gaussDensityReal s * M s * (G (τ s) - gA))
    _ ≤ ∫ s in Set.Ioo (0 : ℝ) 1, E * (gaussDensityReal s * M s) :=
        setIntegral_mono_on hintabs hintwM measurableSet_Ioo habs
    _ = E * (gaussMeasure (cfCylinder v)).toReal := by
        rw [integral_const_mul, hmixV]
    _ = (9 / 10) ^ g * (4 * (volume A).toReal) *
        (gaussMeasure (cfCylinder v)).toReal := by rw [hE]

end NormalNumbers
