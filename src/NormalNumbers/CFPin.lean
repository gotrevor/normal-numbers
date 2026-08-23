/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFRecursion
import NormalNumbers.CFInvariance

/-!
# W3 — the mean pin (route step 2, part 2)

`G_k(t)` contracts to a constant (`horizonIntegral_lipschitz`); this file
pins the constant to `γ(A)`.  The mixture identity
`∫₀¹ h_s(y) · ds/((1+s) log 2) = 1/((1+y) log 2)` expresses the Gauss
density as the `γ`-average of the conditional family, so by Fubini

  `∫₀¹ G_k(s) dλ(s) = γ(B_k) = γ(A)`   (`λ(ds) = ds/((1+s) log 2)`, mass 1)

and since `λ` is a probability measure on `[0,1]`,

  `|G_k(t) − γ(A)| = |∫ (G_k(t) − G_k(s)) dλ(s)| ≤ Lip(G_k) ≤ (9/10)ᵏ·2|A|`.
-/

namespace NormalNumbers

open MeasureTheory

/-- The real Gauss density. -/
noncomputable def gaussDensityReal (y : ℝ) : ℝ := ((1 + y) * Real.log 2)⁻¹

/-! ## `γ` of the horizon set -/

lemma gaussMeasure_inter_Ioo {S : Set ℝ} (hS : MeasurableSet S) :
    gaussMeasure (Set.Ioo 0 1 ∩ S) = gaussMeasure S := by
  rw [gaussMeasure_apply (measurableSet_Ioo.inter hS), gaussMeasure_apply hS]
  congr 1
  rw [Set.inter_comm (Set.Ioo 0 1) S, Set.inter_assoc, Set.inter_self]

lemma gaussMeasure_preimage_iterate {S : Set ℝ} (hS : MeasurableSet S)
    (k : ℕ) : gaussMeasure ((gaussMap^[k]) ⁻¹' S) = gaussMeasure S := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ, Set.preimage_comp,
        gaussMeasure_preimage ((measurable_gaussMap.iterate m) hS), ih]

/-- `γ(B_k) = γ(A)`: invariance transports the Gauss mass along the
horizon. -/
lemma gaussMeasure_horizonSet {A : Set ℝ} (hA : MeasurableSet A) (k : ℕ) :
    gaussMeasure (horizonSet A k) = gaussMeasure A := by
  rw [horizonSet, gaussMeasure_inter_Ioo ((measurable_gaussMap.iterate k) hA),
    gaussMeasure_preimage_iterate hA k]

/-! ## `γ` as a real integral -/

lemma integrableOn_gaussDensityReal {B : Set ℝ}
    (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1) :
    IntegrableOn gaussDensityReal B volume := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have hy0 := hy.1
      positivity
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set
    (hB1.trans Set.Ioo_subset_Icc_self)

/-- `γ(B) = ∫_B dy/((1+y) log 2)` in real form, for `B ⊆ (0,1)`. -/
lemma gaussMeasure_toReal_eq {B : Set ℝ} (hB : MeasurableSet B)
    (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1) :
    (gaussMeasure B).toReal = ∫ y in B, gaussDensityReal y := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ᵐ[volume.restrict B] gaussDensityReal := by
    filter_upwards [ae_restrict_mem hB] with y hy
    have hy0 := (hB1 hy).1
    simp only [gaussDensityReal]
    positivity
  have h := ofReal_integral_eq_lintegral_ofReal
    (integrableOn_gaussDensityReal hB1) hnn
  rw [gaussMeasure_apply hB, Set.inter_eq_self_of_subset_left hB1]
  simp only [gaussDensity]
  simp only [gaussDensityReal] at h ⊢
  rw [← h, ENNReal.toReal_ofReal]
  apply setIntegral_nonneg hB
  intro y hy
  have hy0 := (hB1 hy).1
  positivity

/-! ## The mixture identity (slice integrals) -/

/-- `∫₀¹ ds/(1+sy)² = 1/(1+y)` for `y ∈ (0,1)`. -/
lemma integral_mix_kernel {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ s in Set.Ioo (0 : ℝ) 1, ((1 + s * y) ^ 2)⁻¹ = (1 + y)⁻¹ := by
  obtain ⟨hy0, hy1⟩ := hy
  have hpos : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (0 : ℝ) < 1 + s * y := by
    intro s hs
    nlinarith [hs.1, hs.2]
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => -(y⁻¹) * (1 + u * y)⁻¹) (((1 + s * y) ^ 2)⁻¹) s := by
    intro s hs
    have h1 : HasDerivAt (fun u : ℝ => 1 + u * y) y s := by
      simpa using ((hasDerivAt_id s).mul_const y).const_add 1
    have h2 := h1.inv (hpos s hs).ne'
    have h3 := h2.const_mul (-(y⁻¹))
    have heq : -(y⁻¹) * (-y / (1 + s * y) ^ 2) = ((1 + s * y) ^ 2)⁻¹ := by
      field_simp
    rw [heq] at h3
    exact h3
  have hcont : ContinuousOn (fun s : ℝ => ((1 + s * y) ^ 2)⁻¹)
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact (((continuous_const.add (continuous_id.mul continuous_const))).pow
        2).continuousOn
    · intro s hs
      exact (pow_pos (hpos s hs) 2).ne'
  have hIoc : (Set.Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] Set.Ioc (0 : ℝ) 1 :=
    Ioo_ae_eq_Ioc
  rw [setIntegral_congr_set hIoc, ← intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hderiv s (by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      at hs)) ((hcont.mono (by rw [Set.uIcc_of_le
        (by norm_num : (0:ℝ) ≤ 1)])).intervalIntegrable)]
  have h10 : (0 : ℝ) < 1 + y := by linarith
  field_simp
  ring

/-- The mixing weight has mass one: `∫₀¹ ds/((1+s) log 2) = 1`. -/
lemma integral_mix_weight :
    ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s = 1 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => Real.log (1 + u) * (Real.log 2)⁻¹)
      (gaussDensityReal s) s := by
    intro s hs
    have h0 : (0 : ℝ) < 1 + s := by linarith [hs.1]
    have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 s := by
      simpa using (hasDerivAt_id s).const_add 1
    have h2 := (h1.log h0.ne').mul_const (Real.log 2)⁻¹
    have heq : 1 / (1 + s) * (Real.log 2)⁻¹ = gaussDensityReal s := by
      simp only [gaussDensityReal]
      field_simp
    rw [heq] at h2
    exact h2
  have hcont : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hderiv s (huIcc ▸ hs))
      (hcont.mono huIcc.subset).intervalIntegrable]
  norm_num [Real.log_one]

/-! ## Fubini: the γ-average of `G_k` -/

/-- **The mixture Fubini**: for measurable `B ⊆ (0,1)`,
`∫_B dγ/dy = ∫₀¹ (∫_B h_s) dλ(s)` with `λ(ds) = ds/((1+s) log 2)`. -/
lemma integral_gaussDensityReal_eq_mix {B : Set ℝ} (hB : MeasurableSet B)
    (hB1 : B ⊆ Set.Ioo (0 : ℝ) 1) :
    ∫ y in B, gaussDensityReal y =
      ∫ s in Set.Ioo (0 : ℝ) 1,
        gaussDensityReal s * ∫ y in B, tailDensity s y := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set f : ℝ → ℝ → ℝ :=
    fun s y => (Real.log 2)⁻¹ * ((1 + s * y) ^ 2)⁻¹ with hf
  have hmeas : Measurable (Function.uncurry f) := by
    apply Measurable.const_mul
    apply Measurable.inv
    apply Measurable.pow_const
    exact measurable_const.add (measurable_fst.mul measurable_snd)
  have hintf : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict B)) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; simp [Real.volume_Ioo]⟩
    have : IsFiniteMeasure (volume.restrict B) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hB1) (by simp [Real.volume_Ioo])⟩
    apply Integrable.mono' (g := fun _ => (Real.log 2)⁻¹)
      (integrable_const _) hmeas.aestronglyMeasurable
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hB)] with p hp
    obtain ⟨hs, hy⟩ := hp
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨hy0, hy1⟩ := hB1 hy
    have h1 : (1 : ℝ) ≤ 1 + p.1 * p.2 := by nlinarith
    rw [Function.uncurry, hf, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ((1 + p.1 * p.2) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; nlinarith
    calc (Real.log 2)⁻¹ * ((1 + p.1 * p.2) ^ 2)⁻¹ ≤ (Real.log 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (Real.log 2)⁻¹ := mul_one _
  have hswap := integral_integral_swap hintf
  calc ∫ y in B, gaussDensityReal y
      = ∫ y in B, ∫ s in Set.Ioo (0 : ℝ) 1, f s y := by
        apply setIntegral_congr_fun hB
        intro y hy
        obtain ⟨hy0, hy1⟩ := hB1 hy
        rw [hf]
        simp only
        rw [integral_const_mul, integral_mix_kernel (hB1 hy),
          gaussDensityReal, mul_inv]
        ring
    _ = ∫ s in Set.Ioo (0 : ℝ) 1, ∫ y in B, f s y := hswap.symm
    _ = ∫ s in Set.Ioo (0 : ℝ) 1,
          gaussDensityReal s * ∫ y in B, tailDensity s y := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        obtain ⟨hs0, hs1⟩ := hs
        rw [hf]
        simp only
        rw [← integral_const_mul]
        apply setIntegral_congr_fun hB
        intro y hy
        simp only [gaussDensityReal, tailDensity]
        have h1s : (0 : ℝ) < 1 + s := by linarith
        field_simp

/-- **The mean pin**: `∫₀¹ G_k(s) dλ(s) = γ(A)` in real form. -/
lemma integral_horizonIntegral_eq_gauss {A : Set ℝ} (hA : MeasurableSet A)
    (_hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * horizonIntegral A k s =
      (gaussMeasure A).toReal := by
  rw [← gaussMeasure_horizonSet hA k,
    gaussMeasure_toReal_eq (measurableSet_horizonSet hA k)
      (horizonSet_subset A k),
    integral_gaussDensityReal_eq_mix (measurableSet_horizonSet hA k)
      (horizonSet_subset A k)]
  rfl

/-! ## The pin bound -/

/-- `G_k` is continuous on `[0,1]` (it is Lipschitz there). -/
lemma continuousOn_horizonIntegral {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    ContinuousOn (horizonIntegral A k) (Set.Icc (0 : ℝ) 1) := by
  set L : ℝ := (9 / 10) ^ k * (2 * (volume A).toReal) with hL
  have hL0 : 0 ≤ L := by
    have := ENNReal.toReal_nonneg (a := volume A)
    positivity
  apply LipschitzOnWith.continuousOn (K := Real.toNNReal L)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq]
  calc |horizonIntegral A k x - horizonIntegral A k y| ≤ L * |x - y| :=
        horizonIntegral_lipschitz hA hA1 k hx hy
    _ = (Real.toNNReal L : ℝ) * |x - y| := by
        rw [Real.coe_toNNReal L hL0]

/-- **The pin**: `G_k(t)` is within `(9/10)ᵏ·4|A|` of `γ(A)`, uniformly
on `[0,1]`. -/
theorem abs_horizonIntegral_sub_gauss {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |horizonIntegral A k t - (gaussMeasure A).toReal| ≤
      (9 / 10) ^ k * (4 * (volume A).toReal) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set G : ℝ → ℝ := horizonIntegral A k with hG
  set L : ℝ := (9 / 10) ^ k * (2 * (volume A).toReal) with hL
  have hL0 : 0 ≤ L := by
    have := ENNReal.toReal_nonneg (a := volume A)
    positivity
  -- integrabilities on (0,1)
  have hIoofin : volume (Set.Ioo (0 : ℝ) 1) < ⊤ := by simp [Real.volume_Ioo]
  have hwint : IntegrableOn gaussDensityReal (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_gaussDensityReal (le_refl _)
  have hcontw : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have hwG : IntegrableOn (fun s => gaussDensityReal s * G s)
      (Set.Ioo (0 : ℝ) 1) volume :=
    ((hcontw.mul (continuousOn_horizonIntegral hA hA1 k)).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hwGt : IntegrableOn (fun s => gaussDensityReal s * G t)
      (Set.Ioo (0 : ℝ) 1) volume := hwint.mul_const _
  -- the difference identity
  have hdiff : G t - (gaussMeasure A).toReal =
      ∫ s in Set.Ioo (0 : ℝ) 1,
        gaussDensityReal s * (G t - G s) := by
    have h1 : G t = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G t := by
      rw [integral_mul_const, integral_mix_weight, one_mul]
    rw [← integral_horizonIntegral_eq_gauss hA hA1 k]
    calc G t - ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G s
        = (∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G t) -
            ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G s := by
          rw [← h1]
      _ = ∫ s in Set.Ioo (0 : ℝ) 1,
            (gaussDensityReal s * G t - gaussDensityReal s * G s) :=
          (integral_sub hwGt hwG).symm
      _ = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (G t - G s) := by
          simp only [mul_sub]
  -- bound the averaged difference
  rw [hdiff]
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Ioo (0 : ℝ) 1) (C := 2 * L) hIoofin (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul]
      have hs0 := hs.1
      have hw0 : 0 ≤ gaussDensityReal s := by
        rw [gaussDensityReal]; positivity
      have hw2 : gaussDensityReal s ≤ 2 := by
        rw [gaussDensityReal]
        have h12 : (1 / 2 : ℝ) ≤ (1 + s) * Real.log 2 := by
          nlinarith [Real.log_two_gt_d9, hs.1, hs.2]
        calc ((1 + s) * Real.log 2)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
              rw [inv_le_inv₀ (by nlinarith [Real.log_two_gt_d9]) (by norm_num)]
              exact h12
          _ = 2 := by norm_num
      have hGL : |G t - G s| ≤ L := by
        have h1 := horizonIntegral_lipschitz hA hA1 k ht
          (Set.Ioo_subset_Icc_self hs)
        have h2 : |t - s| ≤ 1 := by
          rw [abs_le]
          constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]
        calc |G t - G s| ≤ L * |t - s| := h1
          _ ≤ L * 1 := mul_le_mul_of_nonneg_left h2 hL0
          _ = L := mul_one L
      calc |gaussDensityReal s| * |G t - G s| ≤ 2 * L :=
        mul_le_mul (by rwa [abs_of_nonneg hw0]) hGL (abs_nonneg _) (by norm_num))
  rw [Real.norm_eq_abs] at hbound
  calc |∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (G t - G s)| ≤
      2 * L * (volume.real (Set.Ioo (0 : ℝ) 1)) := hbound
    _ = (9 / 10) ^ k * (4 * (volume A).toReal) := by
        rw [measureReal_def, Real.volume_Ioo, hL]
        norm_num
        ring

/-- Real-form comparison: `|A| ≤ 2 log 2 · γ(A)`. -/
lemma volume_toReal_le_gauss {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    (volume A).toReal ≤ 2 * Real.log 2 * (gaussMeasure A).toReal := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hAfin : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Ioo]) (measure_mono hA1)
  have hγfin : gaussMeasure A ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [gaussMeasure_univ]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ A))
  have h := volume_le_gaussMeasure A hA hA1
  have h2 := ENNReal.toReal_mono hγfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  calc (volume A).toReal =
      2 * Real.log 2 * ((2 * Real.log 2)⁻¹ * (volume A).toReal) := by
        field_simp
    _ ≤ 2 * Real.log 2 * (gaussMeasure A).toReal := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The two-sided envelope in real form**:
`(1 ± 8 log 2·(9/10)ᵏ)·γ(A)` traps `G_k(t)` on `[0,1]`. -/
theorem horizonIntegral_envelope {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - 8 * Real.log 2 * (9 / 10) ^ k) * (gaussMeasure A).toReal ≤
        horizonIntegral A k t ∧
      horizonIntegral A k t ≤
        (1 + 8 * Real.log 2 * (9 / 10) ^ k) * (gaussMeasure A).toReal := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hρ : (0 : ℝ) ≤ (9 / 10 : ℝ) ^ k := by positivity
  have hγ0 : 0 ≤ (gaussMeasure A).toReal := ENNReal.toReal_nonneg
  have hpin := abs_horizonIntegral_sub_gauss hA hA1 k ht
  have hcmp := volume_toReal_le_gauss hA hA1
  have hbound : |horizonIntegral A k t - (gaussMeasure A).toReal| ≤
      8 * Real.log 2 * (9 / 10) ^ k * (gaussMeasure A).toReal := by
    calc |horizonIntegral A k t - (gaussMeasure A).toReal| ≤
        (9 / 10) ^ k * (4 * (volume A).toReal) := hpin
      _ ≤ (9 / 10) ^ k * (4 * (2 * Real.log 2 * (gaussMeasure A).toReal)) := by
          apply mul_le_mul_of_nonneg_left _ hρ
          linarith
      _ = 8 * Real.log 2 * (9 / 10) ^ k * (gaussMeasure A).toReal := by ring
  rw [abs_le] at hbound
  constructor <;> nlinarith [hbound.1, hbound.2]

end NormalNumbers
