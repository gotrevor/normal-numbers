/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFGammaMixing

/-!
# The ψ-mixing pin: a *constant-free* geometric Gauss–Kuzmin bound

`CFPin.lean` proves `|G_k(t) − γ(A)| ≤ (9/10)^k·4|A|`, which after
`|A| ≤ 2 log 2·γ(A)` reads `|G_k(t) − γ(A)| ≤ 5.55·(9/10)^k·γ(A)`.  Philipp's
ψ-mixing statement (`Literature.philipp_psi_mixing`) demands the *constant-free*
form `≤ ρ^n·γ(A)` with `ρ < 4/5` for **every** `n ≥ 1`, and no rearrangement of a
`C·θ^n` bound with `θ = 9/10 > 4/5` can deliver that.  Two changes fix it.

* **Metric.**  Measure the `t`-regularity of `G_k` in the *log metric*
  `d(t,t') = |log(1+t) − log(1+t')|` instead of `|t − t'|`.  This is Lipschitz
  in the coordinate `τ = log(1+t)`, in which the Gauss measure on the tail
  parameter is *uniform* on `[0, log 2]` (`gaussDensityReal s · ds = dτ/log 2`).
  The transfer operator `stepOp` contracts this metric much harder than `|t−t'|`
  (the branch `t ↦ 1/(1+t)`, which costs a factor `≈ 1/2` in `|t−t'|` at `t = 0`,
  costs only `≈ 1/4` here), and the *averaging* constant improves too.

* **Constants.**  In the log metric the base Lipschitz constant of `G_0` is
  `2 log 2·γ(A)` (`horizonIntegral_zero_logLip`) and the mean-pin averaging
  factor is `≤ log 2 / 2` (`integral_gaussDensity_mul_abs_log_sub_le`, exactly the
  uniform-coordinate computation `∫₀^L |a−τ| dτ/L = (a² + (L−a)²)/(2L) ≤ L/2`).
  Their product is `(log 2)² < 1`, so the pin is
  `|G_k(t) − γ(A)| ≤ θ^k·(log 2)²·γ(A) ≤ θ^k·γ(A)` — constant-free.

The one analytic input is the log-metric contraction `stepOp_logLipschitz`.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## The exact `tailDensity` difference and its log-metric bound -/

/-- The exact difference of two tail densities.  The numerator factors as
`(t − t')·(1 − 2y − y²(t + t' + tt'))`. -/
lemma tailDensity_sub_eq {t t' y : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (hy : 0 ≤ y) :
    tailDensity t y - tailDensity t' y =
      (t - t') * (1 - 2 * y - y ^ 2 * (t + t' + t * t')) /
        ((1 + t * y) ^ 2 * (1 + t' * y) ^ 2) := by
  have h1 : (0 : ℝ) < 1 + t * y := by nlinarith [mul_nonneg ht hy]
  have h2 : (0 : ℝ) < 1 + t' * y := by nlinarith [mul_nonneg ht' hy]
  rw [tailDensity, tailDensity]
  field_simp
  ring

/-- Ordered half of the log-metric bound. -/
private lemma abs_tailDensity_sub_le_log_aux {t t' y : ℝ} (ht0 : 0 ≤ t') (htt' : t' ≤ t)
    (ht1 : t ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |tailDensity t y - tailDensity t' y| ≤
      2 / (1 + y) * |Real.log (1 + t) - Real.log (1 + t')| := by
  have ht0' : (0 : ℝ) ≤ t := le_trans ht0 htt'
  have ht1' : t' ≤ 1 := le_trans htt' ht1
  have hty : (0 : ℝ) ≤ t * y := mul_nonneg ht0' hy0
  have hty' : (0 : ℝ) ≤ t' * y := mul_nonneg ht0 hy0
  have h1 : (0 : ℝ) < 1 + t * y := by linarith
  have h2 : (0 : ℝ) < 1 + t' * y := by linarith
  have hy : (0 : ℝ) < 1 + y := by linarith
  have ht1p : (0 : ℝ) < 1 + t := by linarith
  have ht1p' : (0 : ℝ) < 1 + t' := by linarith
  set P : ℝ := (1 + t * y) * (1 + t' * y) with hP
  have hP1 : (1 : ℝ) ≤ P := by rw [hP]; nlinarith
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le one_pos hP1
  set N : ℝ := 1 - 2 * y - y ^ 2 * (t + t' + t * t') with hN
  -- the two structural inequalities
  have hfac : (1 + y) * (1 + t) ≤ 2 * P := by
    rw [hP]; nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr ht1),
      mul_nonneg hty' (le_of_lt hy), mul_nonneg (mul_nonneg ht0 hy0) hty]
  have hbr : -N ≤ P := by
    rw [hN, hP]
    nlinarith [mul_nonneg (mul_nonneg ht0' hy0) (sub_nonneg.mpr hy1),
      mul_nonneg (mul_nonneg ht0 hy0) (sub_nonneg.mpr hy1),
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ht0' ht0) hy0) hy0)
        (sub_nonneg.mpr hy1), sub_nonneg.mpr hy1]
  have hNle : N ≤ 1 := by
    rw [hN]
    nlinarith [mul_nonneg (mul_nonneg hy0 hy0) (by nlinarith : (0:ℝ) ≤ t + t' + t * t')]
  -- |N|·(1+y)(1+t) ≤ 2P²
  have hkey : (1 + y) * (1 + t) * |N| ≤ 2 * (P * P) := by
    rcases abs_cases N with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [habs]
      calc (1 + y) * (1 + t) * N ≤ (1 + y) * (1 + t) * 1 := by
            apply mul_le_mul_of_nonneg_left hNle (by positivity)
        _ = (1 + y) * (1 + t) := mul_one _
        _ ≤ 2 * P := hfac
        _ ≤ 2 * (P * P) := by nlinarith
    · rw [habs]
      calc (1 + y) * (1 + t) * -N ≤ (2 * P) * P := by
            apply mul_le_mul hfac hbr (by linarith [abs_nonneg N, habs]) (by positivity)
        _ = 2 * (P * P) := by ring
  -- the log lower bound
  have hlog : (t - t') / (1 + t) ≤ Real.log (1 + t) - Real.log (1 + t') := by
    have hx : (0 : ℝ) < (1 + t') / (1 + t) := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (ne_of_gt ht1p') (ne_of_gt ht1p)] at h
    have hr : (1 + t') / (1 + t) - 1 = (t' - t) / (1 + t) := by field_simp; ring
    rw [hr] at h
    have : -(( t' - t) / (1 + t)) ≤ -(Real.log (1 + t') - Real.log (1 + t)) := by linarith
    calc (t - t') / (1 + t) = -((t' - t) / (1 + t)) := by ring
      _ ≤ -(Real.log (1 + t') - Real.log (1 + t)) := this
      _ = Real.log (1 + t) - Real.log (1 + t') := by ring
  have hlog0 : 0 ≤ (t - t') / (1 + t) := by
    apply div_nonneg (by linarith) (le_of_lt ht1p)
  -- assemble
  have hmid : |tailDensity t y - tailDensity t' y| ≤ 2 / (1 + y) * ((t - t') / (1 + t)) := by
    rw [tailDensity_sub_eq ht0' ht0 hy0, abs_div, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr htt'), abs_of_pos (by positivity : (0:ℝ) < (1 + t * y) ^ 2 * (1 + t' * y) ^ 2)]
    rw [show 2 / (1 + y) * ((t - t') / (1 + t)) = (2 * (t - t')) / ((1 + y) * (1 + t)) by
      field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (1 + t * y) ^ 2 * (1 + t' * y) ^ 2 = P * P := by rw [hP]; ring
    rw [hsq]
    nlinarith [hkey, sub_nonneg.mpr htt', abs_nonneg N, mul_pos hP0 hP0]
  refine hmid.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hlog.trans (le_abs_self _)

/-- **Log-metric pointwise bound**: `|h_t(y) − h_{t'}(y)| ≤ 2/(1+y)·d(t,t')`
with `d` the log metric.  Sharp at `(y,t,t') = (1,0,0)` and `(0,1,1)`. -/
lemma abs_tailDensity_sub_le_log {t t' y : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ht' : t' ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailDensity t y - tailDensity t' y| ≤
      2 / (1 + y) * |Real.log (1 + t) - Real.log (1 + t')| := by
  rcases le_total t' t with h | h
  · exact abs_tailDensity_sub_le_log_aux ht'.1 h ht.2 hy.1 hy.2
  · rw [abs_sub_comm, abs_sub_comm (Real.log (1 + t))]
    exact abs_tailDensity_sub_le_log_aux ht.1 h ht'.2 hy.1 hy.2


/-! ## The base log-Lipschitz constant of `G₀` -/

/-- `(1+y)⁻¹ = log 2 · gaussDensityReal y`. -/
lemma inv_one_add_eq_log_mul_gaussDensityReal (y : ℝ) :
    2 / (1 + y) = 2 * Real.log 2 * gaussDensityReal y := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [gaussDensityReal]
  rcases eq_or_ne (1 + y) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- **`G₀` is `2 log 2·γ(A)`-Lipschitz in the log metric.** -/
lemma horizonIntegral_zero_logLip {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |horizonIntegral A 0 t - horizonIntegral A 0 t'| ≤
      2 * Real.log 2 * (gaussMeasure A).toReal *
        |Real.log (1 + t) - Real.log (1 + t')| := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := |Real.log (1 + t) - Real.log (1 + t')| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hB0 : horizonSet A 0 = A := by
    rw [horizonSet, Function.iterate_zero, Set.preimage_id,
      Set.inter_eq_self_of_subset_right hA1]
  have hint : IntegrableOn (tailDensity t) A volume :=
    (integrableOn_tailDensity ht.1).mono_set hA1
  have hint' : IntegrableOn (tailDensity t') A volume :=
    (integrableOn_tailDensity ht'.1).mono_set hA1
  have hg : IntegrableOn (fun y => 2 * Real.log 2 * δ * gaussDensityReal y) A volume :=
    (integrableOn_gaussDensityReal hA1).const_mul _
  rw [horizonIntegral, horizonIntegral, hB0, ← integral_sub hint hint']
  calc |∫ y in A, (tailDensity t y - tailDensity t' y)|
      ≤ ∫ y in A, |tailDensity t y - tailDensity t' y| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict A)
          (fun y => tailDensity t y - tailDensity t' y)
    _ ≤ ∫ y in A, 2 * Real.log 2 * δ * gaussDensityReal y := by
        refine setIntegral_mono_on ((hint.sub hint').abs) hg hA ?_
        intro y hy
        have hy' : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self (hA1 hy)
        have h := abs_tailDensity_sub_le_log ht ht' hy'
        rw [inv_one_add_eq_log_mul_gaussDensityReal] at h
        calc |tailDensity t y - tailDensity t' y|
            ≤ 2 * Real.log 2 * gaussDensityReal y * δ := h
          _ = 2 * Real.log 2 * δ * gaussDensityReal y := by ring
    _ = 2 * Real.log 2 * (gaussMeasure A).toReal * δ := by
        rw [integral_const_mul, ← gaussMeasure_toReal_eq hA hA1]; ring

/-! ## The contraction (crux) -/

/-- **CRUX (open).**  One-step contraction of `stepOp` in the log metric
`d(t,t') = |log(1+t) − log(1+t')|`, with factor `3/4`.

Numerically the true factor is `≈ 0.51`: splitting
`stepOp φ t − stepOp φ t' = Σ A_k + Σ B_k` exactly as in `stepOp_lipschitz`
(`CFContraction.lean`), the `A`-series contributes
`Σ_k w_k(t)·c_k` with `c_k = sup_{s∈[0,1]} (1+s)/((k+1+s)(k+2+s)) ≤ 1/2`
(the `log`-metric image of the branch gap), total `≈ 0.29`; the Abel-resummed
`B`-series contributes `≈ 0.22` through the closed form
`gTail t t' k = (1+t)/(k+1+t) − (1+t')/(k+1+t')`, whose `t`-derivative is
`k/(k+1+t)²`, i.e. `≤ 1/4·d(t,t')` uniformly.  `3/4` is deliberately loose.

Any factor `< 79/100` suffices downstream (`horizonIntegral_pin_geom`). -/
theorem stepOp_logLipschitz {φ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |φ x - φ y| ≤ L * |Real.log (1 + x) - Real.log (1 + y)|)
    {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |stepOp φ t - stepOp φ t'| ≤
      3 / 4 * L * |Real.log (1 + t) - Real.log (1 + t')| := by
  sorry

/-- **Geometric log-Lipschitz decay** of `G_k`, factor `3/4` per step. -/
theorem horizonIntegral_logLip {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |horizonIntegral A k t - horizonIntegral A k t'| ≤
      (3 / 4) ^ k * (2 * Real.log 2 * (gaussMeasure A).toReal) *
        |Real.log (1 + t) - Real.log (1 + t')| := by
  induction k generalizing t t' with
  | zero => simpa using horizonIntegral_zero_logLip hA hA1 ht ht'
  | succ m ih =>
      rw [horizonIntegral_succ A hA m ht, horizonIntegral_succ A hA m ht']
      have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hL : (0 : ℝ) ≤ (3 / 4) ^ m * (2 * Real.log 2 * (gaussMeasure A).toReal) := by
        have := ENNReal.toReal_nonneg (a := gaussMeasure A)
        positivity
      have h := stepOp_logLipschitz hL (fun x hx y hy => ih hx hy) ht ht'
      calc |stepOp (horizonIntegral A m) t - stepOp (horizonIntegral A m) t'| ≤
          3 / 4 * ((3 / 4) ^ m * (2 * Real.log 2 * (gaussMeasure A).toReal)) *
            |Real.log (1 + t) - Real.log (1 + t')| := h
        _ = (3 / 4) ^ (m + 1) * (2 * Real.log 2 * (gaussMeasure A).toReal) *
            |Real.log (1 + t) - Real.log (1 + t')| := by rw [pow_succ]; ring


/-! ## The mean-pin averaging factor in the log metric -/

private lemma hasDerivAt_logAntider (a : ℝ) {s : ℝ} (hs : -1 < s) :
    HasDerivAt
      (fun u : ℝ => (a * Real.log (1 + u) - Real.log (1 + u) * Real.log (1 + u) / 2) / Real.log 2)
      (gaussDensityReal s * (a - Real.log (1 + s))) s := by
  have h0 : (0 : ℝ) < 1 + s := by linarith
  have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 s := by
    simpa using (hasDerivAt_id s).const_add 1
  have hl : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + s)) s := by
    simpa [one_div] using h1.log h0.ne'
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : HasDerivAt (fun u : ℝ => a * Real.log (1 + u)) (a * (1 / (1 + s))) s :=
    hl.const_mul a
  have h3 : HasDerivAt (fun u : ℝ => Real.log (1 + u) * Real.log (1 + u) / 2)
      (Real.log (1 + s) * (1 / (1 + s))) s := by
    have h := (hl.mul hl).div_const 2
    rw [show (1 / (1 + s) * Real.log (1 + s) + Real.log (1 + s) * (1 / (1 + s))) / 2
        = Real.log (1 + s) * (1 / (1 + s)) by ring] at h
    exact h
  have h4 : HasDerivAt
      (fun u : ℝ => (a * Real.log (1 + u) - Real.log (1 + u) * Real.log (1 + u) / 2) / Real.log 2)
      ((a * (1 / (1 + s)) - Real.log (1 + s) * (1 / (1 + s))) / Real.log 2) s :=
    (h2.sub h3).div_const _
  have hval : gaussDensityReal s * (a - Real.log (1 + s))
      = (a * (1 / (1 + s)) - Real.log (1 + s) * (1 / (1 + s))) / Real.log 2 := by
    simp only [gaussDensityReal]
    field_simp
  rw [hval]
  exact h4

/-- **The log-metric averaging factor**: in the coordinate `τ = log(1+s)` the
Gauss measure is uniform on `[0, log 2]`, so
`∫ |a − τ| dτ/log 2 = (a² + (log 2 − a)²)/(2 log 2) ≤ log 2 / 2`. -/
lemma integral_gaussDensity_mul_abs_log_sub_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ s in Set.Ioo (0 : ℝ) 1,
        gaussDensityReal s * |Real.log (1 + t) - Real.log (1 + s)| ≤ Real.log 2 / 2 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨ht0, ht1⟩ := ht
  set a : ℝ := Real.log (1 + t) with hadef
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  have haL : a ≤ Real.log 2 := by
    rw [hadef]
    exact Real.log_le_log (by linarith) (by linarith)
  set f : ℝ → ℝ := fun s => gaussDensityReal s * |a - Real.log (1 + s)| with hf
  have hcontw : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have hcontlog : ContinuousOn (fun s : ℝ => Real.log (1 + s)) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro y hy; have := hy.1; linarith
  have hcontf : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    hcontw.mul ((continuousOn_const.sub hcontlog).abs)
  -- to an interval integral
  have hconv : ∫ s in Set.Ioo (0 : ℝ) 1, f s = ∫ s in (0 : ℝ)..1, f s := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hsub01 : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le ht0]; exact Set.Icc_subset_Icc le_rfl ht1
  have hsub02 : Set.uIcc t (1 : ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le ht1]; exact Set.Icc_subset_Icc ht0 le_rfl
  have hii1 : IntervalIntegrable f volume 0 t :=
    (hcontf.mono hsub01).intervalIntegrable
  have hii2 : IntervalIntegrable f volume t 1 :=
    (hcontf.mono hsub02).intervalIntegrable
  have hsplit : (∫ s in (0:ℝ)..t, f s) + (∫ s in t..(1:ℝ), f s) = ∫ s in (0:ℝ)..1, f s :=
    intervalIntegral.integral_add_adjacent_intervals hii1 hii2
  -- piece 1
  have hpiece1 : ∫ s in (0:ℝ)..t, f s = a ^ 2 / (2 * Real.log 2) := by
    have hcongr : ∫ s in (0:ℝ)..t, f s
        = ∫ s in (0:ℝ)..t, gaussDensityReal s * (a - Real.log (1 + s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' := hsub01 hs
      have : Real.log (1 + s) ≤ a := by
        rw [hadef]
        exact Real.log_le_log (by linarith [hs'.1]) (by
          rw [Set.uIcc_of_le ht0] at hs; linarith [hs.2])
      rw [hf]
      simp only
      rw [abs_of_nonneg (by linarith)]
    rw [hcongr]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => (a * Real.log (1 + u) - Real.log (1 + u) * Real.log (1 + u) / 2) / Real.log 2)
      (fun s hs => hasDerivAt_logAntider a (by
        have := hsub01 hs; linarith [this.1]))
      (by
        apply ContinuousOn.intervalIntegrable
        exact ((hcontw.mul (continuousOn_const.sub hcontlog)).mono hsub01))]
    simp only [← hadef]
    rw [show (1 : ℝ) + 0 = 1 by ring, Real.log_one]
    field_simp
    ring
  -- piece 2
  have hpiece2 : ∫ s in t..(1:ℝ), f s
      = Real.log 2 / 2 - a + a ^ 2 / (2 * Real.log 2) := by
    have hcongr : ∫ s in t..(1:ℝ), f s
        = ∫ s in t..(1:ℝ), -(gaussDensityReal s * (a - Real.log (1 + s))) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' := hsub02 hs
      have : a ≤ Real.log (1 + s) := by
        rw [hadef]
        exact Real.log_le_log (by linarith) (by
          rw [Set.uIcc_of_le ht1] at hs; linarith [hs.1])
      rw [hf]
      simp only
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hcongr]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => -((a * Real.log (1 + u) - Real.log (1 + u) * Real.log (1 + u) / 2) / Real.log 2))
      (fun s hs => (hasDerivAt_logAntider a (by
        have := hsub02 hs; linarith [this.1])).neg)
      (by
        apply ContinuousOn.intervalIntegrable
        exact (((hcontw.mul (continuousOn_const.sub hcontlog)).neg).mono hsub02))]
    simp only [← hadef]
    rw [show (1 : ℝ) + 1 = 2 by ring]
    field_simp
    ring
  rw [hconv, ← hsplit, hpiece1, hpiece2]
  have hkey : a ^ 2 / (2 * Real.log 2) + (Real.log 2 / 2 - a + a ^ 2 / (2 * Real.log 2))
      = Real.log 2 / 2 + (a ^ 2 - a * Real.log 2) / Real.log 2 := by
    field_simp; ring
  rw [hkey]
  have : (a ^ 2 - a * Real.log 2) / Real.log 2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hlog.le
    nlinarith
  linarith


/-! ## The constant-free pin -/

/-- **The ψ-mixing pin**: `|G_k(t) − γ(A)| ≤ (79/100)^k·γ(A)`, uniformly in
`t ∈ [0,1]` — *no* multiplicative constant, and `79/100 < 4/5`.  The true
bound proved here is `(3/4)^k·(log 2)²·γ(A)`; the slack absorbs both a lossy
contraction factor and the `(log 2)² < 1` head constant. -/
theorem horizonIntegral_pin_geom {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |horizonIntegral A k t - (gaussMeasure A).toReal| ≤
      (79 / 100) ^ k * (gaussMeasure A).toReal := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set γA : ℝ := (gaussMeasure A).toReal with hγA
  have hγ0 : 0 ≤ γA := ENNReal.toReal_nonneg
  set G : ℝ → ℝ := horizonIntegral A k with hG
  set Lk : ℝ := (3 / 4 : ℝ) ^ k * (2 * Real.log 2 * γA) with hLk
  have hLk0 : 0 ≤ Lk := by rw [hLk]; positivity
  have hIoofin : volume (Set.Ioo (0 : ℝ) 1) < ⊤ := by simp [Real.volume_Ioo]
  have hwint : IntegrableOn gaussDensityReal (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_gaussDensityReal (le_refl _)
  have hcontw : ContinuousOn gaussDensityReal (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_const.add continuous_id).mul continuous_const).continuousOn
    · intro y hy
      have := hy.1
      positivity
  have hcontlog : ContinuousOn (fun s : ℝ => Real.log (1 + s)) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro y hy; have := hy.1; linarith
  have hcontG : ContinuousOn G (Set.Icc (0 : ℝ) 1) := continuousOn_horizonIntegral hA hA1 k
  have hwG : IntegrableOn (fun s => gaussDensityReal s * G s)
      (Set.Ioo (0 : ℝ) 1) volume :=
    ((hcontw.mul hcontG).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hwGt : IntegrableOn (fun s => gaussDensityReal s * G t)
      (Set.Ioo (0 : ℝ) 1) volume := hwint.mul_const _
  have hdiff : G t - γA = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (G t - G s) := by
    have h1 : G t = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G t := by
      rw [integral_mul_const, integral_mix_weight, one_mul]
    rw [hγA, ← integral_horizonIntegral_eq_gauss hA hA1 k]
    calc G t - ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * horizonIntegral A k s
        = (∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G t) -
            ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * G s := by rw [← h1]
      _ = ∫ s in Set.Ioo (0 : ℝ) 1,
            (gaussDensityReal s * G t - gaussDensityReal s * G s) :=
          (integral_sub hwGt hwG).symm
      _ = ∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (G t - G s) := by
          simp only [mul_sub]
  have hintabs : IntegrableOn (fun s => |gaussDensityReal s * (G t - G s)|)
      (Set.Ioo (0 : ℝ) 1) volume := by
    have : ContinuousOn (fun s => |gaussDensityReal s * (G t - G s)|)
        (Set.Icc (0 : ℝ) 1) := (hcontw.mul (continuousOn_const.sub hcontG)).abs
    exact (this.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hintmaj : IntegrableOn
      (fun s => Lk * (gaussDensityReal s * |Real.log (1 + t) - Real.log (1 + s)|))
      (Set.Ioo (0 : ℝ) 1) volume := by
    have : ContinuousOn
        (fun s => Lk * (gaussDensityReal s * |Real.log (1 + t) - Real.log (1 + s)|))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.mul (hcontw.mul ((continuousOn_const.sub hcontlog).abs))
    exact (this.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  rw [hdiff]
  have hstep : |∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (G t - G s)| ≤
      Lk * (Real.log 2 / 2) := by
    calc |∫ s in Set.Ioo (0 : ℝ) 1, gaussDensityReal s * (G t - G s)|
        ≤ ∫ s in Set.Ioo (0 : ℝ) 1, |gaussDensityReal s * (G t - G s)| := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
            (fun s => gaussDensityReal s * (G t - G s))
      _ ≤ ∫ s in Set.Ioo (0 : ℝ) 1,
            Lk * (gaussDensityReal s * |Real.log (1 + t) - Real.log (1 + s)|) := by
          refine setIntegral_mono_on hintabs hintmaj measurableSet_Ioo ?_
          intro s hs
          have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hs
          have hw0 : 0 ≤ gaussDensityReal s := by
            rw [gaussDensityReal]; have := hs.1; positivity
          rw [abs_mul, abs_of_nonneg hw0]
          have h := horizonIntegral_logLip hA hA1 k ht hs'
          calc gaussDensityReal s * |G t - G s|
              ≤ gaussDensityReal s * (Lk * |Real.log (1 + t) - Real.log (1 + s)|) := by
                exact mul_le_mul_of_nonneg_left h hw0
            _ = Lk * (gaussDensityReal s * |Real.log (1 + t) - Real.log (1 + s)|) := by
                ring
      _ = Lk * ∫ s in Set.Ioo (0 : ℝ) 1,
            gaussDensityReal s * |Real.log (1 + t) - Real.log (1 + s)| :=
          integral_const_mul _ _
      _ ≤ Lk * (Real.log 2 / 2) := by
          exact mul_le_mul_of_nonneg_left
            (integral_gaussDensity_mul_abs_log_sub_le ht) hLk0
  refine hstep.trans ?_
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hsq : Real.log 2 * Real.log 2 ≤ 1 := by nlinarith
  have hpow : (3 / 4 : ℝ) ^ k ≤ (79 / 100 : ℝ) ^ k := by
    have : ∀ n : ℕ, (3 / 4 : ℝ) ^ n ≤ (79 / 100 : ℝ) ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ m ihm =>
          have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ m := by positivity
          rw [pow_succ, pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 79/100) m]
    exact this k
  have hpow0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k := by positivity
  calc Lk * (Real.log 2 / 2)
      = (3 / 4 : ℝ) ^ k * (Real.log 2 * Real.log 2) * γA := by rw [hLk]; ring
    _ ≤ (3 / 4 : ℝ) ^ k * 1 * γA := by
        apply mul_le_mul_of_nonneg_right _ hγ0
        exact mul_le_mul_of_nonneg_left hsq hpow0
    _ = (3 / 4 : ℝ) ^ k * γA := by ring
    _ ≤ (79 / 100 : ℝ) ^ k * γA := mul_le_mul_of_nonneg_right hpow hγ0


/-! ## ψ-mixing at the cylinder level -/

/-- Countable sets are `γ`-null. -/
lemma gaussMeasure_countable_null {S : Set ℝ} (hS : S.Countable) : gaussMeasure S = 0 := by
  apply MeasureTheory.withDensity_absolutelyContinuous
    (volume.restrict (Set.Ioo (0 : ℝ) 1))
    (fun x => ENNReal.ofReal (((1 + x) * Real.log 2)⁻¹))
  rw [Measure.restrict_apply' measurableSet_Ioo]
  exact measure_mono_null Set.inter_subset_left (hS.measure_zero _)

theorem gaussMeasure_cylinder_psi_mixing (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a)
    (g : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    |(gaussMeasure (cfCylinder v ∩ (gaussMap^[v.length + g]) ⁻¹' A)).toReal -
        (gaussMeasure (cfCylinder v)).toReal * (gaussMeasure A).toReal| ≤
      (79 / 100) ^ g * (gaussMeasure A).toReal *
        (gaussMeasure (cfCylinder v)).toReal := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set X : Set ℝ := cfCylinder v ∩ (gaussMap^[v.length + g]) ⁻¹' A with hX
  have hXmeas : MeasurableSet X :=
    (measurableSet_cfCylinder v).inter
      ((measurable_gaussMap.iterate (v.length + g)) hA)
  have hX1 : X ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx => hx.1.1
  have hVmeas : MeasurableSet (cfCylinder v) := measurableSet_cfCylinder v
  have hV1 := cfCylinder_subset_Ioo v
  set E : ℝ := (79 / 100) ^ g * (gaussMeasure A).toReal with hE
  have hE0 : 0 ≤ E := by
    have := ENNReal.toReal_nonneg (a := gaussMeasure A)
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
    have hpin := horizonIntegral_pin_geom hA hA1 g (hτmap hs')
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
    _ = (79 / 100) ^ g * (gaussMeasure A).toReal *
        (gaussMeasure (cfCylinder v)).toReal := by rw [hE]


end NormalNumbers
