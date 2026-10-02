/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Fourier coefficients of the hat function on the circle

`hat L m y = max 0 (L - ‖y - m‖)` on `AddCircle 1`, for `0 ≤ L ≤ 1/2`.  Its `n`-th Fourier
coefficient is `e(-nm)(e(nL) + e(-nL) - 2)/(−2πin)²`, so `‖ĥ(n)‖ ≤ 1/(π²n²)` (`norm_hat_coeff_le`),
and `ĥ(0) = L²`.
-/

open Complex MeasureTheory intervalIntegral

namespace NormalNumbers.HatFourier

/-- Antiderivative of `x ↦ e^{cx}(x − α)`. -/
theorem hasDerivAt_prim (c : ℂ) (hc : c ≠ 0) (α x : ℝ) :
    HasDerivAt (fun x : ℝ => exp (c * x) * (((x - α : ℝ) : ℂ) / c - 1 / c ^ 2))
      (exp (c * x) * ((x - α : ℝ) : ℂ)) x := by
  have h1 : HasDerivAt (fun x : ℝ => exp (c * x)) (exp (c * x) * c) x := by
    have := ((hasDerivAt_id x).ofReal_comp.const_mul c).cexp
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => ((x - α : ℝ) : ℂ) / c - 1 / c ^ 2) (1 / c) x := by
    have := (((hasDerivAt_id x).sub_const α).ofReal_comp.div_const c).sub_const (1 / c ^ 2)
    simpa using this
  refine (h1.mul h2).congr_deriv ?_
  field_simp
  ring

theorem integral_exp_mul_linear (c : ℂ) (hc : c ≠ 0) (α a b : ℝ) :
    ∫ x in a..b, exp (c * x) * ((x - α : ℝ) : ℂ) =
      exp (c * b) * (((b - α : ℝ) : ℂ) / c - 1 / c ^ 2) -
        exp (c * a) * (((a - α : ℝ) : ℂ) / c - 1 / c ^ 2) := by
  refine integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_prim c hc α x) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  fun_prop

theorem hat_integral (L m : ℝ) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 2) (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (m - 1 / 2)..(m + 1 / 2), exp (c * x) * ((max 0 (L - |x - m|) : ℝ) : ℂ) =
      (exp (c * (m - L : ℝ)) + exp (c * (m + L : ℝ)) - 2 * exp (c * m)) / c ^ 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun x : ℝ => exp (c * x) * ((max 0 (L - |x - m|) : ℝ) : ℂ)) volume a b := fun a b =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← integral_add_adjacent_intervals (hint _ (m - L)) (hint (m - L) _),
    ← integral_add_adjacent_intervals (hint (m - L) m) (hint m _),
    ← integral_add_adjacent_intervals (hint m (m + L)) (hint (m + L) _)]
  have e1 : ∫ x in (m - 1 / 2)..(m - L), exp (c * x) * ((max 0 (L - |x - m|) : ℝ) : ℂ) = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℂ)) (fun x hx => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by linarith)] at hx
      simp only
      rw [max_eq_left (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2])]
      simp
  have e4 : ∫ x in (m + L)..(m + 1 / 2), exp (c * x) * ((max 0 (L - |x - m|) : ℝ) : ℂ) = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℂ)) (fun x hx => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by linarith)] at hx
      simp only
      rw [max_eq_left (by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1])]
      simp
  have e2 : ∫ x in (m - L)..m, exp (c * x) * ((max 0 (L - |x - m|) : ℝ) : ℂ) =
      ∫ x in (m - L)..m, exp (c * x) * ((x - (m - L) : ℝ) : ℂ) := by
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [abs_of_nonpos (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
    congr 2; ring
  have e3 : ∫ x in m..(m + L), exp (c * x) * ((max 0 (L - |x - m|) : ℝ) : ℂ) =
      -∫ x in m..(m + L), exp (c * x) * ((x - (m + L) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_neg]
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [abs_of_nonneg (by linarith [hx.1]), max_eq_right (by linarith [hx.2])]
    push_cast; ring
  rw [e1, e4, e2, e3, integral_exp_mul_linear c hc, integral_exp_mul_linear c hc]
  push_cast
  field_simp
  ring

/-- The hat function of half-width `L` centred at `m`. -/
noncomputable def hat (L m : ℝ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun y => ((max 0 (L - ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖) : ℝ) : ℂ), by fun_prop⟩

theorem hat_coe (L m x : ℝ) (hx : |x - m| ≤ 1 / 2) :
    hat L m (x : AddCircle (1 : ℝ)) = ((max 0 (L - |x - m|) : ℝ) : ℂ) := by
  show ((max 0 (L - ‖(x : AddCircle (1 : ℝ)) - ((m : ℝ) : AddCircle (1 : ℝ))‖) : ℝ) : ℂ) = _
  rw [← AddCircle.coe_sub, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2
    (by simpa using hx)]

theorem hat_coeff (L m : ℝ) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 2) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (hat L m) n =
      (exp ((2 * Real.pi * I * (-n : ℤ)) * (m - L : ℝ)) +
        exp ((2 * Real.pi * I * (-n : ℤ)) * (m + L : ℝ)) -
          2 * exp ((2 * Real.pi * I * (-n : ℤ)) * m)) / (2 * Real.pi * I * (-n : ℤ)) ^ 2 := by
  have hc : (2 * Real.pi * I * (-n : ℤ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, hn, I_ne_zero]
  rw [fourierCoeff_eq_intervalIntegral _ n (m - 1 / 2), ← hat_integral L m hL0 hL _ hc,
    show m - 1 / 2 + 1 = m + 1 / 2 by ring]
  simp only [div_one, one_smul, smul_eq_mul]
  refine integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by linarith)] at hx
  have hx' : |x - m| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hat_coe L m x hx', fourier_coe_apply]
  congr 2
  push_cast; ring

theorem norm_exp_imag (θ : ℝ) (r : ℝ) : ‖exp ((θ * I) * (r : ℂ))‖ = 1 := by
  rw [norm_exp]
  simp

theorem norm_hat_coeff_le (L m : ℝ) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 2) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (hat L m) n‖ ≤ 1 / (Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  rw [hat_coeff L m hL0 hL n hn]
  have hθ : (2 * Real.pi * I * (-n : ℤ) : ℂ) = ((2 * Real.pi * (-n : ℤ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hθ, norm_div, norm_pow]
  have hcn : ‖((2 * Real.pi * (-n : ℤ) : ℝ) : ℂ) * I‖ = 2 * Real.pi * |(n : ℝ)| := by
    rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    push_cast
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2),
      abs_of_pos Real.pi_pos]
  rw [hcn]
  have hnum : ‖exp (((2 * Real.pi * (-n : ℤ) : ℝ) : ℂ) * I * ((m - L : ℝ) : ℂ)) +
      exp (((2 * Real.pi * (-n : ℤ) : ℝ) : ℂ) * I * ((m + L : ℝ) : ℂ)) -
      2 * exp (((2 * Real.pi * (-n : ℤ) : ℝ) : ℂ) * I * ((m : ℝ) : ℂ))‖ ≤ 4 := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le _ _) _).trans ?_
    rw [norm_mul, norm_exp_imag, norm_exp_imag, norm_exp_imag]
    norm_num
  have hn1 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc _ ≤ 4 * (Real.pi ^ 2 * (n : ℝ) ^ 2) := by gcongr
    _ = 1 * (2 * Real.pi * |(n : ℝ)|) ^ 2 := by rw [mul_pow, sq_abs]; ring

theorem hat_of_neg (L m : ℝ) (hL : L ≤ 0) : hat L m = 0 := by
  ext y
  show ((max 0 (L - ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖) : ℝ) : ℂ) = 0
  rw [max_eq_left (by linarith [norm_nonneg (y - ((m : ℝ) : AddCircle (1 : ℝ)))])]
  simp

theorem norm_hat_coeff_le' (L m : ℝ) (hL : L ≤ 1 / 2) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (hat L m) n‖ ≤ 1 / (Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  rcases le_or_gt L 0 with h | h
  · rw [hat_of_neg L m h]
    have : fourierCoeff (0 : AddCircle (1 : ℝ) → ℂ) n = 0 := by simp [fourierCoeff]
    simp only [ContinuousMap.coe_zero, this, norm_zero]
    positivity
  · exact norm_hat_coeff_le L m h.le hL n hn

/-- The plateau function: `1` within `L − ρ` of `m`, `0` beyond `L`, linear between. -/
noncomputable def plateau (L ρ m : ℝ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun y => ((min 1 (max 0 ((L - ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖) / ρ)) : ℝ) : ℂ),
    by fun_prop⟩

theorem plateau_eq (L ρ m : ℝ) (hρ : 0 < ρ) :
    plateau L ρ m = (ρ⁻¹ : ℂ) • (hat L m - hat (L - ρ) m) := by
  ext y
  show ((min 1 (max 0 ((L - ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖) / ρ)) : ℝ) : ℂ) =
    (ρ⁻¹ : ℂ) * (((max 0 (L - ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖) : ℝ) : ℂ) -
      ((max 0 (L - ρ - ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖) : ℝ) : ℂ))
  set r := ‖y - ((m : ℝ) : AddCircle (1 : ℝ))‖
  have hr : 0 ≤ r := norm_nonneg _
  have key : min 1 (max 0 ((L - r) / ρ)) = ρ⁻¹ * (max 0 (L - r) - max 0 (L - ρ - r)) := by
    rcases le_or_gt (L - r) 0 with h1 | h1
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg h1 hρ.le), max_eq_left h1,
        max_eq_left (by linarith)]
      simp
    rcases le_or_gt (L - ρ - r) 0 with h2 | h2
    · rw [max_eq_right (div_nonneg h1.le hρ.le), max_eq_right h1.le, max_eq_left h2,
        min_eq_right ((div_le_one hρ).2 (by linarith))]
      field_simp; ring
    · rw [max_eq_right (div_nonneg h1.le hρ.le), max_eq_right h1.le, max_eq_right h2.le,
        min_eq_left ((one_le_div hρ).2 (by linarith))]
      field_simp; ring
  rw [key]
  push_cast
  ring

theorem norm_plateau_coeff_le (L ρ m : ℝ) (hρ : 0 < ρ) (hL : L ≤ 1 / 2) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (plateau L ρ m) n‖ ≤ 2 / ρ * (1 / (Real.pi ^ 2 * (n : ℝ) ^ 2)) := by
  rw [plateau_eq L ρ m hρ]
  have hcoe : ⇑((ρ⁻¹ : ℂ) • (hat L m - hat (L - ρ) m)) =
      (ρ⁻¹ : ℂ) • (⇑(hat L m) - ⇑(hat (L - ρ) m)) := rfl
  have hint : ∀ f : C(AddCircle (1 : ℝ), ℂ), Integrable (⇑f) AddCircle.haarAddCircle := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsub : (⇑(hat L m) - ⇑(hat (L - ρ) m)) = ⇑(hat L m) + (-1 : ℂ) • ⇑(hat (L - ρ) m) := by
    ext y; simp; ring
  rw [hcoe, fourierCoeff.const_smul, hsub, fourierCoeff.add (hint _) ((hint _).smul _),
    Pi.add_apply, fourierCoeff.const_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have h1 := norm_hat_coeff_le' L m hL n hn
  have h2 := norm_hat_coeff_le' (L - ρ) m (by linarith) n hn
  have := norm_sub_le (fourierCoeff (⇑(hat L m)) n) (fourierCoeff (⇑(hat (L - ρ) m)) n)
  have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ
  calc ρ⁻¹ * ‖fourierCoeff (⇑(hat L m)) n - fourierCoeff (⇑(hat (L - ρ) m)) n‖
      ≤ ρ⁻¹ * (2 * (1 / (Real.pi ^ 2 * (n : ℝ) ^ 2))) := by gcongr; linarith
    _ = _ := by field_simp

end NormalNumbers.HatFourier
