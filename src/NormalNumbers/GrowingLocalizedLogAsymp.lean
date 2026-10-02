/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Polynomial versus exponential, in the form the `ζ_Y` assembly consumes
-/

namespace NormalNumbers.GrowingLocalizedLog

open Filter Asymptotics

theorem eventually_poly_le_exp {b : ℝ} (hb : 0 < b) (C : ℝ) :
    ∀ᶠ ℓ : ℕ in atTop, C * ((ℓ : ℝ) + 3) ^ 4 ≤ Real.exp (b * ℓ) := by
  have hO := isLittleO_pow_exp_pos_mul_atTop 4 hb
  have hc : (0 : ℝ) < 1 / (16 * (|C| + 1)) := by positivity
  have hev := hO.def hc
  have hev' : ∀ᶠ x : ℝ in atTop, C * (x + 3) ^ 4 ≤ Real.exp (b * x) := by
    filter_upwards [hev, eventually_ge_atTop (3 : ℝ)] with x hx hx3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_pos (Real.exp_pos _)] at hx
    have h1 : (x + 3) ^ 4 ≤ 16 * x ^ 4 := by
      have : x + 3 ≤ 2 * x := by linarith
      calc (x + 3) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 * x ^ 4 := by ring
    have h2 : C * (x + 3) ^ 4 ≤ (|C| + 1) * (16 * x ^ 4) := by
      have : C ≤ |C| + 1 := by have := le_abs_self C; linarith
      have hp : 0 ≤ (x + 3) ^ 4 := by positivity
      calc C * (x + 3) ^ 4 ≤ (|C| + 1) * (x + 3) ^ 4 := mul_le_mul_of_nonneg_right this hp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (|C| + 1) * (16 * x ^ 4) ≤ Real.exp (b * x) := by
      have : x ^ 4 ≤ 1 / (16 * (|C| + 1)) * Real.exp (b * x) := hx
      have hpos : 0 < 16 * (|C| + 1) := by positivity
      calc (|C| + 1) * (16 * x ^ 4) = (16 * (|C| + 1)) * x ^ 4 := by ring
        _ ≤ (16 * (|C| + 1)) * (1 / (16 * (|C| + 1)) * Real.exp (b * x)) :=
            mul_le_mul_of_nonneg_left this hpos.le
        _ = Real.exp (b * x) := by field_simp
    linarith
  exact tendsto_natCast_atTop_atTop.eventually hev'

/-- Natural-number form: `C (ℓ+3)^4 ≤ 2^ℓ` eventually. -/
theorem eventually_poly_le_two_pow (C : ℕ) : ∀ᶠ ℓ : ℕ in atTop, C * (ℓ + 3) ^ 4 ≤ 2 ^ ℓ := by
  filter_upwards [eventually_poly_le_exp (Real.log_pos one_lt_two) C] with ℓ h
  have : Real.exp (Real.log 2 * ℓ) = (2 : ℝ) ^ ℓ := by
    rw [Real.exp_mul, Real.exp_log two_pos, Real.rpow_natCast]
  rw [this] at h
  exact_mod_cast h

end NormalNumbers.GrowingLocalizedLog
