/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# G4 §5: the parameter schedule — C4, the budget is dominated

Brief §5 sets `L = log log X`, `K = ⌊log L / (100 log log L)⌋`, `s = K²`, `r = s^K`.  The
Fourier-coefficient budget of §4E is `Λ = (2D+1)^r = exp(O(rK))` and the small-prime decay is
`δ₃ ≈ exp(−c L 8^{−K})`.  **C4** is the statement that the decay wins:

    C · r · K · 8^K  <  c · L     eventually in `L`, for every fixed `C, c > 0`,

equivalently `exp(C r K) · exp(−c L 8^{−K}) < 1`.  With `r = K^{2K}` this is
`C K^{2K+1} 8^K < c L`, proved here as `schedule_budget`.  The mechanism: `log(K^{2K+1}8^K)
= (2K+1) log K + K log 8 ≤ (log L)/50 + 3 (log L)/200 + log log L ≤ (log L)/10`, so the left
side is at most `C L^{1/10}`.

This is one simultaneous limit in `L`; `K` is never frozen.
-/

open Real Filter

namespace NormalNumbers.G4

/-- `K(L) = ⌊log L / (100 log log L)⌋`. -/
noncomputable def scheduleK (L : ℝ) : ℕ := ⌊log L / (100 * log (log L))⌋₊

lemma two_le_log_of_le {x : ℝ} (hx : 1000 ≤ x) : 2 ≤ log x := by
  have he : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have h2 : exp 2 ≤ 1000 := by
    have : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    have hlt : exp 1 ≤ 3 := exp_one_lt_three.le
    rw [this]
    nlinarith [exp_pos 1]
  calc (2 : ℝ) = log (exp 2) := (log_exp 2).symm
    _ ≤ log x := log_le_log (exp_pos 2) (h2.trans hx)

lemma log_eight_le_three : log 8 ≤ 3 := by
  have he : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have h : (8 : ℝ) ≤ exp 3 := by
    have : exp 3 = exp 1 * exp 1 * exp 1 := by rw [← exp_add, ← exp_add]; norm_num
    rw [this]
    nlinarith [exp_pos 1]
  calc log 8 ≤ log (exp 3) := log_le_log (by norm_num) h
    _ = 3 := log_exp 3

/-- `log x ≤ 2√x` for `x > 0`. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : log x = 2 * log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  rw [h1]
  have := log_le_sub_one_of_pos hs
  linarith

/-- **The exponent bound**: for `log L ≥ 1000` and `K = K(L) ≥ 1`,
`(2K+1) log K + K log 8 ≤ (log L)/10`. -/
lemma scheduleK_log_bound {L : ℝ} (hL : 1000 ≤ log L) (hK : 1 ≤ scheduleK L) :
    (2 * (scheduleK L : ℝ) + 1) * log (scheduleK L) + (scheduleK L : ℝ) * log 8 ≤ log L / 10 := by
  set x := log L with hx
  set y := log x with hy
  have hx0 : 0 < x := by linarith
  have hy2 : 2 ≤ y := two_le_log_of_le hL
  have hy0 : 0 < y := by linarith
  set K : ℝ := (scheduleK L : ℝ) with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hK
  have hKle : K ≤ x / (100 * y) := by
    rw [hKdef]; unfold scheduleK; rw [← hx, ← hy]
    exact Nat.floor_le (by positivity)
  have hKx : K ≤ x := by
    calc K ≤ x / (100 * y) := hKle
      _ ≤ x / 1 := by
          apply div_le_div_of_nonneg_left hx0.le one_pos; linarith
      _ = x := div_one x
  have hlogK : log K ≤ y := log_le_log (by linarith) hKx
  have hlogK0 : 0 ≤ log K := log_nonneg hK1
  have hKy : K * y ≤ x / 100 := by
    calc K * y ≤ x / (100 * y) * y := mul_le_mul_of_nonneg_right hKle hy0.le
      _ = x / 100 := by field_simp
  have h8 := log_eight_le_three
  have hlog8_0 : 0 ≤ log 8 := log_nonneg (by norm_num)
  -- `y ≤ 2√x ≤ 0.065 x` since `√x ≥ √1000 > 31`
  have hsq : (31 : ℝ) ≤ Real.sqrt x := by
    rw [show (31 : ℝ) = Real.sqrt (31 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  have hyx : y ≤ x * (13 / 200) := by
    have h1 := log_le_two_mul_sqrt hx0
    have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith
  have hA : (2 * K + 1) * log K ≤ x / 50 + y := by
    calc (2 * K + 1) * log K ≤ (2 * K + 1) * y :=
          mul_le_mul_of_nonneg_left hlogK (by linarith)
      _ = 2 * (K * y) + y := by ring
      _ ≤ 2 * (x / 100) + y := by linarith
      _ = x / 50 + y := by ring
  have hB : K * log 8 ≤ x * (3 / 200) := by
    calc K * log 8 ≤ K * 3 := mul_le_mul_of_nonneg_left h8 (by linarith)
      _ ≤ x / (100 * y) * 3 := by
          apply mul_le_mul_of_nonneg_right hKle (by norm_num)
      _ ≤ x / (100 * 2) * 3 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          apply div_le_div_of_nonneg_left hx0.le (by norm_num)
          linarith
      _ = x * (3 / 200) := by ring
  linarith

/-- **C4, the budget inequality.**  For every fixed `C, c > 0`, eventually in `L`:
`C · K^{2K+1} · 8^K < c · L` with `K = K(L)`; equivalently `exp(C r K) exp(−c L 8^{−K}) < 1`
for `r = K^{2K}`. -/
theorem schedule_budget (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * (scheduleK L : ℝ) ^ (2 * scheduleK L + 1) * 8 ^ scheduleK L < c * L := by
  have hev : ∀ᶠ L : ℝ in atTop, exp (max 1000 (10 * |log (C / c)| + 10)) ≤ L :=
    eventually_ge_atTop _
  filter_upwards [hev] with L hL
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hx : max 1000 (10 * |log (C / c)| + 10) ≤ log L := by
    rw [← log_exp (max 1000 (10 * |log (C / c)| + 10))]
    exact log_le_log (exp_pos _) hL
  have hx1000 : 1000 ≤ log L := (le_max_left _ _).trans hx
  have hxC : 10 * |log (C / c)| + 10 ≤ log L := (le_max_right _ _).trans hx
  rcases Nat.eq_zero_or_pos (scheduleK L) with h0 | hpos
  · rw [h0]; simp; positivity
  · have hK1 : 1 ≤ scheduleK L := hpos
    have hKr : (1 : ℝ) ≤ (scheduleK L : ℝ) := by exact_mod_cast hK1
    have hKpos : (0 : ℝ) < (scheduleK L : ℝ) := by linarith
    have hbound := scheduleK_log_bound hx1000 hK1
    -- rewrite the left side as an exponential
    have hL1 : C * (scheduleK L : ℝ) ^ (2 * scheduleK L + 1) * 8 ^ scheduleK L
        = exp (log C + ((2 * (scheduleK L : ℝ) + 1) * log (scheduleK L)
            + (scheduleK L : ℝ) * log 8)) := by
      have e1 : (scheduleK L : ℝ) ^ (2 * scheduleK L + 1)
          = exp ((2 * (scheduleK L : ℝ) + 1) * log (scheduleK L)) := by
        rw [← exp_log (pow_pos hKpos _), log_pow]; push_cast; ring
      have e2 : (8 : ℝ) ^ scheduleK L = exp ((scheduleK L : ℝ) * log 8) := by
        rw [← exp_log (pow_pos (by norm_num : (0:ℝ) < 8) _), log_pow]
      rw [e1, e2, exp_add, exp_add, exp_log hC, mul_assoc]
    have hL2 : c * L = exp (log c + log L) := by
      rw [exp_add, exp_log hc, exp_log hLpos]
    rw [hL1, hL2, exp_lt_exp]
    have hlogCc : log (C / c) = log C - log c := log_div hC.ne' hc.ne'
    have habs : log C - log c ≤ |log (C / c)| := hlogCc ▸ le_abs_self _
    linarith

end NormalNumbers.G4
