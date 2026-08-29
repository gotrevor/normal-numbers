/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# `lcm(1..n)` growth bounds (VENDORED)

**Provenance**: vendored 2026-08-29 from `~/src/collatz-moonshot`
`CollatzMoonshot/FrontA/Gelfond.lean` (same mathlib pin), re-homed by copy into
`NormalNumbers.Legendre` per the dep re-homing decision.  Only the namespace and
this header were changed.  Supplies `lcmUpto_le` (`lcm(1..n) ≤ 4ⁿ·e^{2√n·log n}`,
from mathlib's Chebyshev `ψ` estimate), `log_div_sqrt_tendsto_zero`, and
`lcmUpto_mul_geom_tendsto_zero` — the "geometric beats the denominator" bricks the
`LnTwoExpSep` discharge consumes.
-/

open Chebyshev Real

namespace NormalNumbers.Legendre

/-- **Denominator growth `lcm(1,…,n) ≤ 4^n · e^{2√n·log n}` (leg 1 of the Gelfond construction).**
The Padé/hypergeometric approximants to `log₂3` have coefficients whose denominators divide
`lcm(1,…,n)`; a *finite* (polynomial) irrationality measure requires this to grow at most like a
fixed exponential.  Direct from mathlib's Chebyshev estimate `ψ(n) = log lcm(1..n) ≤ log 4·n + 2√n·log n`.
(The sub-exponential factor `e^{2√n·log n}` is absorbed by the geometric main term in the assembly.) -/
theorem lcmUpto_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.lcmUpto n : ℝ) ≤ 4 ^ n * Real.exp (2 * Real.sqrt n * Real.log n) := by
  have hpos : (0 : ℝ) < (Nat.lcmUpto n : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (Nat.lcmUpto n)
      ≤ (n : ℝ) * Real.log 4 + 2 * Real.sqrt n * Real.log n := by
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    have h := Chebyshev.psi_le hnR
    linarith [h]
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hpos, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hexp

open Filter Topology Asymptotics

/-- `log n / √n → 0` (the sub-exponential factor in `lcmUpto_le` is beaten by any geometric base).
From `log =o[atTop] x^(1/2)`. -/
theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n _
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]

/-- **`lcm(1..n)·cⁿ → 0` for `0 ≤ c < 1/4` (leg-1 assembly brick).**  `lcmUpto n ≤ 4ⁿ·e^{2√n·log n}`
(`lcmUpto_le`), so `lcm·cⁿ ≤ (4c)ⁿ·e^{2√n·log n} = exp(n·log(4c) + 2√n·log n)`; the exponent `→ −∞`
because `4c < 1` makes the linear term dominate the sub-exponential `2√n·log n` (`log_div_sqrt_
tendsto_zero`).  This is exactly the "the geometric remainder beats the denominator" limit that turns a
small-nonzero-integer-combination sequence into an irrationality/effective-measure conclusion — used
for `log 2` now (`legendre_log_two_small`) and reused, two-kernel-wise, by leg 3. -/
theorem lcmUpto_mul_geom_tendsto_zero {c : ℝ} (hc0 : 0 ≤ c) (hc : 4 * c < 1) :
    Tendsto (fun n : ℕ => (Nat.lcmUpto n : ℝ) * c ^ n) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hc0 with hc00 | hc0'
  · -- c = 0: eventually zero
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← hc00, zero_pow (by omega), mul_zero]
  · -- 0 < c
    set b := 4 * c with hb
    have hb0 : 0 < b := by rw [hb]; linarith
    have hlogb : Real.log b < 0 := Real.log_neg hb0 hc
    -- exponent → atBot
    have hh : Tendsto (fun n : ℕ => (n : ℝ) * Real.log b + 2 * Real.sqrt n * Real.log n)
        atTop atBot := by
      have hK : (0 : ℝ) < -Real.log b / 4 := by linarith
      have hev : ∀ᶠ n : ℕ in atTop, Real.log n / Real.sqrt n < -Real.log b / 4 :=
        log_div_sqrt_tendsto_zero.eventually (Iio_mem_nhds hK)
      have hle : ∀ᶠ n : ℕ in atTop,
          (n : ℝ) * Real.log b + 2 * Real.sqrt n * Real.log n ≤ (n : ℝ) * (Real.log b / 2) := by
        filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
        have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
        have hsn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
        have key : 2 * Real.sqrt n * Real.log n
            = 2 * (n : ℝ) * (Real.log n / Real.sqrt n) := by
          rw [show 2 * (n : ℝ) * (Real.log n / Real.sqrt n)
                = 2 * Real.log n * ((n : ℝ) / Real.sqrt n) from by ring, Real.div_sqrt]
          ring
        have h2 : 2 * (n : ℝ) * (Real.log n / Real.sqrt n) ≤ -(n : ℝ) * Real.log b / 2 := by
          calc 2 * (n : ℝ) * (Real.log n / Real.sqrt n)
              ≤ 2 * (n : ℝ) * (-Real.log b / 4) :=
                mul_le_mul_of_nonneg_left (le_of_lt hn) (by positivity)
            _ = -(n : ℝ) * Real.log b / 2 := by ring
        have hbridge : (n : ℝ) * (Real.log b / 2) = (n : ℝ) * Real.log b / 2 := by ring
        rw [key]; linarith [h2, hbridge]
      refine tendsto_atBot_mono' atTop hle ?_
      exact (tendsto_natCast_atTop_atTop).atTop_mul_const_of_neg (by linarith)
    -- g n = exp(exponent) → 0, and squeeze
    have hg : Tendsto (fun n : ℕ => b ^ n * Real.exp (2 * Real.sqrt n * Real.log n))
        atTop (𝓝 0) := by
      have hexp : (fun n : ℕ => b ^ n * Real.exp (2 * Real.sqrt n * Real.log n))
          = fun n : ℕ => Real.exp ((n : ℝ) * Real.log b + 2 * Real.sqrt n * Real.log n) := by
        funext n
        rw [Real.exp_add]
        congr 1
        rw [Real.exp_nat_mul, Real.exp_log hb0]
      rw [hexp]
      exact Real.tendsto_exp_atBot.comp hh
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · filter_upwards with n; positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      calc (Nat.lcmUpto n : ℝ) * c ^ n
          ≤ (4 ^ n * Real.exp (2 * Real.sqrt n * Real.log n)) * c ^ n :=
            mul_le_mul_of_nonneg_right (lcmUpto_le n hn) (pow_nonneg hc0 n)
        _ = b ^ n * Real.exp (2 * Real.sqrt n * Real.log n) := by rw [hb, mul_pow]; ring

end NormalNumbers.Legendre
