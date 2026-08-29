/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns
import NormalNumbers.DiophantineWall
import NormalNumbers.LegendreHeight

/-!
# Tier-1 discharge: `LnTwoExpSep` via the shifted-Legendre package

Lane-2 target 4 (2026-08-29 operator brief; blueprint §5 item 6).  The donor
machinery (vendored: `LegendreShifted.lean`, `LcmUptoGrowth.lean`) gives, for
every `ℓ`, integers `P, Q` with `0 < |P + Q·log 2| ≤ lcmUpto ℓ·(1/5)^ℓ`; the
two honest gaps — an explicit height `|Q| ≤ (ℓ+1)·8^ℓ·lcmUpto ℓ` and the lower
bound `|P + Q·log 2| ≥ lcmUpto ℓ·(1/6)·(1/12)^ℓ` — are closed in
`LegendreHeight.lean` (`legendre_log_two_package`).

## The pairing argument (this file)

For `n` large take `ℓ = 4n` and any integer `p`; set `d = |2ⁿ·log 2 − p|` and
consider the integer `N = P·2ⁿ + Q·p = 2ⁿ·(P + Q·log 2) − Q·(2ⁿ·log 2 − p)`.

* `N ≠ 0`: then `1 ≤ |N| ≤ 2ⁿ·|P + Q·log 2| + |Q|·d ≤ 1/2 + H·d` (the first
  term is `≤ 1/2` because `2ⁿ·lcm(4n)·(1/5)^{4n} → 0`, base `512/625 < 1`), so
  `d ≥ 1/(2H) ≥ 2^{−26n}`.
* `N = 0`: then `|Q|·d = 2ⁿ·|P + Q·log 2| ≥ 2ⁿ·lcm(4n)·(1/6)(1/12)^{4n}`, and
  the `lcm` cancels against the height: `d ≥ 2ⁿ/(6(4n+1)·96^{4n}) ≥ 2^{−26n}`
  because `2²⁷ > 96⁴`.

All three eventual inequalities are instances of one master limit: geometric
`rⁿ` (`r < 1`) beats `(4n+1)·e^{2√(4n)·log(4n)}` (the `lcmUpto` sub-exponential
error from `lcmUpto_le`).

## Why `β = 26` (draft's `β = 4` raised, per the brief's DRAFT clause)

The honest crude constants force it: the height is `|Q| ≲ lcm(4n)·8^{4n}
≤ 2^{8n}·2^{12n}·e^{o(n)}`, giving `2^{−20n−o(n)}` in the nonzero case, and the
zero case gives `2^{n−4n·log₂96} ≈ 2^{−25.4n}`; `β = 26` absorbs both
(`ℓ = 4n` is needed to beat `2ⁿ`: `ℓ·log₂(5/4) > n` forces `ℓ > 3.1n`).  The
optimal Alladi–Robinson-style rate (`β ≈ 3.63`) needs the sharp coefficient
asymptotics `Σ|c_k| ~ P_ℓ(3)`-type bounds and two-sided sharp remainder
estimates — not attempted here.  Any explicit `β` lights the run tower:
`run_le_of_expSep` caps every zero/one run of binary `ln 2` at `βn + O(log n)`,
unconditionally.
-/

namespace NormalNumbers

open Filter Real Legendre

/-- Master limit: for `0 < r < 1`, the geometric factor kills both the
polynomial factor and the `lcmUpto` sub-exponential error term at index `4n`:
`(4n+1)·rⁿ·e^{2√(4n)·log(4n)} → 0`. -/
private lemma tendsto_poly_geom_subexp {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto
      (fun n : ℕ => ((4 * n + 1 : ℕ) : ℝ) * r ^ n *
        Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  set ε : ℝ := -Real.log r / 32 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have h4 : Tendsto (fun n : ℕ => 4 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.log ((4 * n : ℕ) : ℝ) / Real.sqrt ((4 * n : ℕ) : ℝ) < ε :=
    (log_div_sqrt_tendsto_zero.comp h4).eventually (Iio_mem_nhds hεpos)
  -- dominating sequence g → 0
  have hg : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (Real.log r / 2) + 1))
      atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_atBot_add_const_right
    exact tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards with n
    positivity
  · filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hm1 : (1 : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < ((4 * n : ℕ) : ℝ) := by linarith
    have hsqrtpos : (0 : ℝ) < Real.sqrt ((4 * n : ℕ) : ℝ) := Real.sqrt_pos.mpr hmpos
    -- log(4n) < ε·√(4n) ≤ ε·(4n)
    have hlog1 : Real.log ((4 * n : ℕ) : ℝ) < ε * Real.sqrt ((4 * n : ℕ) : ℝ) := by
      have := (div_lt_iff₀ hsqrtpos).mp hn
      linarith
    have hsqrt_le : Real.sqrt ((4 * n : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr hm1)
    have hlog2 : Real.log ((4 * n : ℕ) : ℝ) ≤ ε * ((4 * n : ℕ) : ℝ) := by
      nlinarith
    -- the sub-exponential exponent: s < 8εn
    have hs : 2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)
        ≤ 8 * ε * (n : ℝ) := by
      have h1 : 2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)
          ≤ 2 * Real.sqrt ((4 * n : ℕ) : ℝ) * (ε * Real.sqrt ((4 * n : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hlog1) (by positivity)
      have h2 : Real.sqrt ((4 * n : ℕ) : ℝ) * Real.sqrt ((4 * n : ℕ) : ℝ)
          = ((4 * n : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
      have h3 : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by push_cast; ring
      nlinarith
    -- the polynomial factor: 4n+1 ≤ exp(1 + 4εn)
    have hpoly : ((4 * n + 1 : ℕ) : ℝ) ≤ Real.exp (1 + 4 * ε * (n : ℝ)) := by
      have hpos : (0 : ℝ) < ((4 * n + 1 : ℕ) : ℝ) := by positivity
      rw [← Real.exp_log hpos]
      apply Real.exp_le_exp.mpr
      have hle : ((4 * n + 1 : ℕ) : ℝ) ≤ 2 * ((4 * n : ℕ) : ℝ) := by
        push_cast
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      calc Real.log ((4 * n + 1 : ℕ) : ℝ)
          ≤ Real.log (2 * ((4 * n : ℕ) : ℝ)) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log 2 + Real.log ((4 * n : ℕ) : ℝ) :=
            Real.log_mul (by norm_num) (by positivity)
        _ ≤ 1 + 4 * ε * (n : ℝ) := by
            have hlog2' : Real.log 2 ≤ 1 := by
              calc Real.log 2 ≤ Real.log (Real.exp 1) :=
                    Real.log_le_log (by norm_num)
                      (by linarith [Real.add_one_le_exp (1 : ℝ)])
                _ = 1 := Real.log_exp 1
            have h3 : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by push_cast; ring
            nlinarith
    -- assemble
    have hrpow : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr0]
    calc ((4 * n + 1 : ℕ) : ℝ) * r ^ n *
          Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ))
        ≤ Real.exp (1 + 4 * ε * (n : ℝ)) * Real.exp ((n : ℝ) * Real.log r) *
          Real.exp (8 * ε * (n : ℝ)) := by
          rw [hrpow]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hpoly (by positivity))
            (Real.exp_le_exp.mpr hs) (by positivity) (by positivity)
      _ = Real.exp (1 + 4 * ε * (n : ℝ) + (n : ℝ) * Real.log r + 8 * ε * (n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((n : ℝ) * (Real.log r / 2) + 1) := by
          apply Real.exp_le_exp.mpr
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
          rw [hεdef]
          nlinarith
  -- (end master)

/-- **Tier-1 discharge: effective exponential dyadic separation for `ln 2`,
in-house via shifted-Legendre linear forms.**  `β = 26`: the draft's `β = 4`
raised per its DRAFT clause — see the module docstring for the honest-constant
accounting (`|Q| ≲ 2^{20n}` height, zero case `≈ 2^{−25.4n}`, and `2²⁷ > 96⁴`
closes it). -/
theorem lnTwoExpSep_holds : ∃ N₀ : ℕ, LnTwoExpSep 26 N₀ := by
  -- Eventual inequality (1): the linear form is small against `2ⁿ`.
  have hC1 : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ n * ((Nat.lcmUpto (4 * n) : ℝ) * (1 / 5 : ℝ) ^ (4 * n)) ≤ 1 / 2 := by
    have hM := tendsto_poly_geom_subexp
      (r := 512 / 625) (by norm_num) (by norm_num)
    have hev := hM.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hlcm := Legendre.lcmUpto_le (4 * n) (by omega)
    have hstep : (2 : ℝ) ^ n * ((Nat.lcmUpto (4 * n) : ℝ) * (1 / 5 : ℝ) ^ (4 * n))
        ≤ ((4 * n + 1 : ℕ) : ℝ) * (512 / 625 : ℝ) ^ n *
          Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) := by
      have h1 : (2 : ℝ) ^ n * ((Nat.lcmUpto (4 * n) : ℝ) * (1 / 5 : ℝ) ^ (4 * n))
          ≤ (2 : ℝ) ^ n * ((4 : ℝ) ^ (4 * n) *
              Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) *
              (1 / 5 : ℝ) ^ (4 * n)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hlcm (by positivity)
      have h2 : (2 : ℝ) ^ n * ((4 : ℝ) ^ (4 * n) *
            Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) *
            (1 / 5 : ℝ) ^ (4 * n))
          = (512 / 625 : ℝ) ^ n *
            Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) := by
        rw [pow_mul, pow_mul, show ((4 : ℝ) ^ 4) = 256 by norm_num,
          show ((1 / 5 : ℝ) ^ 4) = 1 / 625 by norm_num]
        rw [show (512 / 625 : ℝ) = 2 * (256 * (1 / 625)) by norm_num, mul_pow, mul_pow]
        ring
      have h3 : (1 : ℝ) ≤ ((4 * n + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ 4 * n + 1 := by omega
        exact_mod_cast this
      calc (2 : ℝ) ^ n * ((Nat.lcmUpto (4 * n) : ℝ) * (1 / 5 : ℝ) ^ (4 * n))
          ≤ (512 / 625 : ℝ) ^ n *
            Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) := by
            rw [← h2]; exact h1
        _ ≤ ((4 * n + 1 : ℕ) : ℝ) * (512 / 625 : ℝ) ^ n *
            Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith [pow_pos (show (0:ℝ) < 512/625 by norm_num) n]
    exact hstep.trans (le_of_lt hn)
  -- Eventual inequality (2): twice the height is at most `2^{26n}`.
  have hC2 : ∀ᶠ n : ℕ in atTop,
      2 * ((((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * (Nat.lcmUpto (4 * n) : ℝ))
        ≤ (2 : ℝ) ^ (26 * n) := by
    have hM := tendsto_poly_geom_subexp
      (r := 1 / 64) (by norm_num) (by norm_num)
    have hev := hM.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hlcm := Legendre.lcmUpto_le (4 * n) (by omega)
    set S : ℝ :=
      Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) with hSdef
    have hS0 : 0 < S := Real.exp_pos _
    have hcast : (((4 * n : ℕ) : ℝ) + 1) = ((4 * n + 1 : ℕ) : ℝ) := by push_cast; ring
    have h1 : 2 * ((((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * (Nat.lcmUpto (4 * n) : ℝ))
        ≤ 2 * (((4 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (4 * n) * ((4 : ℝ) ^ (4 * n) * S)) := by
      rw [hcast]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hlcm (by positivity)
    have h2 : 2 * (((4 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (4 * n) * ((4 : ℝ) ^ (4 * n) * S))
        = 2 * (((4 * n + 1 : ℕ) : ℝ) * (1 / 64 : ℝ) ^ n * S) * (2 : ℝ) ^ (26 * n) := by
      rw [pow_mul, pow_mul, pow_mul,
        show ((8 : ℝ) ^ 4) = 4096 by norm_num,
        show ((4 : ℝ) ^ 4) = 256 by norm_num,
        show ((2 : ℝ) ^ 26) = 67108864 by norm_num]
      have key : (4096 : ℝ) ^ n * 256 ^ n = (1 / 64 : ℝ) ^ n * 67108864 ^ n := by
        rw [← mul_pow, ← mul_pow]; norm_num
      linear_combination (2 * ((4 * n + 1 : ℕ) : ℝ) * S) * key
    calc 2 * ((((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * (Nat.lcmUpto (4 * n) : ℝ))
        ≤ 2 * (((4 * n + 1 : ℕ) : ℝ) * (1 / 64 : ℝ) ^ n * S) * (2 : ℝ) ^ (26 * n) := by
          rw [← h2]; exact h1
      _ ≤ 2 * (1 / 4) * (2 : ℝ) ^ (26 * n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left (le_of_lt hn) (by norm_num)
      _ ≤ (2 : ℝ) ^ (26 * n) := by
          nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) (26 * n)]
  -- Eventual inequality (3): height·2^{−26n} at most the lower bound (zero case).
  have hC3 : ∀ᶠ n : ℕ in atTop,
      (((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * (Nat.lcmUpto (4 * n) : ℝ) *
          ((2 : ℝ) ^ (26 * n))⁻¹
        ≤ (2 : ℝ) ^ n *
          ((Nat.lcmUpto (4 * n) : ℝ) * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n))) := by
    have hM := tendsto_poly_geom_subexp
      (r := 84934656 / 134217728) (by norm_num) (by norm_num)
    have hev := hM.eventually_lt_const (show (0 : ℝ) < 1 / 6 by norm_num)
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hm1 : (1 : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * n := by omega
      exact_mod_cast this
    have hS1 : (1 : ℝ) ≤
        Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      apply Real.exp_le_exp.mpr
      have hlognn : 0 ≤ Real.log ((4 * n : ℕ) : ℝ) := Real.log_nonneg hm1
      positivity
    -- core integer inequality: 6·(4n+1)·8^{4n}·12^{4n} ≤ 2^{27n}
    have hcore : 6 * (((4 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (4 * n) * (12 : ℝ) ^ (4 * n))
        ≤ (2 : ℝ) ^ (27 * n) := by
      have h1 : ((4 * n + 1 : ℕ) : ℝ) * (84934656 / 134217728 : ℝ) ^ n ≤ 1 / 6 := by
        calc ((4 * n + 1 : ℕ) : ℝ) * (84934656 / 134217728 : ℝ) ^ n
            ≤ ((4 * n + 1 : ℕ) : ℝ) * (84934656 / 134217728 : ℝ) ^ n *
              Real.exp (2 * Real.sqrt ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ)) := by
              nlinarith [mul_pos
                (mul_pos (show (0:ℝ) < ((4 * n + 1 : ℕ) : ℝ) by positivity)
                  (pow_pos (show (0:ℝ) < 84934656 / 134217728 by norm_num) n))
                (Real.exp_pos (2 * Real.sqrt ((4 * n : ℕ) : ℝ) *
                  Real.log ((4 * n : ℕ) : ℝ)))]
          _ ≤ 1 / 6 := le_of_lt hn
      have h2 : (8 : ℝ) ^ (4 * n) * (12 : ℝ) ^ (4 * n)
          = (84934656 / 134217728 : ℝ) ^ n * (2 : ℝ) ^ (27 * n) := by
        rw [pow_mul, pow_mul, pow_mul,
          show ((8 : ℝ) ^ 4) = 4096 by norm_num,
          show ((12 : ℝ) ^ 4) = 20736 by norm_num,
          show ((2 : ℝ) ^ 27) = 134217728 by norm_num,
          ← mul_pow, ← mul_pow]
        norm_num
      calc 6 * (((4 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (4 * n) * (12 : ℝ) ^ (4 * n))
          = 6 * (((4 * n + 1 : ℕ) : ℝ) * (84934656 / 134217728 : ℝ) ^ n) *
            (2 : ℝ) ^ (27 * n) := by rw [mul_assoc (((4 * n + 1 : ℕ) : ℝ)), h2]; ring
        _ ≤ 6 * (1 / 6) * (2 : ℝ) ^ (27 * n) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = (2 : ℝ) ^ (27 * n) := by ring
    -- convert to the fraction shape
    have hcast : (((4 * n : ℕ) : ℝ) + 1) = ((4 * n + 1 : ℕ) : ℝ) := by push_cast; ring
    have hfrac : (((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * ((2 : ℝ) ^ (26 * n))⁻¹
        ≤ (2 : ℝ) ^ n * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n)) := by
      rw [hcast, ← div_eq_mul_inv,
        show (1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n) = 1 / (6 * (12 : ℝ) ^ (4 * n)) by
          rw [div_pow]; ring,
        mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      calc ((4 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (4 * n) * (6 * (12 : ℝ) ^ (4 * n))
          = 6 * (((4 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (4 * n) * (12 : ℝ) ^ (4 * n)) := by
            ring
        _ ≤ (2 : ℝ) ^ (27 * n) := hcore
        _ = (2 : ℝ) ^ n * (2 : ℝ) ^ (26 * n) := by
            rw [← pow_add]; congr 1; omega
    calc (((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * (Nat.lcmUpto (4 * n) : ℝ) *
            ((2 : ℝ) ^ (26 * n))⁻¹
        = ((((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * ((2 : ℝ) ^ (26 * n))⁻¹) *
            (Nat.lcmUpto (4 * n) : ℝ) := by ring
      _ ≤ ((2 : ℝ) ^ n * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n))) *
            (Nat.lcmUpto (4 * n) : ℝ) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (2 : ℝ) ^ n *
            ((Nat.lcmUpto (4 * n) : ℝ) * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n))) := by
          ring
  -- extract a uniform threshold
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hC1.and (hC2.and hC3)).and
    (eventually_ge_atTop 1))
  refine ⟨N₀, ?_⟩
  rw [LnTwoExpSep, lnTwoDyadicSep_iff_int]
  intro n hn p
  obtain ⟨⟨h1, h2, h3⟩, hn1⟩ := hN₀ n hn
  -- the Legendre package at ℓ = 4n
  obtain ⟨P, Q, hup, hlow, hQ⟩ := Legendre.legendre_log_two_package (4 * n)
  set L : ℝ := Real.log 2 with hLdef
  set d : ℝ := |L * 2 ^ n - (p : ℝ)| with hddef
  have hd0 : 0 ≤ d := abs_nonneg _
  set form : ℝ := (P : ℝ) + (Q : ℝ) * L with hformdef
  set H : ℝ := (((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) * (Nat.lcmUpto (4 * n) : ℝ)
    with hHdef
  have hH0 : 0 < H := by
    rw [hHdef]
    have : (0 : ℝ) < (Nat.lcmUpto (4 * n) : ℝ) := by
      exact_mod_cast Nat.lcmUpto_pos (4 * n)
    positivity
  have hQle : |(Q : ℝ)| ≤ H := by
    rw [hHdef]
    exact_mod_cast hQ
  -- the pairing integer
  set N : ℤ := P * 2 ^ n + Q * p with hNdef
  have hNid : (N : ℝ) = 2 ^ n * form - (Q : ℝ) * (L * 2 ^ n - (p : ℝ)) := by
    rw [hNdef, hformdef]
    push_cast
    ring
  -- goal in inverse-power form
  have hgoal_eq : (2 : ℝ) ^ (-((26 : ℝ) * (n : ℝ))) = ((2 : ℝ) ^ (26 * n))⁻¹ := by
    rw [show -((26 : ℝ) * (n : ℝ)) = -(((26 * n : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [show (2 : ℝ) ^ (-(26 * (n : ℝ))) = (2 : ℝ) ^ (-((26 : ℝ) * (n : ℝ))) by norm_num,
    hgoal_eq]
  by_cases hNz : N = 0
  · -- zero case: |Q|·d = 2ⁿ·|form| ≥ 2ⁿ·lcm·(1/6)(1/12)^{4n}; the lcm cancels
    -- against the height via hC3.
    have hid : (Q : ℝ) * (L * 2 ^ n - (p : ℝ)) = 2 ^ n * form := by
      have := hNid
      rw [hNz] at this
      push_cast at this
      linarith
    have habs : |(Q : ℝ)| * d = 2 ^ n * |form| := by
      rw [hddef, ← abs_mul, hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^n)]
    have hlow2 : (2 : ℝ) ^ n *
        ((Nat.lcmUpto (4 * n) : ℝ) * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n)))
        ≤ H * d := by
      calc (2 : ℝ) ^ n *
            ((Nat.lcmUpto (4 * n) : ℝ) * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n)))
          ≤ 2 ^ n * |form| := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hlow
        _ = |(Q : ℝ)| * d := habs.symm
        _ ≤ H * d := mul_le_mul_of_nonneg_right hQle hd0
    have hchain : H * ((2 : ℝ) ^ (26 * n))⁻¹ ≤ H * d := by
      calc H * ((2 : ℝ) ^ (26 * n))⁻¹
          ≤ (2 : ℝ) ^ n *
            ((Nat.lcmUpto (4 * n) : ℝ) * ((1 / 6 : ℝ) * (1 / 12 : ℝ) ^ (4 * n))) := h3
        _ ≤ H * d := hlow2
    exact le_of_mul_le_mul_left hchain hH0
  · -- nonzero case: 1 ≤ |N| ≤ 2ⁿ·|form| + |Q|·d ≤ 1/2 + H·d, so d ≥ 1/(2H).
    have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hNz
    have hNle : |(N : ℝ)| ≤ 2 ^ n * |form| + |(Q : ℝ)| * d := by
      rw [hNid]
      calc |2 ^ n * form - (Q : ℝ) * (L * 2 ^ n - (p : ℝ))|
          ≤ |2 ^ n * form| + |(Q : ℝ) * (L * 2 ^ n - (p : ℝ))| := abs_sub _ _
        _ = 2 ^ n * |form| + |(Q : ℝ)| * d := by
            rw [abs_mul, abs_mul, hddef,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^n)]
    have hsmall : 2 ^ n * |form| ≤ 1 / 2 := by
      calc (2 : ℝ) ^ n * |form|
          ≤ 2 ^ n * ((Nat.lcmUpto (4 * n) : ℝ) * (1 / 5 : ℝ) ^ (4 * n)) := by
            apply mul_le_mul_of_nonneg_left hup (by positivity)
        _ ≤ 1 / 2 := h1
    have hHd : 1 / 2 ≤ H * d := by
      have : |(Q : ℝ)| * d ≤ H * d := mul_le_mul_of_nonneg_right hQle hd0
      linarith
    have h2H : 2 * H ≤ (2 : ℝ) ^ (26 * n) := by
      calc 2 * H = 2 * ((((4 * n : ℕ) : ℝ) + 1) * (8 : ℝ) ^ (4 * n) *
            (Nat.lcmUpto (4 * n) : ℝ)) := by rw [hHdef]
        _ ≤ (2 : ℝ) ^ (26 * n) := h2
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) ≤ 2 * (H * d) := by linarith
      _ = d * (2 * H) := by ring
      _ ≤ d * (2 : ℝ) ^ (26 * n) := mul_le_mul_of_nonneg_left h2H hd0

end NormalNumbers
