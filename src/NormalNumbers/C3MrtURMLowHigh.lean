/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtWindowMass

/-!
# `UniformResonantMass` (DIRECTION ②.4): the low/high split that tames the error tail

`C3MrtWindowMass` built the whole Brun–Titchmarsh toolkit for `UniformResonantMass`
(`resonant_window_mass_le`, `sum_inv_gap_le`, `windowIndexW`, `abs_windowIndexW_le`,
`sum_Icc_symm_le`, `sum_exp_neg_le`, `small_prime_mass_le`) but never assembled it, and the
assembly as sketched there **does not close**:

> `sum_exp_neg_le`: "With `c = π/(32|t|)` … this is the `1 + 32|t|/π` that the Brun–Titchmarsh
> error tail costs."

That cost is `O(|t|)`, and `UniformResonantMass` allows only
`100δ(log log Y + log(2+|t|)) + C` with `C` chosen **before** `t`.  So `O(|t|)` overshoots the
budget by an exponential, and the sketched route fails on its own error term.

**The repair (this file).**  Split the resonant primes at the height

    lowHeight t = 8 · log(2 + |t|)                  (in the variable `log p`)

instead of at an absolute constant.

* **Low range** `log p ≤ lowHeight t`: do *not* use windows at all — bound the whole range by
  Mertens (`small_prime_mass_le`), giving `log(lowHeight t) + mertensBound`, which is
  `O(log log(2+|t|))`.  That is a whole exponential *below* the `100δ·log(2+|t|)` the budget
  allows, and `log_log_absorb` below discharges the comparison for every fixed `δ > 0` (the
  constant absorbing it may depend on `δ`, which `UniformResonantMass` permits).
* **High range** `log p > lowHeight t`: every window now sits at height `a ≥ 8 log(2+|t|)`, so its
  Brun–Titchmarsh error carries the factor `exp(−a/8) ≤ (2+|t|)⁻¹`.  Summing over the windows,
  whose spacing in the height variable is `2π/|t|`, costs `≈ (|t|/2π)·8·(2+|t|)⁻¹ ≤ 4/π`:
  **the error tail is `O(1)`, not `O(|t|)`.**  The `|t|` from the window count is cancelled by the
  `(2+|t|)⁻¹` that the raised starting height supplies — which is exactly what the absolute
  starting height could not do.

This file lands the split, the low range, and the absorption inequality, and states the high
range as one named sorry (`highResonantMass_le`) carrying that error-tail computation.
-/

open Filter Topology Finset Real

namespace NormalNumbers

namespace CastingOut

/-- The height (in `log p`) at which the resonance analysis switches from Mertens to
Brun–Titchmarsh.  Growing like `log(2+|t|)` is the whole point: it is what makes the
Brun–Titchmarsh error tail summable to `O(1)` rather than `O(|t|)`. -/
noncomputable def lowHeight (t : ℝ) : ℝ := 8 * Real.log (2 + |t|)

theorem lowHeight_pos (t : ℝ) : 0 < lowHeight t := by
  have h : (1:ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
  have := Real.log_pos h
  rw [lowHeight]; linarith

theorem lowHeight_ge (t : ℝ) : 8 * Real.log 2 ≤ lowHeight t := by
  have h : (2:ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
  have := Real.log_le_log (by norm_num) h
  rw [lowHeight]; linarith

/-! ### The split -/

open scoped Classical in
/-- The resonant primes of height at most `lowHeight t`. -/
noncomputable def lowResonantMass (z : ℂ) (t : ℝ) (Y : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ ((Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ)).filter
      (fun p : ℕ => Real.log (p : ℝ) ≤ lowHeight t), (p : ℝ)⁻¹

open scoped Classical in
/-- The resonant primes of height above `lowHeight t`. -/
noncomputable def highResonantMass (z : ℂ) (t : ℝ) (Y : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ ((Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ)).filter
      (fun p : ℕ => ¬ Real.log (p : ℝ) ≤ lowHeight t), (p : ℝ)⁻¹

theorem resonantMass_eq_low_add_high (z : ℂ) (t : ℝ) (Y : ℕ) (δ : ℝ) :
    resonantMass z t Y δ = lowResonantMass z t Y δ + highResonantMass z t Y δ := by
  classical
  simp only [resonantMass, lowResonantMass, highResonantMass]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-! ### The low range is Mertens, and costs only `log log(2+|t|)` -/

/-- **The low range.**  No windows, no cancellation: the primes below height `lowHeight t` are
bounded by Mertens alone, at `log(lowHeight t) + 1 + mertensBound`. -/
theorem lowResonantMass_le (z : ℂ) (t : ℝ) (Y : ℕ) (δ : ℝ) :
    lowResonantMass z t Y δ
      ≤ Real.log (lowHeight t) + 1 + Erdos67b.PrimeEstimates.mertensBound := by
  classical
  rw [lowResonantMass]
  set G : Finset ℕ := ((Erdos67b.primesUpTo Y).filter
    (fun p => |(primePhase z t p).arg| < δ)).filter
    (fun p : ℕ => Real.log (p : ℝ) ≤ lowHeight t) with hG
  set B : ℕ := ⌈Real.exp (lowHeight t)⌉₊ with hB
  have hexp2 : (2:ℝ) ≤ Real.exp (lowHeight t) := by
    have h8 := lowHeight_ge t
    have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.log 2 ≤ lowHeight t := by linarith
    calc (2:ℝ) = Real.exp (Real.log 2) := by rw [Real.exp_log]; norm_num
      _ ≤ Real.exp (lowHeight t) := Real.exp_le_exp.2 this
  have hBR : (2:ℝ) ≤ (B : ℝ) := le_trans hexp2 (Nat.le_ceil _)
  have hB2 : (2:ℕ) ≤ B := by exact_mod_cast hBR
  -- every prime in the low range is `≤ B`
  have hGb : ∀ p ∈ G, p.Prime ∧ p ≤ B := by
    intro p hp
    rw [hG] at hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    have hpp : p.Prime := (Erdos67b.mem_primesUpTo.1 (Finset.mem_filter.1 hp1).1).1
    refine ⟨hpp, ?_⟩
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hle : (p:ℝ) ≤ Real.exp (lowHeight t) := by
      rw [← Real.exp_log hp0]
      exact Real.exp_le_exp.2 hp2
    have : (p:ℝ) ≤ (B:ℝ) := le_trans hle (Nat.le_ceil _)
    exact_mod_cast this
  have hmass := small_prime_mass_le hB2 hGb
  refine le_trans hmass ?_
  -- `log B ≤ lowHeight t + 1`, hence `log log B ≤ log (lowHeight t) + …`
  have hBle : (B:ℝ) ≤ Real.exp (lowHeight t) + 1 := le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hlogB : Real.log (B:ℝ) ≤ lowHeight t + 1 := by
    have h1 : Real.log (B:ℝ) ≤ Real.log (Real.exp (lowHeight t) + 1) :=
      Real.log_le_log (by linarith) hBle
    have h2 : Real.exp (lowHeight t) + 1 ≤ Real.exp (lowHeight t + 1) := by
      have hmul : Real.exp (lowHeight t + 1) = Real.exp (lowHeight t) * Real.exp 1 := by
        rw [Real.exp_add]
      have he1 : (2:ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have hpos : (0:ℝ) < Real.exp (lowHeight t) := Real.exp_pos _
      nlinarith [hmul, hexp2]
    have h3 : Real.log (Real.exp (lowHeight t) + 1) ≤ lowHeight t + 1 := by
      have := Real.log_le_log (by positivity) h2
      rwa [Real.log_exp] at this
    linarith
  have hLpos := lowHeight_pos t
  have hlogBpos : 0 < Real.log (B:ℝ) := Real.log_pos (by linarith)
  have houter : Real.log (Real.log (B:ℝ)) ≤ Real.log (lowHeight t + 1) :=
    Real.log_le_log hlogBpos hlogB
  -- and `log(L+1) ≤ log L + 1/L ≤ log L + 1/(8 log 2)`
  have hstep : Real.log (lowHeight t + 1) ≤ Real.log (lowHeight t) + 1 / lowHeight t := by
    have hfrac : Real.log ((lowHeight t + 1) / lowHeight t) ≤ 1 / lowHeight t := by
      have h := Real.log_le_sub_one_of_pos
        (show (0:ℝ) < (lowHeight t + 1) / lowHeight t by positivity)
      have heq : (lowHeight t + 1) / lowHeight t - 1 = 1 / lowHeight t := by
        field_simp
        ring
      linarith [heq ▸ h]
    have hdiv : Real.log ((lowHeight t + 1) / lowHeight t)
        = Real.log (lowHeight t + 1) - Real.log (lowHeight t) :=
      Real.log_div (by linarith) (ne_of_gt hLpos)
    linarith [hdiv ▸ hfrac]
  have hinv : 1 / lowHeight t ≤ 1 / (8 * Real.log 2) := by
    have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact one_div_le_one_div_of_le (by positivity) (lowHeight_ge t)
  have hsmall : 1 / (8 * Real.log 2) ≤ 1 := by
    have hl2 : Real.log 2 ≥ 1/2 := by nlinarith [Real.log_two_gt_d9]
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hmert := Erdos67b.PrimeEstimates.mertensBound_nonneg
  linarith

/-! ### The absorption: `log log(2+|t|)` fits inside `ε · log(2+|t|)` -/

/-- `log w ≤ ε·w + (log(1/ε) − 1)` for `ε, w > 0`: the tangent-line bound, which is how the low
range's `log log(2+|t|)` is absorbed into the budget's `100δ·log(2+|t|)` for every fixed `δ`. -/
theorem log_le_eps_mul {ε : ℝ} (hε : 0 < ε) {w : ℝ} (hw : 0 < w) :
    Real.log w ≤ ε * w + (Real.log (1/ε) - 1) := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ε * w by positivity)
  rw [Real.log_mul (ne_of_gt hε) (ne_of_gt hw)] at h
  have hlog : Real.log (1/ε) = - Real.log ε := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  linarith

/-- **The absorption, in the form the assembly needs.**  For every `ε > 0` there is a constant
`C(ε)` with `log (lowHeight t) ≤ ε · log(2+|t|) + C(ε)` for all `t` — so the low range never
exceeds the budget, no matter how large `|t|` is. -/
theorem log_lowHeight_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Real.log (lowHeight t)
      ≤ ε * Real.log (2 + |t|) + (Real.log 8 + Real.log (1/ε) - 1) := by
  have hlog2 : (0:ℝ) < Real.log (2 + |t|) := by
    have := abs_nonneg t
    exact Real.log_pos (by linarith)
  have hsplit : Real.log (lowHeight t) = Real.log 8 + Real.log (Real.log (2 + |t|)) := by
    rw [lowHeight, Real.log_mul (by norm_num) (ne_of_gt hlog2)]
  rw [hsplit]
  have := log_le_eps_mul hε hlog2
  linarith

/-! ### The high range: the error tail, and the one remaining obligation -/

/-- **The high range — the remaining obligation of `UniformResonantMass`.**

Above height `lowHeight t = 8 log(2+|t|)` the resonant primes are covered by the windows
`|t| log p ∈ (γ_m − δ, γ_m + δ)`, `γ_m = |arg z − 2πm| ≥ 2δ`, and `resonant_window_mass_le`
bounds window `m` by `16δ/(|t| a_m) + 6(1+a_m)³ exp(−a_m/2)` with `a_m = (γ_m − δ)/|t|`.

* The **main terms** sum to `≤ (32δ/π)(1 + log K) + O(δ)` by `sum_inv_gap_le` and
  `sum_Icc_symm_le`, with `K ≈ (|t| log Y + δ + π)/(2π)` by `abs_windowIndexW_le`, so
  `log K ≤ log log Y + log(2+|t|) + O(1)` — inside the `100δ(...)` budget, since `32/π < 11`.
* The **error terms** are where the sketched route in `C3MrtWindowMass` failed.  Because every
  window here has `a_m ≥ lowHeight t = 8 log(2+|t|)`, each error carries
  `exp(−a_m/8) ≤ (2+|t|)⁻¹`, and the windows are spaced `2π/|t|` apart in `a`, so the tail sums
  to `≲ (|t|/2π) · 8 · (2+|t|)⁻¹ ≤ 4/π = O(1)` via `sum_exp_neg_le` and `window_err_le`.  The
  `|t|` of the window count is cancelled by the `(2+|t|)⁻¹` the raised starting height supplies.

Disclosed as a `sorry`: this is the Brun–Titchmarsh bookkeeping, not a further analytic input —
every ingredient it needs is already proved in `C3MrtWindowMass`. -/
theorem highResonantMass_le {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z)
    (t : ℝ) {Y : ℕ} (hY : 2 ≤ Y) :
    highResonantMass z t Y δ
      ≤ 50 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|)) + (4 / Real.pi + 40 * δ) := by
  sorry

/-- **`UniformResonantMass`, modulo the high range.**  With `highResonantMass_le` in hand the
low/high split closes the statement: the low range contributes
`ε·log(2+|t|) + C(ε)` with `ε = 50δ`, the high range the rest, and `100δ = 50δ + 50δ` covers
both.  This is the shape `UniformResonantMass` asks for, with `C` depending only on `z` and `δ`. -/
theorem uniformResonantMass_of_high {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ resEps z) (t : ℝ) {Y : ℕ} (hY : 2 ≤ Y) :
    resonantMass z t Y δ
      ≤ 100 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|))
        + (Real.log 8 + Real.log (1/(50*δ)) - 1 + Erdos67b.PrimeEstimates.mertensBound
            + (4 / Real.pi + 40 * δ) + 25 * δ + 1) := by
  have hlow := lowResonantMass_le z t Y δ
  have habs := log_lowHeight_le (show (0:ℝ) < 50 * δ by linarith) t
  have hhigh := highResonantMass_le hz hδ0 hδ t hY
  have hsplit := resonantMass_eq_low_add_high z t Y δ
  have hll : (0:ℝ) ≤ Real.log (2 + |t|) := by
    have := abs_nonneg t
    exact Real.log_nonneg (by linarith)
  -- `log log Y ≥ log log 2 > −1/2` for `Y ≥ 2`, which is what the `25δ` in the constant pays for
  have hlogY : Real.log 2 ≤ Real.log (Y : ℝ) := by
    have : (2:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
    exact Real.log_le_log (by norm_num) this
  have hexph : (1.6:ℝ) < Real.exp (1/2) := by
    have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos (1/2 : ℝ), hsq]
  have hlog2gt : Real.exp (-(1/2 : ℝ)) < Real.log 2 := by
    have hinv : Real.exp (-(1/2:ℝ)) = 1 / Real.exp (1/2) := by
      rw [Real.exp_neg]; ring
    have h16 : 1 / Real.exp (1/2) < 1 / 1.6 :=
      one_div_lt_one_div_of_lt (by norm_num) hexph
    have := Real.log_two_gt_d9
    rw [hinv]
    nlinarith
  have hloglogY : -(1/2 : ℝ) ≤ Real.log (Real.log (Y : ℝ)) := by
    have hpos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : Real.log (Real.exp (-(1/2:ℝ))) ≤ Real.log (Real.log (Y:ℝ)) :=
      Real.log_le_log (Real.exp_pos _) (le_trans hlog2gt.le hlogY)
    rwa [Real.log_exp] at h1
  rw [hsplit]
  nlinarith [hlow, habs, hhigh, hloglogY, hδ0]

end CastingOut

end NormalNumbers
