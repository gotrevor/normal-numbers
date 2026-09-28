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

    lowHeight t = 16 · log(2 + |t|)                 (in the variable `log p`)

instead of at an absolute constant.

* **Low range** `log p ≤ lowHeight t`: do *not* use windows at all — bound the whole range by
  Mertens (`small_prime_mass_le`), giving `log(lowHeight t) + mertensBound`, which is
  `O(log log(2+|t|))`.  That is a whole exponential *below* the `100δ·log(2+|t|)` the budget
  allows, and `log_log_absorb` below discharges the comparison for every fixed `δ > 0` (the
  constant absorbing it may depend on `δ`, which `UniformResonantMass` permits).
* **High range** `log p > lowHeight t`: the effective start of window `m` is
  `aWin = max((γ_m − δ)/|t|, lowHeight t) ≥ (lowHeight t + (γ_m − δ)/|t|)/2`, so its
  Brun–Titchmarsh error carries `exp(−aWin/8) ≤ exp(−lowHeight t/16)·exp(−(γ_m−δ)/(16|t|))`
  `= (2+|t|)⁻¹ · exp(−(γ_m−δ)/(16|t|))`.  **The `16` in `lowHeight` is exactly the factor `2`
  that `max ≥ average` costs**: at `8` the surviving factor would be only `(2+|t|)^{-1/2}`, which
  does not beat the `O(|t|)` window count, and the repair would fail for the same reason the
  original plan did.  Summing over the windows,
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
noncomputable def lowHeight (t : ℝ) : ℝ := 16 * Real.log (2 + |t|)

theorem lowHeight_pos (t : ℝ) : 0 < lowHeight t := by
  have h : (1:ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
  have := Real.log_pos h
  rw [lowHeight]; linarith

theorem lowHeight_ge (t : ℝ) : 8 * Real.log 2 ≤ lowHeight t := by
  have h : (2:ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
  have h2 := Real.log_le_log (by norm_num) h
  have h3 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [lowHeight]; linarith

/-- `exp(−lowHeight t / 16) = (2 + |t|)⁻¹` — the factor that cancels the window count. -/
theorem exp_neg_lowHeight (t : ℝ) :
    Real.exp (-(lowHeight t / 16)) = (2 + |t|)⁻¹ := by
  have hpos : (0:ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
  have h : lowHeight t / 16 = Real.log (2 + |t|) := by rw [lowHeight]; ring
  rw [h, Real.exp_neg, Real.exp_log hpos]

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
      ≤ ε * Real.log (2 + |t|) + (Real.log 16 + Real.log (1/ε) - 1) := by
  have hlog2 : (0:ℝ) < Real.log (2 + |t|) := by
    have := abs_nonneg t
    exact Real.log_pos (by linarith)
  have hsplit : Real.log (lowHeight t) = Real.log 16 + Real.log (Real.log (2 + |t|)) := by
    rw [lowHeight, Real.log_mul (by norm_num) (ne_of_gt hlog2)]
  rw [hsplit]
  have := log_le_eps_mul hε hlog2
  linarith

/-! ### Narrowing the open leaf: the window partition, the small-`Y` case, and `log K`

Three of the five steps of `highResonantMass_le` are discharged here, leaving only the
per-window estimate and its summation. -/

/-- The number of resonance windows that can meet `[2, Y]`. -/
noncomputable def resWindowCount (t δ : ℝ) (Y : ℕ) : ℕ :=
  ⌈(|t| * Real.log (Y : ℝ) + δ + Real.pi) / (2 * Real.pi)⌉₊

open scoped Classical in
/-- The reciprocal mass of the high-range resonant primes in window `m`. -/
noncomputable def windowMass (z : ℂ) (t : ℝ) (Y : ℕ) (δ : ℝ) (m : ℤ) : ℝ :=
  ∑ p ∈ (((Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ)).filter
      (fun p : ℕ => ¬ Real.log (p : ℝ) ≤ lowHeight t)).filter
      (fun p => windowIndexW z t δ p = m), (p : ℝ)⁻¹

/-- **Step 1 — the window partition.**  Every high-range resonant prime lands in exactly one
window of index `|m| ≤ resWindowCount t δ Y`, so the high mass is the sum of the window masses. -/
theorem highResonantMass_eq_sum_windows {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ : δ ≤ resEps z)
    (t : ℝ) (Y : ℕ) :
    highResonantMass z t Y δ
      = ∑ m ∈ Finset.Icc (-(resWindowCount t δ Y : ℤ)) (resWindowCount t δ Y : ℤ),
          windowMass z t Y δ m := by
  classical
  rw [highResonantMass]
  refine (Finset.sum_fiberwise_of_maps_to (g := fun p => windowIndexW z t δ p) ?_ _).symm
  intro p hp
  obtain ⟨hp1, _⟩ := Finset.mem_filter.1 hp
  obtain ⟨hpY, hres⟩ := Finset.mem_filter.1 hp1
  obtain ⟨hpp, hple⟩ := Erdos67b.mem_primesUpTo.1 hpY
  have hp2 : 2 ≤ p := hpp.two_le
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
  have hlogle : Real.log (p:ℝ) ≤ Real.log (Y:ℝ) := by
    have : (p:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hple
    exact Real.log_le_log hp0 this
  have hT : |t| * Real.log (p:ℝ) ≤ |t| * Real.log (Y:ℝ) :=
    mul_le_mul_of_nonneg_left hlogle (abs_nonneg t)
  have hbd := abs_windowIndexW_le hz hp2 hδ hres hT
  rw [Finset.mem_Icc]
  rw [resWindowCount]
  constructor
  · have := abs_le.1 hbd |>.1; omega
  · have := abs_le.1 hbd |>.2; omega

/-- **Step 1b — the small-`Y` case is trivial.**  If `log Y` does not even reach the split height
there is no high range at all; in particular this covers `Y = 2`, where
`log 2 < 8 log 2 ≤ lowHeight t`. -/
theorem highResonantMass_eq_zero {z : ℂ} {δ : ℝ} {t : ℝ} {Y : ℕ}
    (h : Real.log (Y : ℝ) ≤ lowHeight t) : highResonantMass z t Y δ = 0 := by
  classical
  rw [highResonantMass, Finset.sum_eq_zero]
  intro p hp
  exfalso
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
  obtain ⟨hpY, _⟩ := Finset.mem_filter.1 hp1
  obtain ⟨hpp, hple⟩ := Erdos67b.mem_primesUpTo.1 hpY
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
  have hlogle : Real.log (p:ℝ) ≤ Real.log (Y:ℝ) := by
    have : (p:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hple
    exact Real.log_le_log hp0 this
  exact hp2 (le_trans hlogle h)

/-- **Step 3a — the window count is at most `(2+|t|)·log Y`,** so `log K` costs exactly the
budget's two terms and nothing more: `log K ≤ log(2+|t|) + log log Y`, with constant `0`. -/
theorem resWindowCount_le {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi / 2) (t : ℝ) {Y : ℕ}
    (hY : 3 ≤ Y) :
    ((resWindowCount t δ Y : ℕ) : ℝ) ≤ (2 + |t|) * Real.log (Y : ℝ) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hYR : (3:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hlogY : (1:ℝ) < Real.log (Y:ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (Y:ℝ) := Real.log_le_log (by norm_num) hYR
    have : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      nlinarith [Real.exp_one_lt_d9]
    linarith
  have ht0 : (0:ℝ) ≤ |t| := abs_nonneg t
  set A : ℝ := (|t| * Real.log (Y:ℝ) + δ + Real.pi) / (2 * Real.pi) with hA
  have hceil : ((resWindowCount t δ Y : ℕ) : ℝ) ≤ A + 1 := by
    rw [resWindowCount, ← hA]
    exact le_of_lt (Nat.ceil_lt_add_one (by
      rw [hA]
      have : (0:ℝ) ≤ |t| * Real.log (Y:ℝ) := by positivity
      positivity))
  refine le_trans hceil ?_
  have hAsplit : A = |t| * Real.log (Y:ℝ) / (2 * Real.pi) + (δ + Real.pi) / (2 * Real.pi) := by
    rw [hA]; ring
  have h34 : (δ + Real.pi) / (2 * Real.pi) ≤ 3 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hAle : A ≤ |t| * Real.log (Y:ℝ) / (2 * Real.pi) + 3 / 4 := by
    rw [hAsplit]; linarith
  have hnn : (0:ℝ) ≤ |t| * Real.log (Y:ℝ) := by
    have : (0:ℝ) ≤ Real.log (Y:ℝ) := by linarith
    positivity
  have h1 : |t| * Real.log (Y:ℝ) / (2 * Real.pi) ≤ |t| * Real.log (Y:ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, hnn]
  have h2 : (3:ℝ)/4 + 1 ≤ 2 * Real.log (Y:ℝ) := by linarith
  linarith

/-! ### Step 2: the per-window estimate, at the raised starting height

The split supplies the window's starting height for free: a high-range prime in window `m` has
`log p` both `> (γ_m − δ)/|t|` and `> lowHeight t`, so the effective start is the **max** of the
two, which is `≥ lowHeight t ≥ 8 log 2` — and that is simultaneously

* the `log 2 ≤ a` hypothesis of `resonant_window_mass_le`, for free, and
* the `exp(−a/8) ≤ (2+|t|)⁻¹` that makes the error tail summable to `O(1)`.

Raising the start does not weaken the main term: it only ever *decreases* `16δ/(|t|·a)`, and
`aWin_ge_gap` keeps the comparison with `γ_m − δ` that `sum_inv_gap_le` needs. -/

/-- The effective starting height of window `m` in the high range. -/
noncomputable def aWin (z : ℂ) (t δ : ℝ) (m : ℤ) : ℝ :=
  max ((|z.arg - 2 * Real.pi * m| - δ) / |t|) (lowHeight t)

theorem aWin_ge_low (z : ℂ) (t δ : ℝ) (m : ℤ) : lowHeight t ≤ aWin z t δ m := le_max_right _ _

theorem aWin_ge_gap (z : ℂ) (t δ : ℝ) (m : ℤ) :
    (|z.arg - 2 * Real.pi * m| - δ) / |t| ≤ aWin z t δ m := le_max_left _ _

theorem aWin_ge_log_two (z : ℂ) (t δ : ℝ) (m : ℤ) : Real.log 2 ≤ aWin z t δ m := by
  have h1 := aWin_ge_low z t δ m
  have h2 := lowHeight_ge t
  have h3 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- **Step 2 — the per-window mass, short-window case `2δ ≤ |t|`.**  Brun–Titchmarsh at the
raised starting height. -/
theorem windowMass_le {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z)
    {t : ℝ} (ht : 2 * δ ≤ |t|) (Y : ℕ) (m : ℤ) :
    windowMass z t Y δ m
      ≤ 16 * δ / (|t| * aWin z t δ m)
        + 6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m)) := by
  classical
  have htpos : (0:ℝ) < |t| := by linarith
  rw [windowMass]
  refine resonant_window_mass_le hδ0 ht (aWin_ge_log_two z t δ m) ?_ ?_
  · intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp2, _⟩ := Finset.mem_filter.1 hp1
    exact (Erdos67b.mem_primesUpTo.1 (Finset.mem_filter.1 hp2).1).1
  · intro p hp
    obtain ⟨hp1, hpm⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp2, hphigh⟩ := Finset.mem_filter.1 hp1
    obtain ⟨hpY, hres⟩ := Finset.mem_filter.1 hp2
    obtain ⟨hpp, _⟩ := Erdos67b.mem_primesUpTo.1 hpY
    have hp2le : 2 ≤ p := hpp.two_le
    obtain ⟨hlo, hhi⟩ := windowIndexW_spec hz hp2le hδ hres
    rw [hpm] at hlo hhi
    have hgaplt : (|z.arg - 2 * Real.pi * m| - δ) / |t| < Real.log (p:ℝ) := by
      rw [div_lt_iff₀ htpos]
      calc |z.arg - 2 * Real.pi * m| - δ < |t| * Real.log (p:ℝ) := hlo
        _ = Real.log (p:ℝ) * |t| := by ring
    have hhighlt : lowHeight t < Real.log (p:ℝ) := lt_of_not_ge hphigh
    refine ⟨max_lt hgaplt hhighlt, ?_⟩
    -- `log p < (γ_m + δ)/|t| = (γ_m − δ)/|t| + 2δ/|t| ≤ aWin + 2δ/|t|`
    have hupper : Real.log (p:ℝ) < (|z.arg - 2 * Real.pi * m| + δ) / |t| := by
      rw [lt_div_iff₀ htpos]
      calc Real.log (p:ℝ) * |t| = |t| * Real.log (p:ℝ) := by ring
        _ < |z.arg - 2 * Real.pi * m| + δ := hhi
    have hsplit : (|z.arg - 2 * Real.pi * m| + δ) / |t|
        = (|z.arg - 2 * Real.pi * m| - δ) / |t| + 2 * δ / |t| := by
      field_simp
      ring
    have hmono : (|z.arg - 2 * Real.pi * m| - δ) / |t| + 2 * δ / |t|
        ≤ aWin z t δ m + 2 * δ / |t| := by
      have := aWin_ge_gap z t δ m; linarith
    calc Real.log (p:ℝ) < (|z.arg - 2 * Real.pi * m| + δ) / |t| := hupper
      _ = (|z.arg - 2 * Real.pi * m| - δ) / |t| + 2 * δ / |t| := hsplit
      _ ≤ aWin z t δ m + 2 * δ / |t| := hmono

/-- The main term at the raised height is still controlled by the *gap* `γ_m − δ`, so
`sum_inv_gap_le` applies unchanged: raising the start only helps. -/
theorem windowMass_main_le {z : ℂ} {δ : ℝ} (hδ0 : 0 < δ) {t : ℝ} (ht : 2 * δ ≤ |t|) (m : ℤ)
    (hgap : 0 < |z.arg - 2 * Real.pi * m| - δ) :
    16 * δ / (|t| * aWin z t δ m) ≤ 16 * δ / (|z.arg - 2 * Real.pi * m| - δ) := by
  have htpos : (0:ℝ) < |t| := by linarith
  have hge := aWin_ge_gap z t δ m
  have hmul : |z.arg - 2 * Real.pi * m| - δ ≤ |t| * aWin z t δ m := by
    rw [div_le_iff₀ htpos] at hge
    have hcomm : aWin z t δ m * |t| = |t| * aWin z t δ m := mul_comm _ _
    rw [hcomm] at hge
    exact hge
  have hpos : (0:ℝ) < |t| * aWin z t δ m := by
    have := aWin_ge_log_two z t δ m
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have : (0:ℝ) < aWin z t δ m := by linarith
    positivity
  exact div_le_div_of_nonneg_left (by linarith) hgap hmul

/-! ### Step 3: summing the main terms over the windows

The bound function is taken to be `16δ / max(2π|m| − π − δ, δ)`, which is **nonneg for every
`m`** — including `m = 0`, where the naive `2π|m| − π − δ` is negative.  That is what lets
`sum_Icc_symm_le` (which needs a nonneg function of `|m|`) apply directly, with no separate
treatment of the central window: the `max` absorbs it, because `γ_m − δ ≥ δ` always holds
(`γ_m ≥ 2·resEps z ≥ 2δ` by `two_resEps_le_abs_shift`). -/

/-- The nonneg majorant of the per-window main term. -/
noncomputable def gapMaj (δ : ℝ) (x : ℝ) : ℝ := 16 * δ / max (2 * Real.pi * x - Real.pi - δ) δ

theorem gapMaj_nonneg {δ : ℝ} (hδ0 : 0 < δ) (x : ℝ) : 0 ≤ gapMaj δ x := by
  rw [gapMaj]
  have : (0:ℝ) < max (2 * Real.pi * x - Real.pi - δ) δ := lt_of_lt_of_le hδ0 (le_max_right _ _)
  positivity

/-- The per-window main term is majorised by `gapMaj` at `|m|`. -/
theorem main_term_le_gapMaj {z : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z) (m : ℤ) :
    16 * δ / (|z.arg - 2 * Real.pi * m| - δ) ≤ gapMaj δ |(m : ℝ)| := by
  have hgap2 : 2 * resEps z ≤ |z.arg - 2 * Real.pi * m| := two_resEps_le_abs_shift z m
  have hγ : 2 * δ ≤ |z.arg - 2 * Real.pi * m| := by linarith
  have hden : (0:ℝ) < |z.arg - 2 * Real.pi * m| - δ := by linarith
  -- both branches of the `max` are `≤ γ_m − δ`
  have h1 : 2 * Real.pi * |(m:ℝ)| - Real.pi - δ ≤ |z.arg - 2 * Real.pi * m| - δ := by
    have h2 : |z.arg| ≤ Real.pi := Complex.abs_arg_le_pi z
    have h3 := abs_sub_abs_le_abs_sub (2 * Real.pi * (m : ℝ)) z.arg
    rw [abs_sub_comm] at h3
    have h4 : |2 * Real.pi * (m : ℝ)| = 2 * Real.pi * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    linarith [h4 ▸ h3]
  have h2 : δ ≤ |z.arg - 2 * Real.pi * m| - δ := by linarith
  have hmax : max (2 * Real.pi * |(m:ℝ)| - Real.pi - δ) δ ≤ |z.arg - 2 * Real.pi * m| - δ :=
    max_le h1 h2
  have hmaxpos : (0:ℝ) < max (2 * Real.pi * |(m:ℝ)| - Real.pi - δ) δ :=
    lt_of_lt_of_le hδ0 (le_max_right _ _)
  rw [gapMaj]
  exact div_le_div_of_nonneg_left (by linarith) hmaxpos hmax

/-- `range (K+1)` is `{0} ∪ Icc 1 K`, the split that separates the central window. -/
theorem range_succ_eq_insert_Icc (K : ℕ) :
    Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
  ext j
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- **Step 3 — the main terms sum inside the budget.**  `∑_{|m| ≤ K} 16δ/(γ_m − δ) ≤ 32 +
(64δ/π)(1 + log K)`: the central window contributes the absolute constant, and the rest is the
harmonic sum of `sum_inv_gap_le`.  Since `64/π < 22 < 50`, this sits well inside the
`50δ(log log Y + log(2+|t|))` the split allots to the high range. -/
theorem main_sum_le {z : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z) (K : ℕ) :
    ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), 16 * δ / (|z.arg - 2 * Real.pi * m| - δ)
      ≤ 32 + (64 * δ / Real.pi) * (1 + Real.log K) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hδπ : δ ≤ Real.pi / 2 := le_trans hδ (resEps_le_pi_div_two z)
  -- majorise termwise, then use the symmetric-sum brick
  have hstep1 : ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      16 * δ / (|z.arg - 2 * Real.pi * m| - δ)
      ≤ ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), gapMaj δ |(m : ℝ)| :=
    Finset.sum_le_sum fun m _ => main_term_le_gapMaj hδ0 hδ m
  have hstep2 : ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), gapMaj δ |(m : ℝ)|
      ≤ 2 * ∑ j ∈ Finset.range (K + 1), gapMaj δ (j : ℝ) :=
    sum_Icc_symm_le (gapMaj δ) (gapMaj_nonneg hδ0)
  -- the central window is an absolute constant, the rest is harmonic
  have hzero : gapMaj δ 0 = 16 := by
    rw [gapMaj]
    have hmax : max (2 * Real.pi * 0 - Real.pi - δ) δ = δ := by
      refine max_eq_right ?_
      linarith
    rw [hmax]
    field_simp
  have htail : ∀ j ∈ Finset.Icc 1 K,
      gapMaj δ (j : ℝ) ≤ 16 * δ * (2 * Real.pi * (j : ℝ) - Real.pi - δ)⁻¹ := by
    intro j hj
    have hj1 : (1:ℝ) ≤ (j : ℝ) := by
      have := (Finset.mem_Icc.1 hj).1; exact_mod_cast this
    have hgap0 : (0:ℝ) < 2 * Real.pi * (j : ℝ) - Real.pi - δ := by nlinarith
    rw [gapMaj]
    have hge : 2 * Real.pi * (j : ℝ) - Real.pi - δ
        ≤ max (2 * Real.pi * (j : ℝ) - Real.pi - δ) δ := le_max_left _ _
    calc 16 * δ / max (2 * Real.pi * (j : ℝ) - Real.pi - δ) δ
        ≤ 16 * δ / (2 * Real.pi * (j : ℝ) - Real.pi - δ) :=
          div_le_div_of_nonneg_left (by linarith) hgap0 hge
      _ = 16 * δ * (2 * Real.pi * (j : ℝ) - Real.pi - δ)⁻¹ := by
          rw [div_eq_mul_inv]
  have hharm := sum_inv_gap_le hδ0.le hδπ K
  have hsplit : ∑ j ∈ Finset.range (K + 1), gapMaj δ (j : ℝ)
      = gapMaj δ 0 + ∑ j ∈ Finset.Icc 1 K, gapMaj δ (j : ℝ) := by
    rw [range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
    norm_num
  have htailsum : ∑ j ∈ Finset.Icc 1 K, gapMaj δ (j : ℝ)
      ≤ 16 * δ * ((2 / Real.pi) * (1 + Real.log K)) := by
    refine le_trans (Finset.sum_le_sum htail) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hharm (by positivity)
  have hfin : 2 * ∑ j ∈ Finset.range (K + 1), gapMaj δ (j : ℝ)
      ≤ 32 + (64 * δ / Real.pi) * (1 + Real.log K) := by
    rw [hsplit, hzero]
    have : (0:ℝ) < Real.pi := hpi
    have heq : 2 * (16 * δ * ((2 / Real.pi) * (1 + Real.log K)))
        = (64 * δ / Real.pi) * (1 + Real.log K) := by
      field_simp; ring
    nlinarith [htailsum, heq]
  linarith [hstep1, hstep2, hfin]

/-! ### Step 4: the error tail sums to an ABSOLUTE constant

This is the step the plan sketched in `C3MrtWindowMass` got wrong (it costs `O(|t|)` there).  The
whole repair is visible in `err_term_le`: because the effective start is a `max`, it dominates the
*average* of the two lower bounds, so the Brun–Titchmarsh factor `exp(−aWin/8)` splits as

    exp(−lowHeight t/16) · exp(−(γ_m − δ)/(16|t|))  =  (2+|t|)⁻¹ · exp(−(γ_m − δ)/(16|t|)),

the first factor independent of `m` and the second summable to `O(1+|t|)`.  The product is `O(1)`.
Note the `16` in `lowHeight` is not cosmetic: `max ≥ average` costs a factor `2`, and at a split
height of `8 log(2+|t|)` the surviving factor would be `(2+|t|)^{-1/2}`, too weak to beat the
`O(|t|)` window count. -/

/-- The window gap in the height variable. -/
noncomputable def gWin (z : ℂ) (t δ : ℝ) (m : ℤ) : ℝ := (|z.arg - 2 * Real.pi * m| - δ) / |t|

/-- `max` dominates the average — the inequality the whole error-tail repair rests on. -/
theorem aWin_ge_avg (z : ℂ) (t δ : ℝ) (m : ℤ) :
    (lowHeight t + gWin z t δ m) / 2 ≤ aWin z t δ m := by
  rw [aWin, gWin]
  rcases le_total ((|z.arg - 2 * Real.pi * m| - δ) / |t|) (lowHeight t) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- **The split of the Brun–Titchmarsh error factor.** -/
theorem err_term_le (z : ℂ) (t δ : ℝ) (m : ℤ) :
    6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m))
      ≤ 100000 * ((2 + |t|)⁻¹ * Real.exp (-(gWin z t δ m / 16))) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : (0:ℝ) ≤ aWin z t δ m := le_trans hlog2.le (aWin_ge_log_two z t δ m)
  refine le_trans (window_err_le ha0) ?_
  have havg := aWin_ge_avg z t δ m
  have hexp : -(aWin z t δ m / 8) ≤ -(lowHeight t / 16) + -(gWin z t δ m / 16) := by linarith
  have hmono : Real.exp (-(aWin z t δ m / 8))
      ≤ Real.exp (-(lowHeight t / 16)) * Real.exp (-(gWin z t δ m / 16)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 hexp
  rw [exp_neg_lowHeight] at hmono
  have : (0:ℝ) ≤ (100000 : ℝ) := by norm_num
  nlinarith [hmono, Real.exp_pos (-(gWin z t δ m / 16))]

/-- The gap grows linearly in `|m|`, so the second factor decays geometrically. -/
theorem exp_neg_gWin_le {z : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z) {t : ℝ}
    (ht : 2 * δ ≤ |t|) (m : ℤ) :
    Real.exp (-(gWin z t δ m / 16))
      ≤ Real.exp (-(Real.pi / (32 * |t|) * |(m : ℝ)|)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have htpos : (0:ℝ) < |t| := by linarith
  have hδπ : δ ≤ Real.pi / 2 := le_trans hδ (resEps_le_pi_div_two z)
  have hgap2 : 2 * resEps z ≤ |z.arg - 2 * Real.pi * m| := two_resEps_le_abs_shift z m
  have hγ : 2 * δ ≤ |z.arg - 2 * Real.pi * m| := by linarith
  -- `2(γ_m − δ) ≥ π|m|`
  have hkey : Real.pi * |(m : ℝ)| ≤ 2 * (|z.arg - 2 * Real.pi * m| - δ) := by
    rcases eq_or_ne m 0 with rfl | hm
    · have hz0 : ((0:ℤ) : ℝ) = 0 := by norm_num
      rw [hz0, mul_zero, abs_zero, mul_zero, sub_zero]
      rw [hz0, mul_zero, sub_zero] at hγ
      linarith
    · have hm1 : (1:ℝ) ≤ |(m : ℝ)| := by
        have h1 : (1:ℤ) ≤ |m| := Int.one_le_abs (by omega)
        rw [← Int.cast_abs]
        exact_mod_cast h1
      have hlow : 2 * Real.pi * |(m:ℝ)| - Real.pi ≤ |z.arg - 2 * Real.pi * m| := by
        have h2 : |z.arg| ≤ Real.pi := Complex.abs_arg_le_pi z
        have h3 := abs_sub_abs_le_abs_sub (2 * Real.pi * (m : ℝ)) z.arg
        rw [abs_sub_comm] at h3
        have h4 : |2 * Real.pi * (m : ℝ)| = 2 * Real.pi * |(m : ℝ)| := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        linarith [h4 ▸ h3]
      nlinarith
  refine Real.exp_le_exp.2 ?_
  rw [neg_le_neg_iff]
  have hL : Real.pi / (32 * |t|) * |(m:ℝ)| = (Real.pi * |(m:ℝ)|) / (32 * |t|) := by ring
  have hR : gWin z t δ m / 16 = (|z.arg - 2 * Real.pi * m| - δ) / (16 * |t|) := by
    rw [gWin]; field_simp
  rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, htpos, abs_nonneg ((m:ℝ))]

/-- **Step 4 — the error tail is an ABSOLUTE constant.**  `∑_{|m| ≤ K}` of the Brun–Titchmarsh
errors is at most `2200000`, uniformly in `t`, `K` and `z`.  This is where the old plan's
`O(|t|)` becomes `O(1)`. -/
theorem err_sum_le {z : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z) {t : ℝ}
    (ht : 2 * δ ≤ |t|) (K : ℕ) :
    ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m))
      ≤ 2200000 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have htpos : (0:ℝ) < |t| := by linarith
  set c : ℝ := Real.pi / (32 * |t|) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hinvpos : (0:ℝ) < (2 + |t|)⁻¹ := by positivity
  -- termwise: `≤ 100000 · (2+|t|)⁻¹ · exp(−c|m|)`
  have hstep1 : ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m))
      ≤ ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (100000 * (2 + |t|)⁻¹) * Real.exp (-(c * |(m : ℝ)|)) := by
    refine Finset.sum_le_sum fun m _ => ?_
    have h1 := err_term_le z t δ m
    have h2 := exp_neg_gWin_le hδ0 hδ ht m
    have h3 : (100000:ℝ) * ((2 + |t|)⁻¹ * Real.exp (-(gWin z t δ m / 16)))
        ≤ (100000 * (2 + |t|)⁻¹) * Real.exp (-(c * |(m : ℝ)|)) := by
      have hmul : Real.exp (-(gWin z t δ m / 16)) ≤ Real.exp (-(c * |(m : ℝ)|)) := by
        rw [hc]; exact h2
      nlinarith [hmul, hinvpos]
    linarith
  -- the symmetric geometric sum
  have hsym : ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), Real.exp (-(c * |(m : ℝ)|))
      ≤ 2 * ∑ j ∈ Finset.range (K + 1), Real.exp (-(c * (j : ℝ))) :=
    sum_Icc_symm_le (fun x => Real.exp (-(c * x))) (fun x => (Real.exp_pos _).le)
  have hgeo := sum_exp_neg_le hc0 (K + 1)
  have hrw : ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (100000 * (2 + |t|)⁻¹) * Real.exp (-(c * |(m : ℝ)|))
      = (100000 * (2 + |t|)⁻¹)
          * ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), Real.exp (-(c * |(m : ℝ)|)) :=
    (Finset.mul_sum _ _ _).symm
  have hcoef : (0:ℝ) ≤ 100000 * (2 + |t|)⁻¹ := by positivity
  have hbound : ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), Real.exp (-(c * |(m : ℝ)|))
      ≤ 2 * (1 + 1 / c) := by linarith [hsym, hgeo]
  -- `(2+|t|)⁻¹ · 2(1 + 32|t|/π) ≤ 22`
  have hcinv : 1 / c = 32 * |t| / Real.pi := by
    rw [hc, one_div_div]
  have hfin : (100000 * (2 + |t|)⁻¹) * (2 * (1 + 1 / c)) ≤ 2200000 := by
    rw [hcinv]
    have h32 : 32 * |t| / Real.pi ≤ 11 * |t| := by
      rw [div_le_iff₀ hpi]
      nlinarith [Real.pi_gt_three, htpos]
    have hpos2 : (0:ℝ) < 2 + |t| := by linarith
    rw [mul_comm (100000:ℝ) ((2 + |t|)⁻¹), mul_assoc, inv_mul_eq_div, div_le_iff₀ hpos2]
    linarith [h32, htpos]
  calc ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m))
      ≤ ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (100000 * (2 + |t|)⁻¹) * Real.exp (-(c * |(m : ℝ)|)) := hstep1
    _ = (100000 * (2 + |t|)⁻¹)
          * ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), Real.exp (-(c * |(m : ℝ)|)) := hrw
    _ ≤ (100000 * (2 + |t|)⁻¹) * (2 * (1 + 1 / c)) :=
        mul_le_mul_of_nonneg_left hbound hcoef
    _ ≤ 2200000 := hfin

/-! ### The high range: the error tail, and the one remaining obligation -/

/-- `log K ≤ log(2+|t|) + log log Y` — step 3a's bound in logarithmic form, valid also at `K = 0`
(where Lean's `log 0 = 0` is below the positive right-hand side). -/
theorem log_resWindowCount_le {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi / 2) (t : ℝ) {Y : ℕ}
    (hY : 3 ≤ Y) :
    Real.log ((resWindowCount t δ Y : ℕ) : ℝ)
      ≤ Real.log (2 + |t|) + Real.log (Real.log (Y : ℝ)) := by
  have ht0 : (0:ℝ) ≤ |t| := abs_nonneg t
  have hYR : (3:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hlogY : (1:ℝ) < Real.log (Y:ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (Y:ℝ) := Real.log_le_log (by norm_num) hYR
    have : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      nlinarith [Real.exp_one_lt_d9]
    linarith
  have hprod : (0:ℝ) < (2 + |t|) * Real.log (Y:ℝ) := by positivity
  have hsplit : Real.log ((2 + |t|) * Real.log (Y:ℝ))
      = Real.log (2 + |t|) + Real.log (Real.log (Y:ℝ)) :=
    Real.log_mul (by linarith) (by linarith)
  rw [← hsplit]
  rcases Nat.eq_zero_or_pos (resWindowCount t δ Y) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    refine Real.log_nonneg ?_
    nlinarith
  · refine Real.log_le_log ?_ (resWindowCount_le hδ0 hδπ t hY)
    exact_mod_cast hpos

/-- **The high range, short-window case `2δ ≤ |t|`** — the four proved steps assembled. -/
theorem highResonantMass_le_wide {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ resEps z) {t : ℝ} (ht : 2 * δ ≤ |t|) {Y : ℕ} (hY : 2 ≤ Y) :
    highResonantMass z t Y δ
      ≤ 50 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|)) + (2200040 + 22 * δ) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hδπ : δ ≤ Real.pi / 2 := le_trans hδ (resEps_le_pi_div_two z)
  have ht0 : (0:ℝ) ≤ |t| := abs_nonneg t
  have hlt : (0:ℝ) < Real.log (2 + |t|) := Real.log_pos (by linarith)
  -- `Y = 2` has an empty high range
  rcases lt_or_ge Y 3 with hY2 | hY3
  · have hYeq : Y = 2 := by omega
    have hzero : highResonantMass z t Y δ = 0 := by
      refine highResonantMass_eq_zero ?_
      have h1 : Real.log ((Y:ℕ) : ℝ) = Real.log 2 := by rw [hYeq]; norm_num
      have h2 : 8 * Real.log 2 ≤ lowHeight t := lowHeight_ge t
      have h3 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      rw [h1]; linarith
    rw [hzero]
    have hllY : (0:ℝ) ≤ Real.log (Real.log (Y:ℝ)) + Real.log (2 + |t|) := by
      have h1 : Real.log ((Y:ℕ) : ℝ) = Real.log 2 := by rw [hYeq]; norm_num
      have h2 : Real.log (Real.log 2) ≤ 0 := by
        refine Real.log_nonpos (Real.log_nonneg (by norm_num)) ?_
        nlinarith [Real.log_two_lt_d9]
      -- `log log 2 ≥ −1/2` and `log(2+|t|) ≥ log 2 > 1/2`
      have h3 : -(1/2 : ℝ) ≤ Real.log (Real.log 2) := by
        have hexph : (1.6:ℝ) < Real.exp (1/2) := by
          have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
            rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_one_gt_d9, Real.exp_pos (1/2 : ℝ), hsq]
        have hinv : Real.exp (-(1/2:ℝ)) = 1 / Real.exp (1/2) := by
          rw [Real.exp_neg]; ring
        have h16 : 1 / Real.exp (1/2) < 1 / 1.6 :=
          one_div_lt_one_div_of_lt (by norm_num) hexph
        have hlt2 : Real.exp (-(1/2:ℝ)) < Real.log 2 := by
          rw [hinv]; nlinarith [Real.log_two_gt_d9]
        have := Real.log_le_log (Real.exp_pos (-(1/2:ℝ))) hlt2.le
        rwa [Real.log_exp] at this
      have h4 : (1/2 : ℝ) < Real.log (2 + |t|) := by
        have h5 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith)
        nlinarith [Real.log_two_gt_d9]
      rw [h1]; linarith
    nlinarith [hllY, hδ0]
  -- the genuine case
  set K : ℕ := resWindowCount t δ Y with hK
  have hpart := highResonantMass_eq_sum_windows hz hδ t Y
  rw [← hK] at hpart
  -- termwise: main + error
  have hterm : ∀ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      windowMass z t Y δ m
        ≤ 16 * δ / (|z.arg - 2 * Real.pi * m| - δ)
          + 6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m)) := by
    intro m _
    have hgap2 : 2 * resEps z ≤ |z.arg - 2 * Real.pi * m| := two_resEps_le_abs_shift z m
    have hgap : 0 < |z.arg - 2 * Real.pi * m| - δ := by linarith
    have h1 := windowMass_le hz hδ0 hδ ht Y m
    have h2 := windowMass_main_le hδ0 ht m hgap
    linarith
  have hsum : highResonantMass z t Y δ
      ≤ (∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), 16 * δ / (|z.arg - 2 * Real.pi * m| - δ))
        + ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            6 * (1 + aWin z t δ m) ^ 3 / Real.sqrt (Real.exp (aWin z t δ m)) := by
    rw [hpart, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hterm
  have hmain := main_sum_le hδ0 hδ K
  have herr := err_sum_le hδ0 hδ ht K
  have hlogK : Real.log ((K : ℕ) : ℝ)
      ≤ Real.log (2 + |t|) + Real.log (Real.log (Y : ℝ)) := by
    rw [hK]; exact log_resWindowCount_le hδ0 hδπ t hY3
  -- `(64δ/π)(1 + log K) ≤ 22δ + 50δ(log log Y + log(2+|t|))`
  have h64 : 64 / Real.pi ≤ 22 := by
    rw [div_le_iff₀ hpi]; nlinarith [Real.pi_gt_three]
  have hllY : (0:ℝ) ≤ Real.log (Real.log (Y:ℝ)) + Real.log (2 + |t|) := by
    have hYR : (3:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY3
    have h3 : Real.log 3 ≤ Real.log (Y:ℝ) := Real.log_le_log (by norm_num) hYR
    have h1 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      nlinarith [Real.exp_one_lt_d9]
    have : (0:ℝ) ≤ Real.log (Real.log (Y:ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hcoef : (64 * δ / Real.pi) * (1 + Real.log ((K : ℕ) : ℝ))
      ≤ 22 * δ + 50 * δ * (Real.log (Real.log (Y:ℝ)) + Real.log (2 + |t|)) := by
    have hpos : (0:ℝ) < 64 * δ / Real.pi := by positivity
    have hc21 : 64 * δ / Real.pi ≤ 22 * δ := by
      rw [div_le_iff₀ hpi]; nlinarith [Real.pi_gt_three, hδ0]
    have hstep : (64 * δ / Real.pi) * (1 + Real.log ((K : ℕ) : ℝ))
        ≤ (64 * δ / Real.pi) * (1 + (Real.log (2 + |t|) + Real.log (Real.log (Y:ℝ)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos.le
    nlinarith [hstep, hc21, hllY, hδ0]
  linarith [hsum, hmain, herr, hcoef]

/-- **The high range, long-window case `|t| < 2δ`** — the one step of `UniformResonantMass` still
open.  Here the windows are longer than a unit in `log p`, so Brun–Titchmarsh does not apply and
the per-window bound must come from the two-sided Mertens estimate
`Erdos67b.PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add`, which gives
`log((γ_m+δ)/(γ_m−δ)) + 2·mertensBound ≤ 2δ/(γ_m−δ) + 2·mertensBound` per window.  The main term
is then summed by the SAME `main_sum_le`; what needs care is that the per-window additive
`2·mertensBound` is paid for, which the window count `K ≤ (2+|t|) log Y ≤ (2+4δ) log Y` makes
possible only because `|t| < 2δ` bounds `K` by `O_δ(log Y)`, so the bookkeeping must group windows
rather than charge each one — the same dyadic grouping the short-window case avoids via the
exponential decay of `err_term_le`. -/
theorem highResonantMass_le_narrow {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ resEps z) {t : ℝ} (ht : |t| < 2 * δ) {Y : ℕ} (hY : 2 ≤ Y) :
    highResonantMass z t Y δ
      ≤ 50 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|)) + (2200040 + 22 * δ) := by
  sorry

/-- **The high range — the remaining obligation of `UniformResonantMass`.**

Above height `lowHeight t = 16 log(2+|t|)` the resonant primes are covered by the windows
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
      ≤ 50 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|)) + (2200040 + 22 * δ) := by
  rcases le_or_gt (2 * δ) |t| with ht | ht
  · exact highResonantMass_le_wide hz hδ0 hδ ht hY
  · exact highResonantMass_le_narrow hz hδ0 hδ ht hY

/-- **`UniformResonantMass`, modulo the high range.**  With `highResonantMass_le` in hand the
low/high split closes the statement: the low range contributes
`ε·log(2+|t|) + C(ε)` with `ε = 50δ`, the high range the rest, and `100δ = 50δ + 50δ` covers
both.  This is the shape `UniformResonantMass` asks for, with `C` depending only on `z` and `δ`. -/
theorem uniformResonantMass_of_high {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ resEps z) (t : ℝ) {Y : ℕ} (hY : 2 ≤ Y) :
    resonantMass z t Y δ
      ≤ 100 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|))
        + (Real.log 16 + Real.log (1/(50*δ)) - 1 + Erdos67b.PrimeEstimates.mertensBound
            + (2200040 + 22 * δ) + 25 * δ + 1) := by
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




