/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CR: from frequencies to the per-cell ratio

S7-CM sandwiched the two sides of `ClassFreqBound` between Birkhoff counts of fixed cells:

    cellHitCount i q ≤ L + N q ,      D q ≤ cellCount i q

with `N q = Σ_{u,c} blockCount (cellSet (u ++ c)) (q+2) x` and
`D q = Σ_u blockCount (cfCylinder u) (q+2−L) x`.  CF-normality gives `N q / q → nm` and
`D q / q → dm`, and the quasi-Bernoulli bound gives `nm ≤ B·dm`.  This module does the remaining
analysis, which is generic:

* `eventually_le_of_freq` — if `f q / q → nm`, `g q / q → dm > 0` and `nm ≤ B·dm`, then for every
  `ε > 0` eventually `f q ≤ (B+ε)·g q`.  (The `δ` that works is `ε·dm/(2(1+B+ε))`.)
* `classFreqSlack_of_limits` — hence `cellHitCount i q ≤ (B+ε)·cellCount i q + L`: the per-cell
  bound with a CONSTANT additive slack.

The slack is not a defect to be removed: with `U i = ∅` the cell is visited only finitely often and
both counts are bounded, so no slack-free inequality can hold.  A constant is harmless downstream —
the front divides by a clock that tends to infinity — which is why `ClassFreqBoundSlack` is the
shape the front should consume.
-/
import NormalNumbers.VandeheyS7CellMem

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

/-- **The generic frequency comparison.** -/
theorem eventually_le_of_freq {f g : ℕ → ℝ} {nm dm B : ℝ}
    (hf : Tendsto (fun q : ℕ => f q / q) atTop (nhds nm))
    (hg : Tendsto (fun q : ℕ => g q / q) atTop (nhds dm))
    (hdm : 0 < dm) (hB : 0 ≤ B) (hnm : nm ≤ B * dm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop, f q ≤ (B + ε) * g q := by
  set δ : ℝ := ε * dm / (2 * (1 + B + ε)) with hδdef
  have hden : (0:ℝ) < 2 * (1 + B + ε) := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hkey : nm + δ ≤ (B + ε) * (dm - δ) := by
    have hδle : (B + ε) * δ + δ ≤ ε * dm := by
      have h1 : (B + ε) * δ + δ = (1 + B + ε) * δ := by ring
      rw [h1, hδdef]
      rw [mul_div_assoc']
      rw [div_le_iff₀ hden]
      nlinarith [mul_pos hε hdm]
    nlinarith [hnm]
  -- `f` is eventually below `(nm+δ)q`, `g` eventually above `(dm−δ)q`
  have hfq : ∀ᶠ q : ℕ in atTop, f q ≤ (nm + δ) * q := by
    have h := hf.eventually (eventually_lt_nhds (show nm < nm + δ by linarith))
    filter_upwards [h, eventually_gt_atTop 0] with q hq hq0
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
    rw [div_lt_iff₀ hqR] at hq
    linarith
  have hgq : ∀ᶠ q : ℕ in atTop, (dm - δ) * q ≤ g q := by
    have h := hg.eventually (eventually_gt_nhds (show dm - δ < dm by linarith))
    filter_upwards [h, eventually_gt_atTop 0] with q hq hq0
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
    rw [lt_div_iff₀ hqR] at hq
    linarith
  filter_upwards [hfq, hgq, eventually_gt_atTop 0] with q h1 h2 hq0
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
  have hBε : 0 ≤ B + ε := by linarith
  calc f q ≤ (nm + δ) * q := h1
    _ ≤ ((B + ε) * (dm - δ)) * q := by
        exact mul_le_mul_of_nonneg_right hkey hqR.le
    _ = (B + ε) * ((dm - δ) * q) := by ring
    _ ≤ (B + ε) * g q := mul_le_mul_of_nonneg_left h2 hBε

namespace MapState

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

/-- **S7-CR.**  The per-cell bound with a constant additive slack, from the two frequencies and
the mass comparison. -/
theorem classFreqSlack_of_limits {net : StateNet Φ x η ρ M} {w : List ℕ} {N D : ℕ → ℝ}
    {nm dm B K : ℝ} (i : Fin M)
    (hnum : ∀ᶠ q in atTop, cellHitCount net w i q ≤ K + N q)
    (hden : ∀ᶠ q in atTop, D q ≤ cellCount net i q)
    (hN : Tendsto (fun q : ℕ => N q / q) atTop (nhds nm))
    (hD : Tendsto (fun q : ℕ => D q / q) atTop (nhds dm))
    (hdm : 0 < dm) (hB : 0 ≤ B) (hmass : nm ≤ B * dm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop, cellHitCount net w i q ≤ (B + ε) * cellCount net i q + K := by
  have hcmp := eventually_le_of_freq hN hD hdm hB hmass hε
  have hBε : 0 ≤ B + ε := by linarith
  filter_upwards [hnum, hden, hcmp] with q h1 h2 h3
  have h4 : (B + ε) * D q ≤ (B + ε) * cellCount net i q :=
    mul_le_mul_of_nonneg_left h2 hBε
  linarith

end MapState

section Audit

#print axioms eventually_le_of_freq
#print axioms MapState.classFreqSlack_of_limits

end Audit

end NormalNumbers.VandeheyS7
