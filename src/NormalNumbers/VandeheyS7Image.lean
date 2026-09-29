/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-IM: from the crux to CF-normality of the IMAGE

S7-RV pinned the crux's frequency: `slotCount Φ x w p / p → γ(I_w)`, on `BlockForgetRun` plus an
affordable width floor.  S7-SO already identified that counting function with the output's own
block count read along the run clock: `slotCount Φ x w p = outCount Φ x w (runClock Φ x p)`.  So
the rescaling lemma `Rescale.tendsto_div_of_tendsto_comp_of_monotone` — the same one
`affineUniformFreq_of_runClock` uses — converts the input-time frequency into the output-time
frequency, and the answer is `γ(I_w)/rate`:

    blockCount (I_w) k (Φ.mob x) / k  →  γ(I_w) / rate .

At `rate = 1` that is exactly `IsCFNormal (Φ.mob x)`, via `isCFNormal_of_irrational_orbit_freq`.

This closes the last structural gap in route A: the chain from the crux to CF-normality of the
image now has no `SampledUniformCount` detour and no anonymous constants.  What remains is
arithmetic, not architecture:

* `BlockForgetRun w` for every genuine `w` — the live crux (S7-BR);
* `WidthAfford Φ x` — the width debt;
* `rate = 1` — the clock debt.  `rate ≤ 1` is free (`runClock p ≤ p`, at most one digit emitted
  per input digit); `rate ≥ 1` follows from `∑_a γ(I_{[a]}) = 1` given the theorem below, since
  the digit frequencies of the image sum to at most `1`.  `tendsto_blockCount_image` is stated so
  that argument can be run against it.

## Guard rule

**Content locator.**  Nothing new is proved about the transducer; S7-SO's identity and S7-RV's
limit are composed by a monotone rescaling.  With `rate = 1` and `Φ = refState` the statement is
the tautology that a CF-normal `x` has the block frequencies of a CF-normal number.

**Degenerate cases.**  `w = []` is excluded by `IsCFNormal`'s own quantifier.  `rate = 0` is
excluded: the rescaling lemma needs `0 < rate`, and at rate `0` the image has finitely many
digits and is rational.
-/
import NormalNumbers.VandeheyS7RefValue
import NormalNumbers.VandeheyS7SlotOut
import NormalNumbers.VandeheyRescale
import NormalNumbers.CFOrbitFreq

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## The output count is the image's block count -/

theorem outCount_eq_blockCount (Φ : MapState) (x : ℝ) (w : List ℕ) (k : ℕ) :
    outCount Φ x w k = blockCount (cfCylinder w) k (Φ.mob x) := by
  classical
  rw [outCount, blockCount_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : gaussMap^[i] (Φ.mob x) ∈ cfCylinder w
  · rw [if_pos hm, blockIndic_eq_one' hm]
  · rw [if_neg hm, blockIndic_eq_zero' hm]

theorem outCount_mono (Φ : MapState) (x : ℝ) (w : List ℕ) : Monotone (outCount Φ x w) := by
  classical
  intro k l hkl
  rw [outCount, outCount]
  refine Finset.sum_le_sum_of_subset_of_nonneg (by exact fun i hi => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hkl)) fun i _ _ => ?_
  by_cases hm : gaussMap^[i] (Φ.mob x) ∈ cfCylinder w
  · rw [if_pos hm]; norm_num
  · rw [if_neg hm]

/-! ## The image's digit-block frequency -/

/-- **S7-IM.**  The crux plus the clock rate give the image's block frequency, with its value. -/
theorem tendsto_blockCount_image {w : List ℕ} (hne : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    (hBF : BlockForgetRun w) (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) (hwf : WidthAfford Φ x) {rate : ℝ} (hrate0 : 0 < rate)
    (hrate : Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds rate)) :
    Tendsto (fun k => blockCount (cfCylinder w) k (Φ.mob x) / (k : ℝ)) atTop
      (nhds ((gaussMeasure (cfCylinder w)).toReal / rate)) := by
  have hslot := tendsto_slotCountFreq_gauss hne hpos hBF Φ hx horb hwf
  have hcomp : Tendsto (fun p => outCount Φ x w (runClock Φ x p) / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal) := by
    refine hslot.congr fun p => ?_
    rw [slotCount_eq_outCount Φ horb hy hyirr w p]
  have hmain := Rescale.tendsto_div_of_tendsto_comp_of_monotone
    (C := outCount Φ x w) (ℓ := runClock Φ x) (outCount_mono Φ x w)
    (fun _ _ h => runClock_mono Φ x h) hrate0 hrate hcomp
  refine hmain.congr fun k => ?_
  rw [outCount_eq_blockCount]

/-- **The image is CF-normal**, once the clock runs at rate `1`.  This is the frozen target's
content for the map `Φ`, with the crux as its only remaining analytic input. -/
theorem isCFNormal_image_of_blockForgetRun
    (hBF : ∀ w : List ℕ, w ≠ [] → (∀ a ∈ w, 1 ≤ a) → BlockForgetRun w)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) (hwf : WidthAfford Φ x)
    (hrate : Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds 1)) :
    IsCFNormal (Φ.mob x) := by
  refine isCFNormal_of_irrational_orbit_freq _ hyirr hy fun v hne hpos => ?_
  have h := tendsto_blockCount_image hne hpos (hBF v hne hpos) Φ hx horb hy hyirr hwf
    (rate := 1) one_pos hrate
  simpa using h

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.outCount_eq_blockCount
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_blockCount_image
#print axioms NormalNumbers.VandeheyS7.MapState.isCFNormal_image_of_blockForgetRun

end Audit
