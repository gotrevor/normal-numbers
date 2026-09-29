/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CO: the clock runs at rate `1` — the clock debt, discharged from the SAME crux

Route A carried two scalar obligations beside the crux: the width affordability `WidthAfford`, and
the clock's rate.  The rate is now free.

The observation is that the crux `BlockForgetRun` is stated for an arbitrary word `w`, and at the
EMPTY word its counting function degenerates to the clock itself:

* `cfCylinder [] = (0,1)`, so `outCount Φ x [] k = k` along a genuine output orbit, and S7-SO's
  identity `slotCount = outCount ∘ runClock` reads `slotCount Φ x [] p = runClock Φ x p`;
* `γ(cfCylinder []) = 1`, since `γ(0,1) = (log 2 − log 1)/log 2`;
* the input-side hypothesis that S7-RV needs — `blockCount (I_[]) p x / p → γ(I_[])` — is the
  triviality `p/p → 1`, needing no normality at all.

So S7-RV at `w = []` says `runClock Φ x p / p → 1`: **the clock rate is `1`**, on nothing but the
crux at the empty word and the width floor.  Feeding that back into S7-IM removes the rate
hypothesis from `isCFNormal_image_of_blockForgetRun` entirely.

What is left of route A is therefore exactly two statements: `BlockForgetRun` (for every word,
including `[]`) and `WidthAfford`.

## Guard rule

**Content locator.**  `rate ≤ 1` was always free (`runClock p ≤ p`); the content is `rate ≥ 1`,
i.e. that stalls have frequency zero — and that is what the crux at `w = []` asserts, since the
reference state never stalls (S7-RR).

**Degenerate cases.**  `p = 0`: both sides `0`.  A stalling run would have `runClock p / p → r < 1`
and would contradict the crux at `[]`, which is the honest content of the discharge.
-/
import NormalNumbers.VandeheyS7Image

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## The empty word -/

theorem gaussMeasure_cfCylinder_nil_toReal :
    (gaussMeasure (cfCylinder ([] : List ℕ))).toReal = 1 := by
  rw [cfCylinder_nil, gaussMeasure_Ioo (le_refl 0) (by norm_num) (le_refl 1)]
  rw [ENNReal.toReal_ofReal]
  · rw [show (1:ℝ) + 1 = 2 by norm_num, show (1:ℝ) + 0 = 1 by norm_num, Real.log_one]
    field_simp
    ring
  · have : Real.log 1 ≤ Real.log (1 + 1) := Real.log_le_log (by norm_num) (by norm_num)
    have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [show (1:ℝ) + 1 = 2 by norm_num, show (1:ℝ) + 0 = 1 by norm_num, Real.log_one] at *
    positivity

/-- At the empty word the input-side hypothesis is trivial. -/
theorem tendsto_blockCount_nil {x : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (fun p => blockCount (cfCylinder ([] : List ℕ)) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder ([] : List ℕ))).toReal) := by
  rw [gaussMeasure_cfCylinder_nil_toReal]
  have hcount : ∀ p : ℕ, blockCount (cfCylinder ([] : List ℕ)) p x = (p : ℝ) := by
    intro p
    rw [blockCount_apply]
    have : ∀ k ∈ range p, blockIndic (cfCylinder ([] : List ℕ)) (gaussMap^[k] x) = 1 := by
      intro k _
      refine blockIndic_eq_one' ?_
      rw [cfCylinder_nil]
      exact horb k
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with p hp
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  rw [hcount p, div_self hpR.ne']

/-- At the empty word the crux's counting function IS the clock. -/
theorem slotCount_nil (Φ : MapState) {x : ℝ}
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) (p : ℕ) :
    slotCount Φ x ([] : List ℕ) p = ((runClock Φ x p : ℕ) : ℝ) := by
  classical
  rw [slotCount_eq_outCount Φ horb hy hyirr [] p, outCount]
  have : ∀ i ∈ range (runClock Φ x p),
      (if gaussMap^[i] (Φ.mob x) ∈ cfCylinder ([] : List ℕ) then (1:ℝ) else 0) = 1 := by
    intro i _
    refine if_pos ?_
    rw [cfCylinder_nil]
    exact (irrational_orbit (Φ.mob x) hyirr hy i).2
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]

/-! ## The discharge -/

/-- **S7-CO: the clock rate is `1`.**  No new hypothesis: the crux at the empty word and the
width floor suffice. -/
theorem tendsto_runClock_div (hBF : BlockForgetRun ([] : List ℕ)) (Φ : MapState) {x : ℝ}
    (hx : IsCFNormal x) (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) (hwf : WidthAfford Φ x) :
    Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds 1) := by
  have h := tendsto_slotCountFreq_gauss hBF Φ hx horb (tendsto_blockCount_nil horb) hwf
  rw [gaussMeasure_cfCylinder_nil_toReal] at h
  refine h.congr fun p => ?_
  rw [slotCount_nil Φ horb hy hyirr p]

/-- **The image is CF-normal, on the crux alone.**  `BlockForgetRun` for every word (including the
empty one) plus `WidthAfford` give `IsCFNormal (Φ.mob x)` for every CF-normal `x`.  The clock
hypothesis of S7-IM is gone. -/
theorem isCFNormal_image_of_crux
    (hBF : ∀ w : List ℕ, BlockForgetRun w)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) (hwf : WidthAfford Φ x) :
    IsCFNormal (Φ.mob x) :=
  isCFNormal_image_of_blockForgetRun (fun w _ _ => hBF w) Φ hx horb hy hyirr hwf
    (tendsto_runClock_div (hBF []) Φ hx horb hy hyirr hwf)

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.slotCount_nil
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_runClock_div
#print axioms NormalNumbers.VandeheyS7.MapState.isCFNormal_image_of_crux

end Audit
