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


/-! ## The converse: the crux at `[]` IS the clock rate

Nothing is lost in the implication above.  At the empty word the reference block average is
constantly `1` (the reference state never stalls), and the run's block average is the run's own
emission density over the window, so the crux's summand is `1 − (emissions in the window)`, which
is NONNEGATIVE — the absolute value is free — and the sliding-block identity turns its Cesàro sum
into `p − runClock Φ x p`, up to the window length.  So the crux at `[]` says exactly that the
clock rate is `1`, no more and no less.  Any block length `T` will do; `T = 1` is taken.
-/

theorem blockAvg_refState_nil {z : ℝ} {T : ℕ} (hT : 0 < T)
    (horb : ∀ k : ℕ, gaussMap^[k] z ∈ Set.Ioo (0:ℝ) 1) :
    blockAvg refState T ([] : List ℕ) z = 1 := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  rw [blockAvg_refState]
  have : ∀ j ∈ range T, blockIndic (cfCylinder ([] : List ℕ)) (gaussMap^[j] z) = 1 := by
    intro j _
    refine blockIndic_eq_one' ?_
    rw [cfCylinder_nil]
    exact horb j
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range,
    div_self hTR.ne']

/-- The Cesàro sum of the run's emission deficit is the clock's deficit, up to the window. -/
theorem sum_one_sub_blockAvg_nil_le (Φ : MapState) {x : ℝ}
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) {T : ℕ} (hT : 0 < T) (p : ℕ) :
    ∑ m ∈ range p, (1 - blockAvg (runState Φ x m) T ([] : List ℕ) (gaussMap^[m] x))
      ≤ ((p : ℝ) - ((runClock Φ x p : ℕ) : ℝ)) + (T : ℝ) := by
  have hid := abs_slotCount_sub_sum_blockAvg_le Φ x ([] : List ℕ) hT p
  rw [slotCount_nil Φ horb hy hyirr p, abs_le] at hid
  have hsum : ∑ m ∈ range p, (1 - blockAvg (runState Φ x m) T ([] : List ℕ) (gaussMap^[m] x))
      = (p : ℝ) - ∑ m ∈ range p, blockAvg (runState Φ x m) T ([] : List ℕ) (gaussMap^[m] x) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]
  rw [hsum]
  linarith [hid.1]

/-- **The converse of S7-CO.**  For one run, a clock rate of `1` gives the crux's clause at the
empty word.  With `tendsto_runClock_div` this makes `BlockForgetRun []` and "the clock runs at
rate `1`" the same statement. -/
theorem blockForgetRun_nil_clause_of_rate (Φ : MapState) {x : ℝ}
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x))
    (hrate : Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds 1))
    {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    ∀ᶠ p : ℕ in atTop,
      ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
        |blockAvg (runState Φ x m) 1 ([] : List ℕ) (gaussMap^[m] x)
          - blockAvg refState 1 ([] : List ℕ) (gaussMap^[m] x)| ≤ ε * (p : ℝ) := by
  classical
  have hdef : Tendsto (fun p : ℕ => 1 - ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub hrate
    simpa using this
  have hsmall := hdef.eventually (eventually_abs_sub_lt (0:ℝ) (show (0:ℝ) < ε / 2 by linarith))
  have hTsmall : ∀ᶠ p : ℕ in atTop, (1:ℝ) / (p : ℝ) ≤ ε / 2 := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).eventually
      (eventually_lt_nhds (show (0:ℝ) < ε / 2 by linarith))
    filter_upwards [this] with p hp using hp.le
  filter_upwards [hsmall, hTsmall, eventually_gt_atTop 0] with p hp hpT hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- each summand is the nonnegative emission deficit
  have hterm : ∀ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
      |blockAvg (runState Φ x m) 1 ([] : List ℕ) (gaussMap^[m] x)
        - blockAvg refState 1 ([] : List ℕ) (gaussMap^[m] x)|
      = 1 - blockAvg (runState Φ x m) 1 ([] : List ℕ) (gaussMap^[m] x) := by
    intro m _
    have horbm : ∀ k : ℕ, gaussMap^[k] (gaussMap^[m] x) ∈ Set.Ioo (0:ℝ) 1 := by
      intro k; rw [← Function.iterate_add_apply]; exact horb _
    rw [blockAvg_refState_nil one_pos horbm]
    have hle := blockAvg_le_one (runState Φ x m) one_pos ([] : List ℕ) (gaussMap^[m] x)
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [Finset.sum_congr rfl hterm]
  -- extend the good part to all times: every summand is nonnegative
  have hnn : ∀ m ∈ range p, (0:ℝ) ≤ 1 - blockAvg (runState Φ x m) 1 ([] : List ℕ)
      (gaussMap^[m] x) := by
    intro m _
    have := blockAvg_le_one (runState Φ x m) one_pos ([] : List ℕ) (gaussMap^[m] x)
    linarith
  have hext : ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
      (1 - blockAvg (runState Φ x m) 1 ([] : List ℕ) (gaussMap^[m] x))
      ≤ ∑ m ∈ range p, (1 - blockAvg (runState Φ x m) 1 ([] : List ℕ) (gaussMap^[m] x)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m hm _ => hnn m hm
  refine hext.trans ?_
  refine (sum_one_sub_blockAvg_nil_le Φ horb hy hyirr one_pos p).trans ?_
  have hdiff : (p : ℝ) - ((runClock Φ x p : ℕ) : ℝ) ≤ (ε / 2) * (p : ℝ) := by
    rw [abs_sub_lt_iff] at hp
    have h1 : 1 - ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ) < ε / 2 := by linarith [hp.1]
    have := mul_lt_mul_of_pos_right h1 hpR
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hpR.ne'] at this
    linarith
  have hT1 : (1:ℝ) ≤ (ε / 2) * (p : ℝ) := by
    rw [div_le_iff₀ hpR] at hpT
    linarith
  push_cast
  linarith

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
#print axioms NormalNumbers.VandeheyS7.MapState.blockForgetRun_nil_clause_of_rate
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_runClock_div
#print axioms NormalNumbers.VandeheyS7.MapState.isCFNormal_image_of_crux

end Audit
