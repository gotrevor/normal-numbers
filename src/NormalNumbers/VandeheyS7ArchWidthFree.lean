/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-AW: route A's architecture WITHOUT the width debt

S7-WQ showed that route A's two remaining inputs are incompatible in shape: on a run whose wide
times are sparse the crux `BlockForgetRun` is vacuous and `WidthAfford` is FALSE, and the lap-91
probe reads the golden run as exactly such a run (`log (1/width)` is a `√n` random walk, while the
clock deficit stops at `7` stalls in `18000` reads).  The width filter is therefore not a
simplification but a liability: it is the only reason the architecture needs a second hypothesis.

This module removes it.  `BlockForgetAll` is the crux with the sum over ALL times — the same
comparison, without the `width ≥ η` restriction:

    ∀ ε > 0, ∃ T > 0, ∀ Φ x (CF-normal), ∀ᶠ p,
      Σ_{m<p} |blockAvg (runState Φ x m) T w (Gᵐx) − blockAvg refState T w (Gᵐx)| ≤ ε·p .

It implies `BlockForgetRun` (`blockForgetRun_of_all`), and it carries the whole chain on its own:

* `abs_slotCountFreq_sub_gauss_le_all` — the crux's frequency is within `3ε` of `γ(I_w)`;
* `tendsto_slotCountFreq_gauss_all` — hence converges to `γ(I_w)` exactly;
* `tendsto_runClock_div_all` — the clock runs at rate `1` (the `w = []` instance, S7-CO);
* `isCFNormal_image_of_blockForgetAll` — **the image is CF-normal**, for every CF-normal input and
  every map, on `BlockForgetAll` alone.

So route A's front is ONE statement with no side conditions: no `RefCesaro` (S7-RV), no clock
hypothesis (S7-CO), and now no width affordability.  The three refuted or refutable scalars
(`WidthAfford`, `MeanSlack`, `ClockLinear`'s uniform floor) leave the critical path entirely.

## What it costs

`BlockForgetAll` is strictly stronger than `BlockForgetRun`, and the √2 witnesses of S7-BX/S7-BY do
NOT refute it: they are single `(state, point)` pairs, whereas this is still a Cesàro average along
a genuine run.  What it gives up is the licence to ignore the narrow times — which the probe says
are almost all of them, so that licence was worth nothing.

## Guard rule

**Content locator.**  Every step is S7-RV's with the width split deleted: step 1 is the
sliding-block identity, step 2 is now the hypothesis verbatim, step 3 is the reference value.

**Degenerate cases.**  `w = []` is the clock instance and is used as such.  `T` is produced by the
hypothesis and only enters through `T/p → 0`.
-/
import NormalNumbers.VandeheyS7ClockOne
import NormalNumbers.VandeheyS7WidthDensity

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- **The width-free crux.**  The block time-average forgets the run's state, in Cesàro average
over ALL input times. -/
def BlockForgetAll (w : List ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 0 < T ∧
    ∀ (Φ : MapState) (x : ℝ), IsCFNormal x → (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      ∀ᶠ p : ℕ in atTop,
        ∑ m ∈ range p,
          |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
            - blockAvg refState T w (gaussMap^[m] x)| ≤ ε * (p : ℝ)

/-- The width-free crux implies the width-filtered one. -/
theorem blockForgetRun_of_all {w : List ℕ} (h : BlockForgetAll w) : BlockForgetRun w := by
  classical
  intro ε hε η _
  obtain ⟨T, hT, hfor⟩ := h ε hε
  refine ⟨T, hT, fun Φ x hx horb => ?_⟩
  filter_upwards [hfor Φ x hx horb] with p hp
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun m _ _ => abs_nonneg _) hp

/-! ## The architecture, with no width hypothesis -/

/-- **The architecture theorem, width-free.**  `BlockForgetAll` alone puts the crux's frequency
within `3ε` of the Gauss mass of the cylinder. -/
theorem abs_slotCountFreq_sub_gauss_le_all {w : List ℕ}
    (hBF : BlockForgetAll w) {ε : ℝ} (hε : 0 < ε)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hbc : Tendsto (fun p => blockCount (cfCylinder w) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal)) :
    ∀ᶠ p : ℕ in atTop,
      |slotCount Φ x w p / (p : ℝ) - (gaussMeasure (cfCylinder w)).toReal| ≤ 3 * ε := by
  classical
  obtain ⟨T, hT, hfor⟩ := hBF ε hε
  set γw := (gaussMeasure (cfCylinder w)).toReal with hγ
  have hrun := hfor Φ x hx horb
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have hA : ∀ᶠ p : ℕ in atTop, (T : ℝ) / (p : ℝ) ≤ ε := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually (eventually_lt_nhds hε)
    filter_upwards [this] with p hp using hp.le
  have hB := (tendsto_cesaro_blockAvg_refState hT hbc).eventually
    (eventually_abs_sub_lt γw hε)
  filter_upwards [hA, hB, hrun, eventually_gt_atTop 0] with p hA' hB' hrun' hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have h1 : |slotCount Φ x w p / (p : ℝ)
      - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)| ≤ ε := by
    have hid := abs_slotCount_sub_sum_blockAvg_le Φ x w hT p
    have hTp : (T:ℝ) ≤ ε * (p:ℝ) := by rw [div_le_iff₀ hpR] at hA'; exact hA'
    rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR]
    linarith
  have h2 : |(∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
      - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)| ≤ ε := by
    rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR, ← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (by linarith [hrun'])
  have h3 : |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - γw| ≤ ε := hB'.le
  calc |slotCount Φ x w p / (p : ℝ) - γw|
      ≤ |slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)|
        + |(∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)|
        + |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - γw| := by
        have t1 := abs_add_le (slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ))
          ((∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ))
        have t2 := abs_add_le ((slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)))
          ((∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - γw)
        simp only [sub_add_sub_cancel] at t1 t2
        linarith
    _ ≤ ε + ε + ε := by linarith
    _ = 3 * ε := by ring

/-- **The crux's frequency, exactly, with no width hypothesis.** -/
theorem tendsto_slotCountFreq_gauss_all {w : List ℕ}
    (hBF : BlockForgetAll w) (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hbc : Tendsto (fun p => blockCount (cfCylinder w) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal)) :
    Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have h := abs_slotCountFreq_sub_gauss_le_all hBF (show (0:ℝ) < δ / 6 by linarith)
    Φ hx horb hbc
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun p hp => ?_⟩
  have := hN p hp
  rw [Real.dist_eq]
  linarith

/-- **The clock rate is `1`, with no width hypothesis.**  The `w = []` instance (S7-CO). -/
theorem tendsto_runClock_div_all (hBF : BlockForgetAll ([] : List ℕ)) (Φ : MapState) {x : ℝ}
    (hx : IsCFNormal x) (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) :
    Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds 1) := by
  have h := tendsto_slotCountFreq_gauss_all hBF Φ hx horb (tendsto_blockCount_nil horb)
  rw [gaussMeasure_cfCylinder_nil_toReal] at h
  refine h.congr fun p => ?_
  rw [slotCount_nil Φ horb hy hyirr p]

/-- **The image's digit-block frequency, width-free.** -/
theorem tendsto_blockCount_image_all {w : List ℕ} (hne : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    (hBF : BlockForgetAll w) (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) {rate : ℝ} (hrate0 : 0 < rate)
    (hrate : Tendsto (fun p => ((runClock Φ x p : ℕ) : ℝ) / (p : ℝ)) atTop (nhds rate)) :
    Tendsto (fun k => blockCount (cfCylinder w) k (Φ.mob x) / (k : ℝ)) atTop
      (nhds ((gaussMeasure (cfCylinder w)).toReal / rate)) := by
  have hslot := tendsto_slotCountFreq_gauss_all hBF Φ hx horb
    (blockCount_tendsto_of_isCFNormal hx horb w hne hpos)
  have hcomp : Tendsto (fun p => outCount Φ x w (runClock Φ x p) / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal) := by
    refine hslot.congr fun p => ?_
    rw [slotCount_eq_outCount Φ horb hy hyirr w p]
  have hmain := Rescale.tendsto_div_of_tendsto_comp_of_monotone
    (C := outCount Φ x w) (ℓ := runClock Φ x) (outCount_mono Φ x w)
    (fun _ _ h => runClock_mono Φ x h) hrate0 hrate hcomp
  refine hmain.congr fun k => ?_
  rw [outCount_eq_blockCount]

/-- **S7-AW, the headline.**  `BlockForgetAll` for every word — and nothing else — makes the image
of every CF-normal input CF-normal.  Route A's front is a single statement. -/
theorem isCFNormal_image_of_blockForgetAll
    (hBF : ∀ w : List ℕ, BlockForgetAll w)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1)
    (hyirr : Irrational (Φ.mob x)) :
    IsCFNormal (Φ.mob x) := by
  have hrate := tendsto_runClock_div_all (hBF []) Φ hx horb hy hyirr
  refine isCFNormal_of_irrational_orbit_freq _ hyirr hy fun v hne hpos => ?_
  have h := tendsto_blockCount_image_all hne hpos (hBF v) Φ hx horb hy hyirr
    (rate := 1) one_pos hrate
  simpa using h

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.blockForgetRun_of_all
#print axioms NormalNumbers.VandeheyS7.MapState.abs_slotCountFreq_sub_gauss_le_all
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_slotCountFreq_gauss_all
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_runClock_div_all
#print axioms NormalNumbers.VandeheyS7.MapState.isCFNormal_image_of_blockForgetAll

end Audit
