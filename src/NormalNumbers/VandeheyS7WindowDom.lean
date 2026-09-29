/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WD: window domination closes the crux

Laps 81–84 leave the §7 front in this shape.  The crux's counting function is a Birkhoff sum of a
fixed observable of the autonomous map `pairStep` (S7-SK); the state at the tested time is exactly
`F^L(s_{n−L}, the L digits read in between)` (S7-WC); and the frequency of any finite-window event
is computed exactly by CF-normality of the input (S7-WN).  This module joins them:

**If the slot observable is dominated, after a fixed delay `L`, by a finite-window event of Gauss
mass `m`, then the crux's frequency is at most `m`.**

    (∀ n, slotObs w (runPair Φ x (n+L)) ≤ 1_{⋃_{v∈S} I_v} (Gⁿx))
      →  ∀ ε > 0, ∀ᶠ p, slotCount Φ x w p / p ≤ Σ_{v∈S} γ(I_v) + ε
                                                            (`slotCount_le_of_windowDominated`)

Nothing else is needed: no modulus, no equidistribution hypothesis, no class-frequency bound.
All the analysis is in S7-WN, and all the remaining mathematics is in *producing* `S` — i.e. in
covering the state-dependent target `s_n⁻¹(I_w)` by a window event of mass `≍ γ(I_w)`.

## What must still be produced, exactly

`S` is a set of input words of some length `K = L + M`.  The `L`-prefix determines the state up to
the far past (S7-WC); the `M`-suffix must decide whether `Gⁿx ∈ s_n⁻¹(I_w)`.  By S7-PB the target
has mass `γ(s⁻¹ I_w) ≤ (2K₀/η)·γ(I_w)` for every state of width `≥ η`, so a window set of the
right mass *exists for each frozen far-past state*; what is open is uniformity in that state, and
that is the Birkhoff–Hopf / compact-box question (directive fact (δ)).  Fact (α) does not obstruct
this: its counterexample families are not orbits of any autonomous map, so they admit no window
domination at all.

## Guard rule

Content locator: the delay `L` costs exactly `L` in the numerator (the first `L` slots are bounded
by `1` each), which dies under `/p`; if the domination were required at `n` rather than `n+L` the
far past would have nowhere to go and the statement would be unusable.  Degenerate case: `S = ∅`
forces `slotObs = 0` from time `L` on, and the conclusion is frequency `0`.
-/
import NormalNumbers.VandeheyS7WindowFreq
import NormalNumbers.VandeheyS7Skew
import NormalNumbers.GaussKB

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

lemma slotObs_nonneg (w : List ℕ) (p : MapState × ℝ) : 0 ≤ slotObs w p := by
  refine mul_nonneg ?_ (blockIndic_nonneg _ _)
  exact Nat.cast_nonneg _

lemma slotObs_le_one (w : List ℕ) (Φ : MapState) (x : ℝ) (n : ℕ) :
    slotObs w (runPair Φ x n) ≤ 1 := by
  have he : emitObs (runPair Φ x n) ≤ 1 := by
    rw [emitObs, ← runWord_eq_pairWord]
    exact_mod_cast runWord_length_le_one Φ x n
  have he0 : 0 ≤ emitObs (runPair Φ x n) := Nat.cast_nonneg _
  have hb := blockIndic_le_one (mapBlockSet (runPair Φ x n).1 w 0) (runPair Φ x n).2
  have hb0 := blockIndic_nonneg (mapBlockSet (runPair Φ x n).1 w 0) (runPair Φ x n).2
  calc slotObs w (runPair Φ x n) ≤ emitObs (runPair Φ x n) * 1 := by
        rw [slotObs]; exact mul_le_mul_of_nonneg_left hb he0
    _ ≤ 1 := by rw [mul_one]; exact he

/-- The delayed slot sum is dominated by the window count, up to the delay. -/
theorem slotCount_le_blockCount_add {Φ : MapState} {x : ℝ} {w : List ℕ} {L : ℕ}
    {A : Set ℝ} (hdom : ∀ n, slotObs w (runPair Φ x (n + L)) ≤ blockIndic A (gaussMap^[n] x))
    (p : ℕ) :
    slotCount Φ x w p ≤ blockCount A p x + L := by
  classical
  rw [slotCount_eq_sum_slotObs]
  have hBnn : 0 ≤ blockCount A p x := by
    show (0:ℝ) ≤ ∑ i ∈ range p, blockIndic A (gaussMap^[i] x)
    exact Finset.sum_nonneg fun i _ => blockIndic_nonneg _ _
  rcases Nat.lt_or_ge p L with hp | hp
  · have : ∑ n ∈ range p, slotObs w (runPair Φ x n) ≤ (p : ℝ) := by
      calc ∑ n ∈ range p, slotObs w (runPair Φ x n) ≤ ∑ _n ∈ range p, (1:ℝ) :=
            Finset.sum_le_sum fun n _ => slotObs_le_one w Φ x n
        _ = (p : ℝ) := by simp
    have hpL : (p : ℝ) ≤ (L : ℝ) := by exact_mod_cast hp.le
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, p = L + k := ⟨p - L, by omega⟩
    rw [Finset.sum_range_add]
    have h1 : ∑ n ∈ range L, slotObs w (runPair Φ x n) ≤ (L : ℝ) := by
      calc ∑ n ∈ range L, slotObs w (runPair Φ x n) ≤ ∑ _n ∈ range L, (1:ℝ) :=
            Finset.sum_le_sum fun n _ => slotObs_le_one w Φ x n
        _ = (L : ℝ) := by simp
    have h2 : ∑ m ∈ range k, slotObs w (runPair Φ x (L + m))
        ≤ ∑ m ∈ range k, blockIndic A (gaussMap^[m] x) := by
      refine Finset.sum_le_sum fun m _ => ?_
      have := hdom m
      rwa [Nat.add_comm m L] at this
    have h3 : ∑ m ∈ range k, blockIndic A (gaussMap^[m] x) ≤ blockCount A (L + k) x := by
      show _ ≤ ∑ i ∈ range (L + k), blockIndic A (gaussMap^[i] x)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.le_add_left k L))) fun i _ _ => blockIndic_nonneg _ _
    linarith

/-- **S7-WD.**  Window domination closes the crux: if the slot observable is dominated, after a
fixed delay, by a finite-window event, the crux's frequency is at most that event's Gauss mass. -/
theorem slotCount_le_of_windowDominated {Φ : MapState} {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1) {w : List ℕ} {L K : ℕ} (hK : 0 < K)
    {S : Finset (List ℕ)} (hlen : ∀ v ∈ S, v.length = K) (hpos : ∀ v ∈ S, ∀ a ∈ v, 1 ≤ a)
    (hdom : ∀ n, slotObs w (runPair Φ x (n + L))
      ≤ blockIndic (⋃ v ∈ S, cfCylinder v) (gaussMap^[n] x))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      slotCount Φ x w p / (p : ℝ) ≤ (∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal) + ε := by
  set m := ∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal with hm
  have hfreq := tendsto_windowFreq hx horb hK hlen hpos
  have hdel : Tendsto (fun p : ℕ => (L : ℝ) / (p : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum : Tendsto
      (fun p : ℕ => blockCount (⋃ v ∈ S, cfCylinder v) p x / (p : ℝ) + (L : ℝ) / (p : ℝ))
      atTop (nhds m) := by simpa using hfreq.add hdel
  have hev := hsum.eventually (eventually_lt_nhds (show m < m + ε by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hle := slotCount_le_blockCount_add hdom (A := ⋃ v ∈ S, cfCylinder v) p
  rw [div_le_iff₀ hpR]
  have hkey : blockCount (⋃ v ∈ S, cfCylinder v) p x + (L : ℝ) ≤ (m + ε) * (p : ℝ) := by
    have h' : (blockCount (⋃ v ∈ S, cfCylinder v) p x + (L : ℝ)) / (p : ℝ) ≤ m + ε := by
      rw [add_div]; exact hp.le
    rwa [div_le_iff₀ hpR] at h'
  linarith [hkey]

end MapState

section Audit

#print axioms MapState.slotCount_le_blockCount_add
#print axioms MapState.slotCount_le_of_windowDominated

end Audit

end NormalNumbers.VandeheyS7
