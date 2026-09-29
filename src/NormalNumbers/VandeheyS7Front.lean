/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-FT: the §7 front, assembled — three named hypotheses and nothing else

S7-CL reduced `BlockAverageBound` to `ClassFreqBound + WidthFreqBound`, but in the wrong
quantifier order: `WidthFreqBound` fixes `η` and then quantifies `ε`, whereas S7-SK produces
`η` only *after* `ε` (the width floor one can afford depends on how much slack one may spend).
That is not a defect of S7-SK — it is the right order, because the NET is also chosen after `ε`.
This module restates the reduction accordingly and assembles the front.

    `blockAverageBound_of_front` :
        ClassFreqBound (uniformly over nets)  +  WidthFreqOrder  ⟹  BlockAverageBound B

and, feeding S7-SK in,

    `blockAverageBound_of_scalar` :
        ClassFreqBound (uniformly over nets)  +  MeanSlack  +  ClockLinear  ⟹  BlockAverageBound B

So the whole §7 chain, from `vandeheyS7_mul_phi` down, now rests on exactly three statements:

1. **`ClassFreqBound`** — per-cell relative frequency, normalized by `cellCount i`.  The mechanism
   that can prove it is S7-MY (finite memory ⟹ the joint event is a single word, constant
   `8 log 2`); the obstruction is that the cell is not a finite-memory function of the input, so
   the needed form is distributional.
2. **`MeanSlack`** — `Σ_{m<q} log d_{m+2} = O(q)`: positive recurrence of one scalar walk.
3. **`ClockLinear`** — `runClock (q+2) ≥ c·q`: Vandehey's Lemma 6.1.

Two of the three are scalar statements about the emission schedule.  Only the first is about the
state space at all.
-/
import NormalNumbers.VandeheyS7Slack
import NormalNumbers.VandeheyS7Net

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ}

/-- The width-frequency hypothesis in the order the decomposition needs: `ε` first, then a width
floor `η` that can be afforded. -/
def WidthFreqOrder (Φ : MapState) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ q in atTop,
    widthBadCount Φ x η q ≤ ε * ((runClock Φ x (q + 2) : ℕ) : ℝ)

/-- S7-SK supplies `WidthFreqOrder` from two scalar facts. -/
theorem widthFreqOrder_of_scalar (Φ : MapState) (x : ℝ) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q)
    (hclock : ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ)) :
    WidthFreqOrder Φ x :=
  fun _ hε => exists_eventually_widthBad_le Φ x hA hc hmean hclock hε

/-- **S7-FT, the reduction in the right quantifier order.** -/
theorem blockAverageBound_of_front (Φ : MapState) (x : ℝ) (w : List ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hclock : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop)
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBound net w B)
    (hW : WidthFreqOrder Φ x) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j) := by
  classical
  rw [blockAverageBound_iff_slot]
  intro ε hε
  set ε' := ε / 3 with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨η, hη, hwide⟩ := hW ε' hε'pos
  obtain ⟨M, ⟨net⟩⟩ := exists_stateNet Φ x hη (show (0:ℝ) < 1 by norm_num)
  have hcells : ∀ᶠ q in atTop, ∀ i : Fin M,
      cellHitCount net w i q ≤ (B + ε') * cellCount net i q :=
    Filter.eventually_all.mpr
      (fun i => hCF hη (show (0:ℝ) < 1 by norm_num) net ε' hε'pos i)
  have hbig : ∀ᶠ q in atTop, (2:ℝ) ≤ ε' * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    have h := hclock.eventually_ge_atTop (2 / ε')
    filter_upwards [h] with q hq
    rw [div_le_iff₀ hε'pos] at hq
    linarith
  have hmain : ∀ᶠ q in atTop,
      slotCount Φ x w (q + 2) ≤ (B + ε) * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    filter_upwards [hcells, hwide, hbig] with q hc hw2 hb2
    have hsplit := slotCount_le_split net w q
    have hsum : ∑ i : Fin M, cellHitCount net w i q
        ≤ (B + ε') * ∑ i : Fin M, cellCount net i q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hc i
    have hcc : ∑ i : Fin M, cellCount net i q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
      sum_cellCount_le_runClock net q
    have hBε : 0 ≤ B + ε' := by linarith
    have h3 : (B + ε') * ∑ i : Fin M, cellCount net i q
        ≤ (B + ε') * ((runClock Φ x (q + 2) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hcc hBε
    have hthree : ε = 3 * ε' := by rw [hε']; ring
    nlinarith [hsplit, hsum, h3, hw2, hb2]
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp hmain
  refine eventually_atTop.mpr ⟨q₀ + 2, fun p hp => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
  exact hq₀ j (by omega)

/-- **The front, in scalar form.**  Three hypotheses; two of them about the emission schedule
alone. -/
theorem blockAverageBound_of_scalar (Φ : MapState) (x : ℝ) (w : List ℕ) {B A c : ℝ} (hB : 0 ≤ B)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hclock : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop)
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBound net w B)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q)
    (hclin : ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ)) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j) :=
  blockAverageBound_of_front Φ x w hB hclock (fun hη hρ _ net => hCF hη hρ net)
    (widthFreqOrder_of_scalar Φ x hA hc hmean hclin)

end MapState

section Audit

#print axioms MapState.widthFreqOrder_of_scalar
#print axioms MapState.blockAverageBound_of_front
#print axioms MapState.blockAverageBound_of_scalar

end Audit

end NormalNumbers.VandeheyS7
