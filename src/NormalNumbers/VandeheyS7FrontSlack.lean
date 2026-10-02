/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-FS: the front, in the shape the memory route can actually deliver

S7-CR showed the per-cell bound the memory mechanism produces carries a CONSTANT additive slack,
and that the slack is forced (a cell visited finitely often has both counts bounded).  This module
re-proves the front against that shape:

    `ClassFreqBoundSlack net w B` :  ∀ ε > 0, ∀ i, ∃ K ≥ 0, ∀ᶠ q, cellHit i q ≤ (B+ε)·cellCount i q + K

    `blockAverageBound_of_frontSlack` :
        ClassFreqBoundSlack (uniformly over nets)  +  WidthFreqOrder  ⟹  BlockAverageBound B

The slack costs nothing: the `M` constants sum to one constant, and the clock tends to infinity, so
the same `hbig` step that already absorbed the two initial times absorbs `2 + Σ_i K i` as well.
`ClassFreqBound` implies `ClassFreqBoundSlack` (`classFreqBoundSlack_of_classFreqBound`), so this
is a strictly weaker hypothesis and the old front is a special case.
-/
import NormalNumbers.VandeheyS7Front
import NormalNumbers.VandeheyS7Compose
import NormalNumbers.VandeheyS7CellRatio

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

/-- The per-cell frequency bound with a constant additive slack. -/
def ClassFreqBoundSlack (net : StateNet Φ x η ρ M) (w : List ℕ) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ i : Fin M, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ q in atTop,
    cellHitCount net w i q ≤ (B + ε) * cellCount net i q + K

theorem classFreqBoundSlack_of_classFreqBound {net : StateNet Φ x η ρ M} {w : List ℕ} {B : ℝ}
    (h : ClassFreqBound net w B) : ClassFreqBoundSlack net w B := by
  intro ε hε i
  refine ⟨0, le_refl 0, ?_⟩
  filter_upwards [h ε hε i] with q hq
  linarith

/-- **S7-FS.**  The front against the slack form. -/
theorem blockAverageBound_of_frontSlack (Φ : MapState) (x : ℝ) (w : List ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hclock : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop)
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBoundSlack net w B)
    (hW : WidthFreqOrder Φ x) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j) := by
  classical
  rw [blockAverageBound_iff_slot]
  intro ε hε
  set ε' := ε / 3 with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨η, hη, hwide⟩ := hW ε' hε'pos
  obtain ⟨M, ⟨net⟩⟩ := exists_stateNet Φ x hη (show (0:ℝ) < 1 by norm_num)
  have hslack := hCF hη (show (0:ℝ) < 1 by norm_num) net ε' hε'pos
  choose Kf hKf hKev using hslack
  set Ksum : ℝ := ∑ i : Fin M, Kf i with hKsum
  have hKsum_nonneg : 0 ≤ Ksum := Finset.sum_nonneg fun i _ => hKf i
  have hcells : ∀ᶠ q in atTop, ∀ i : Fin M,
      cellHitCount net w i q ≤ (B + ε') * cellCount net i q + Kf i :=
    Filter.eventually_all.mpr (fun i => hKev i)
  have hbig : ∀ᶠ q in atTop, (2:ℝ) + Ksum ≤ ε' * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    have h := hclock.eventually_ge_atTop ((2 + Ksum) / ε')
    filter_upwards [h] with q hq
    rw [div_le_iff₀ hε'pos] at hq
    linarith
  have hmain : ∀ᶠ q in atTop,
      slotCount Φ x w (q + 2) ≤ (B + ε) * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    filter_upwards [hcells, hwide, hbig] with q hc hw2 hb2
    have hsplit := slotCount_le_split net w q
    have hsum : ∑ i : Fin M, cellHitCount net w i q
        ≤ (B + ε') * ∑ i : Fin M, cellCount net i q + Ksum := by
      have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hc i)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
      exact h
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

/-- **The front, scalar + slack**: `MeanSlack` and the slack form of the per-cell bound, nothing
else. -/
theorem blockAverageBound_of_meanSlack_slack (Φ : MapState) (x : ℝ) (w : List ℕ) {B A : ℝ}
    (hB : 0 ≤ B) (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) (hA : 0 ≤ A)
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBoundSlack net w B)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j) := by
  obtain ⟨c, hc, hclin⟩ := clockLinear_of_meanSlack Φ x hx hA hmean
  have hclock : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' _ hclin ?_
    exact Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  exact blockAverageBound_of_frontSlack Φ x w hB hclock hCF
    (widthFreqOrder_of_scalar Φ x hA hc hmean hclin)

end MapState

section Audit

#print axioms MapState.classFreqBoundSlack_of_classFreqBound
#print axioms MapState.blockAverageBound_of_frontSlack
#print axioms MapState.blockAverageBound_of_meanSlack_slack

end Audit

end NormalNumbers.VandeheyS7
