/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CA: the per-cell bound with an EXPLICIT constant — `CellMemory` is the only input left

S7-CT proved `ClassFreqBoundSlack` from `CellMemory` plus a cell cover; S7-CV proved the cover
exists.  Composing them, with a uniform bound `P` on the centres' pullback constants:

    `classFreqSlack_of_cellMemory'` :
        CellMemory data  ⟹  ClassFreqBoundSlack net w ((1 + 8 log 2)·((2/log 2)·P·(|I_w| + 2κ) + δ))

and, choosing `δ` freely, the constant can be taken as close as one likes to
`(2(1 + 8 log 2)/log 2)·P·(|I_w| + 2κ)`.  With `P ≤ K/η` (S7-PM, S7-Box) this is the `Cp·γ/η`
shape S7-MD prices, so the §7 chain rests on exactly `MeanSlack` and `CellMemory`.
-/
import NormalNumbers.VandeheyS7CellLim
import NormalNumbers.VandeheyS7CellCov

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

open Classical in
/-- A cell that no wide time is assigned to has both counts zero. -/
lemma cellCounts_eq_zero_of_unused {net : StateNet Φ x η ρ M} {w : List ℕ} {i : Fin M}
    (hun : ∀ m : ℕ, ¬ (net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width)) (q : ℕ) :
    cellCount net i q = 0 ∧ cellHitCount net w i q = 0 := by
  classical
  constructor
  · unfold cellCount
    exact Finset.sum_eq_zero fun m _ => if_neg (hun m)
  · unfold cellHitCount
    exact Finset.sum_eq_zero fun m _ => if_neg (hun m)

open Classical in
/-- **S7-CA.**  The per-cell bound with an explicit constant, from `CellMemory` alone. -/
theorem classFreqSlack_of_cellMemory' {net : StateNet Φ x η ρ M} {L : ℕ}
    {U : Fin M → Finset (List ℕ)} {P δ : ℝ} (w : List ℕ) (hw : w ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a)
    (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1) (hCFn : IsCFNormal x) (hL : 2 ≤ L)
    (hκ : 0 ≤ 4 * ρ / Real.sqrt (|Φ.det| / 6)) (hδ : 0 < δ)
    (hUlen : ∀ i : Fin M, ∀ u ∈ U i, u.length = L ∧ (∀ a ∈ u, 1 ≤ a))
    (hUsel : ∀ i : Fin M, ∀ m : ℕ, L ≤ m + 2 →
      selIndic net i m
        = if ∃ u ∈ U i, gaussMap^[m + 2 - L] x ∈ cfCylinder u then 1 else 0)
    (hUne : ∀ i : Fin M, (U i).Nonempty)
    (hP : ∀ i : Fin M, (∃ m : ℕ, net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width) →
      (net.cen i).pullLip ≤ P) :
    ClassFreqBoundSlack net w
      ((1 + 8 * Real.log 2) *
        ((1 / Real.log 2) *
          (2 * (P * ((volume (cfCylinder w)).toReal
            + 2 * (4 * ρ / Real.sqrt (|Φ.det| / 6))))) + δ)) := by
  classical
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set κ : ℝ := 4 * ρ / Real.sqrt (|Φ.det| / 6) with hκdef
  set V : ℝ := (volume (cfCylinder w)).toReal with hV
  have hVnn : 0 ≤ V := by rw [hV]; positivity
  -- one cover per centre
  have hcovex : ∀ i : Fin M, ∃ G : Finset (List ℕ × ℕ),
      (∀ c ∈ G, (∀ e ∈ c.1, 1 ≤ e) ∧ 1 ≤ c.2) ∧
      (∀ z : ℝ, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → z ∈ clusterSet (net.cen i) w κ →
        ∃ c ∈ G, z ∈ cellSet c.1 c.2) ∧
      ∑ c ∈ G, (gaussMeasure (cellSet c.1 c.2)).toReal
        ≤ (1 / Real.log 2) * (2 * ((net.cen i).pullLip * (V + 2 * κ))) + δ := by
    intro i
    exact exists_cover_clusterSet (net.cen i) w hw hwpos hκ hδ
  choose F hFpos hFcov hFmass using hcovex
  intro ε hε i
  by_cases hused : ∃ m : ℕ, net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width
  · refine classFreqSlack_at w hx hmem hCFn hL hUlen hUsel (hUne i) (hFpos i) (hFcov i) ?_ hε
    have hmono : (net.cen i).pullLip * (V + 2 * κ) ≤ P * (V + 2 * κ) := by
      have hfac : 0 ≤ V + 2 * κ := by positivity
      exact mul_le_mul_of_nonneg_right (hP i hused) hfac
    have hstep : ∑ c ∈ F i, (gaussMeasure (cellSet c.1 c.2)).toReal
        ≤ (1 / Real.log 2) * (2 * (P * (V + 2 * κ))) + δ := by
      refine le_trans (hFmass i) ?_
      have h2 : (1 / Real.log 2) * (2 * ((net.cen i).pullLip * (V + 2 * κ)))
          ≤ (1 / Real.log 2) * (2 * (P * (V + 2 * κ))) := by
        have h3 : (2:ℝ) * ((net.cen i).pullLip * (V + 2 * κ)) ≤ 2 * (P * (V + 2 * κ)) := by
          linarith
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
    have hCq : (0:ℝ) ≤ 1 + 8 * Real.log 2 := by positivity
    exact mul_le_mul_of_nonneg_left hstep hCq
  · -- an unused cell: both counts vanish
    push_neg at hused
    refine ⟨0, le_refl 0, ?_⟩
    filter_upwards with q
    obtain ⟨h1, h2⟩ := cellCounts_eq_zero_of_unused (w := w)
      (fun m => by
        intro hm
        exact absurd hm.2 (not_le.mpr (hused m hm.1))) q
    rw [h1, h2]
    norm_num

end MapState

section Audit

#print axioms MapState.cellCounts_eq_zero_of_unused
#print axioms MapState.classFreqSlack_of_cellMemory'

end Audit

end NormalNumbers.VandeheyS7
