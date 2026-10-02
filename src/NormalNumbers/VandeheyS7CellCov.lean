/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CV: the cover input, discharged — the cluster set IS covered by cheap cells

S7-CT reduced the per-cell bound to `CellMemory` plus "a finite cell family covering the cluster
set, of small total mass".  S7-CS made the cluster set an interval of length
`2·pullLip·(|I_w| + 2κ)`, and `cellCover_inv_log_two` covers any subinterval of `(0,1)` by cells of
total mass `≤ (1/log 2)·length + δ`.  Joining them:

    `exists_cover_clusterSet` :  ∃ F,  F covers `clusterSet t w κ` along irrational points  ∧
        Σ_{c ∈ F} γ(cellSet c) ≤ (1/log 2)·2·pullLip·(|I_w| + 2κ) + δ .

So the cover is NOT an extra hypothesis, and the per-cell constant of S7-CT becomes explicit:

    `B = (1 + 8 log 2)·((2/log 2)·pullLip·(|I_w| + 2κ) + δ)`,

which on a state of width `≥ η` with `denRatio ∈ [1/K, K]` is `O(K·γ(I_w)/η + κ/η)` — exactly the
`Cp·γ/η` shape S7-MD prices.
-/
import NormalNumbers.VandeheyS7Cluster
import NormalNumbers.VandeheyS7Cell

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

/-- **S7-CV.**  A finite cell cover of the cluster set, of mass controlled by the cluster set's
length. -/
theorem exists_cover_clusterSet (t : MapState) (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) {κ : ℝ} (hκ : 0 ≤ κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Finset (List ℕ × ℕ),
      (∀ c ∈ F, (∀ e ∈ c.1, 1 ≤ e) ∧ 1 ≤ c.2) ∧
      (∀ z : ℝ, Irrational z → z ∈ Set.Ioo (0:ℝ) 1 → z ∈ clusterSet t w κ →
        ∃ c ∈ F, z ∈ cellSet c.1 c.2) ∧
      ∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal
        ≤ (1 / Real.log 2) * (2 * (t.pullLip * ((volume (cfCylinder w)).toReal + 2 * κ))) + δ := by
  classical
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := t.pullLip * ((volume (cfCylinder w)).toReal + 2 * κ) with hD
  have hDnn : 0 ≤ D := by
    have := t.pullLip_pos
    rw [hD]; positivity
  obtain ⟨α, hα⟩ := clusterSet_subset_Icc t w hw hpos hκ
  rcases Set.eq_empty_or_nonempty (clusterSet t w κ) with hemp | ⟨z₀, hz₀⟩
  · refine ⟨∅, by simp, ?_, ?_⟩
    · intro z _ _ hz; rw [hemp] at hz; exact absurd hz (Set.notMem_empty z)
    · simp only [Finset.sum_empty]
      positivity
  -- a slightly enlarged interval inside `[0,1]`
  set ν : ℝ := δ * Real.log 2 / 8 with hν
  have hνpos : 0 < ν := by rw [hν]; positivity
  have hz₀I := hα hz₀
  have hz₀m : z₀ ∈ Set.Ioo (0:ℝ) 1 := hz₀.2
  set a' : ℝ := max 0 (α - ν) with ha'
  set b' : ℝ := min 1 (α + 2 * D + ν) with hb'
  have ha'0 : 0 ≤ a' := le_max_left _ _
  have hb'1 : b' ≤ 1 := min_le_left _ _
  have hab' : a' ≤ b' := by
    have h1 : α ≤ z₀ := hz₀I.1
    have h2 : z₀ ≤ α + 2 * D := hz₀I.2
    rw [ha', hb']
    refine max_le ?_ ?_
    · exact le_min zero_le_one (by linarith [hz₀m.1])
    · exact le_min (by linarith [hz₀m.2]) (by linarith)
  obtain ⟨F, hFpos, hFcov, hFmass⟩ := cellCover_inv_log_two a' b' ha'0 hab' hb'1 (δ / 2)
    (by positivity)
  refine ⟨F, hFpos, ?_, ?_⟩
  · intro z hzirr hzmem hzcl
    refine hFcov z hzirr hzmem ?_
    have hzI := hα hzcl
    constructor
    · rw [ha']
      refine max_lt hzmem.1 ?_
      linarith [hzI.1]
    · rw [hb']
      refine lt_min hzmem.2 ?_
      linarith [hzI.2]
  · have hlen : b' - a' ≤ 2 * D + 2 * ν := by
      have h1 : b' ≤ α + 2 * D + ν := min_le_right _ _
      have h2 : α - ν ≤ a' := le_max_right _ _
      linarith
    have hνle : (1 / Real.log 2) * (2 * ν) ≤ δ / 2 := by
      rw [hν]
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hlog (by norm_num)]
      nlinarith [hlog, hδ]
    have hmono : (1 / Real.log 2) * (b' - a') ≤ (1 / Real.log 2) * (2 * D + 2 * ν) :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    have hsplit : (1 / Real.log 2) * (2 * D + 2 * ν)
        = (1 / Real.log 2) * (2 * D) + (1 / Real.log 2) * (2 * ν) := by ring
    linarith
end MapState

section Audit

#print axioms MapState.exists_cover_clusterSet

end Audit

end NormalNumbers.VandeheyS7
