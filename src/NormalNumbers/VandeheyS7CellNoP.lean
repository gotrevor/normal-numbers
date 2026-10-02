/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CB: `ClassFreqBoundSlack` from `CellMemory` alone — the `P` hypothesis is gone

S7-CA proved `ClassFreqBoundSlack` from `CellMemory` plus a uniform bound `P` on the `pullLip` of
the used centres.  S7-PN bounds that `pullLip` unconditionally; this module joins the two, so the
front's per-cell input is now **exactly** `CellMemory` plus a smallness condition on the net's own
precision `ρ`, which the net supplies for free.

    pullLip (net.cen i)  ≤  (E + 2ρ)² / (|det Φ| − 4ρ(E + ρ)),     E = √(6·|det Φ|/η)

(`pullLip_cen_le`), for every **used** cell, because that cell's centre is entrywise `ρ`-close to
a wide run state whose `denMax` is at most `E` (`denMax_sq_le_of_denRatio` with the run's band
`denRatio ∈ (1/2, 6]`, S7-Box).  As `ρ → 0` the bound tends to `E²/|det Φ| = 6/η`.

`classFreqSlack_of_cellMemory_noP` is S7-CA with `P` instantiated.

## Guard rule

Content locator: at `ρ = 0` the bound reads `6/η`, which is `pullLip_le_of_denRatio` itself — all
the new content is the perturbation.  Degenerate case: `4ρ(E+ρ) ≥ |det Φ|` (a net too coarse to
see the determinant) is excluded by the hypothesis, and is the honest failure mode.
-/
import NormalNumbers.VandeheyS7CellAll
import NormalNumbers.VandeheyS7PullNear

namespace NormalNumbers.VandeheyS7

open MeasureTheory

namespace MapState

variable {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}

/-- The run's box scale: `E = √(6·|det Φ|/η)`. -/
noncomputable def boxScale (Φ : MapState) (η : ℝ) : ℝ := Real.sqrt (6 * |Φ.det| / η)

lemma boxScale_nonneg (Φ : MapState) (η : ℝ) : 0 ≤ boxScale Φ η := Real.sqrt_nonneg _

/-- The resulting uniform `pullLip` bound for a net of precision `ρ` at width floor `η`. -/
noncomputable def pullBound (Φ : MapState) (η ρ : ℝ) : ℝ :=
  (boxScale Φ η + 2 * ρ) ^ 2 / (|Φ.det| - 4 * ρ * (boxScale Φ η + ρ))

/-- A wide run state has `denMax ≤ boxScale`. -/
theorem denMax_runState_le {Φ : MapState} {x η : ℝ} (hη : 0 < η) (n : ℕ)
    (hw : η ≤ (runState Φ x (n + 2)).width) :
    (runState Φ x (n + 2)).denMax ≤ boxScale Φ η := by
  set s := runState Φ x (n + 2) with hs
  have hdet : |s.det| = |Φ.det| := absDet_runState Φ x (n + 2)
  have hdpos : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hband1 : 1 / (6:ℝ) ≤ s.denRatio := by
    have h := half_lt_denRatio_runState_succ Φ x (n + 1)
    have : (1:ℝ) / 6 ≤ 1 / 2 := by norm_num
    rw [hs]; linarith [h]
  have hband2 : s.denRatio ≤ 6 := by rw [hs]; exact denRatio_runState_le_six Φ x n
  have hsq := s.denMax_sq_le_of_denRatio (by norm_num : (1:ℝ) ≤ 6) hband1 hband2
  have hwpos : (0:ℝ) < s.width := lt_of_lt_of_le hη hw
  have hmono : 6 * |s.det| / s.width ≤ 6 * |Φ.det| / η := by
    rw [hdet]
    exact div_le_div_of_nonneg_left (by positivity) hη hw
  rw [boxScale]
  exact Real.le_sqrt_of_sq_le (by linarith [hsq, hmono])

/-- **The used centre's `pullLip`, unconditionally.** -/
theorem pullLip_cen_le (hη : 0 < η) (hρ : 0 ≤ ρ) (net : StateNet Φ x η ρ M) (i : Fin M)
    (hused : ∃ m : ℕ, net.idx m = i ∧ η ≤ (runState Φ x (m + 2)).width)
    (hfine : 0 < |Φ.det| - 4 * ρ * (boxScale Φ η + ρ)) :
    (net.cen i).pullLip ≤ pullBound Φ η ρ := by
  obtain ⟨m, hidx, hw⟩ := hused
  set s := runState Φ x (m + 2) with hs
  obtain ⟨h1, h2, h3, h4⟩ := net.near m hw
  rw [hidx] at h1 h2 h3 h4
  have hE : s.denMax ≤ boxScale Φ η := denMax_runState_le hη m hw
  have hdet : |s.det| = |Φ.det| := absDet_runState Φ x (m + 2)
  have key := pullLip_le_of_near (s := s) (cen := net.cen i) hρ hE
    (by rw [abs_sub_comm]; exact h1) (by rw [abs_sub_comm]; exact h2)
    (by rw [abs_sub_comm]; exact h3) (by rw [abs_sub_comm]; exact h4)
    (by rw [hdet]; exact hfine)
  rw [pullBound]
  rwa [hdet] at key

open Classical in
/-- **S7-CB.**  S7-CA with the `pullLip` hypothesis discharged: `ClassFreqBoundSlack` from
`CellMemory` data and a net fine enough to see the determinant. -/
theorem classFreqSlack_of_cellMemory_noP {net : StateNet Φ x η ρ M} {L : ℕ}
    {U : Fin M → Finset (List ℕ)} {δ : ℝ} (w : List ℕ) (hw : w ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a)
    (hx : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1) (hCFn : IsCFNormal x) (hL : 2 ≤ L)
    (hη : 0 < η) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hfine : 0 < |Φ.det| - 4 * ρ * (boxScale Φ η + ρ))
    (hUlen : ∀ i : Fin M, ∀ u ∈ U i, u.length = L ∧ (∀ a ∈ u, 1 ≤ a))
    (hUsel : ∀ i : Fin M, ∀ m : ℕ, L ≤ m + 2 →
      selIndic net i m
        = if ∃ u ∈ U i, gaussMap^[m + 2 - L] x ∈ cfCylinder u then 1 else 0)
    (hUne : ∀ i : Fin M, (U i).Nonempty) :
    ClassFreqBoundSlack net w
      ((1 + 8 * Real.log 2) *
        ((1 / Real.log 2) *
          (2 * ((pullBound Φ η ρ) *
            ((volume (cfCylinder w)).toReal
              + 2 * (4 * ρ / Real.sqrt (|Φ.det| / 6))))) + δ)) := by
  refine classFreqSlack_of_cellMemory' w hw hwpos hx hmem hCFn hL (by positivity) hδ
    hUlen hUsel hUne ?_
  intro i hused
  exact pullLip_cen_le hη hρ net i hused hfine

end MapState

section Audit

#print axioms MapState.denMax_runState_le
#print axioms MapState.pullLip_cen_le
#print axioms MapState.classFreqSlack_of_cellMemory_noP

end Audit

end NormalNumbers.VandeheyS7
