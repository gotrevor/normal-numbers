/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-PN: the net centre's `pullLip`, from the wide state it is near — the last plumbing gap

S7-CA proves `ClassFreqBoundSlack` from `CellMemory` plus a uniform bound `P` on the `pullLip` of
the **used** centres.  Lap 79's next action #1 was to remove `P` as a hypothesis.  That is what
this module does, unconditionally.

A used centre `cen` is entrywise `ρ`-close to a wide run state `s` (`StateNet.near`), and a wide
state has all four entries bounded by its own `denMax`, with

    denMax s ^ 2 = pullLip s · |det s| ≤ K·|det s| / width s ≤ K·|det Φ| / η

(`denMax_sq_le_of_denRatio`, from `pullLip_le_of_denRatio`; along a run `K = 6` by S7-Box).  So

    pullLip cen = denMax cen ^ 2 / |det cen| ≤ (E + 2ρ)^2 / (|det s| − 4ρ(E+ρ))

(`pullLip_le_of_near`), where `E` bounds `denMax s`: the numerator moves by at most `2ρ` because
`d` and `c+d` each move by at most `ρ` and `2ρ`, and the determinant moves by at most `4ρ(E+ρ)`
because every entry is bounded by `E` in absolute value (`abs_entries_le_denMax`).

Letting `ρ → 0` with `E = √(6|det Φ|/η)` gives `P → 6/η`, so any `P > 6/η` is admissible for all
small `ρ` — the hypothesis of S7-CA is discharged by a choice of `ρ`, not by an assumption.

## Guard rule

Content locator: at `ρ = 0` the bound is `E²/|det s|`, which is exactly `pullLip s` when `E` is
sharp — so all the content is in the two perturbation estimates.  Degenerate case: if
`4ρ(E+ρ) ≥ |det s|` the bound is vacuous and the hypothesis `hpos` excludes it; that is the honest
statement that a coarse net cannot see the determinant at all.
-/
import NormalNumbers.VandeheyS7PullMap
import NormalNumbers.VandeheyS7Box

namespace NormalNumbers.VandeheyS7

namespace MapState

/-- Every entry of a state is bounded by its `denMax` in absolute value. -/
theorem abs_entries_le_denMax (s : MapState) :
    |s.a| ≤ s.denMax ∧ |s.b| ≤ s.denMax ∧ |s.c| ≤ s.denMax ∧ |s.d| ≤ s.denMax := by
  have h1 : s.d ≤ s.denMax := le_max_left _ _
  have h2 : s.c + s.d ≤ s.denMax := le_max_right _ _
  have hd := s.hd
  have hcd := s.hcd
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith [s.hab0, s.hbd]
  · linarith [s.habcd, s.hb0]
  · linarith [s.hb0]
  · linarith [s.hbd]
  · linarith
  · linarith
  · linarith
  · linarith

/-- `denMax ^ 2 = pullLip · |det|`. -/
lemma denMax_sq_eq (s : MapState) : s.denMax ^ 2 = s.pullLip * |s.det| := by
  have hdet : (0:ℝ) < |s.det| := abs_pos.mpr s.hdet
  rw [pullLip, div_mul_cancel₀ _ hdet.ne']

/-- **The size of a wide state.**  With the denominator ratio in `[1/K, K]`,
`denMax ^ 2 ≤ K·|det| / width`. -/
theorem denMax_sq_le_of_denRatio (s : MapState) {K : ℝ} (hK : 1 ≤ K)
    (hlow : 1 / K ≤ s.denRatio) (hhigh : s.denRatio ≤ K) :
    s.denMax ^ 2 ≤ K * |s.det| / s.width := by
  have hdet : (0:ℝ) < |s.det| := abs_pos.mpr s.hdet
  have h := s.pullLip_le_of_denRatio hK hlow hhigh
  rw [denMax_sq_eq]
  calc s.pullLip * |s.det| ≤ (K / s.width) * |s.det| :=
        mul_le_mul_of_nonneg_right h hdet.le
    _ = K * |s.det| / s.width := by ring

/-- **The perturbation bound.**  A centre entrywise `ρ`-close to `s` has a controlled `pullLip`. -/
theorem pullLip_le_of_near {s cen : MapState} {ρ E : ℝ} (hρ : 0 ≤ ρ)
    (hE : s.denMax ≤ E)
    (ha : |cen.a - s.a| ≤ ρ) (hb : |cen.b - s.b| ≤ ρ)
    (hc : |cen.c - s.c| ≤ ρ) (hd : |cen.d - s.d| ≤ ρ)
    (hpos : 0 < |s.det| - 4 * ρ * (E + ρ)) :
    cen.pullLip ≤ (E + 2 * ρ) ^ 2 / (|s.det| - 4 * ρ * (E + ρ)) := by
  obtain ⟨hA, hB, hC, hD⟩ := s.abs_entries_le_denMax
  have hEnn : 0 ≤ E := le_trans s.denMax_pos.le hE
  -- entry bounds for `s` and for `cen`
  have hsa : |s.a| ≤ E := le_trans hA hE
  have hsb : |s.b| ≤ E := le_trans hB hE
  have hsc : |s.c| ≤ E := le_trans hC hE
  have hsd : |s.d| ≤ E := le_trans hD hE
  have hca : |cen.a| ≤ E + ρ := by
    have := abs_sub_abs_le_abs_sub cen.a s.a; linarith
  have hcb : |cen.b| ≤ E + ρ := by
    have := abs_sub_abs_le_abs_sub cen.b s.b; linarith
  have hcc : |cen.c| ≤ E + ρ := by
    have := abs_sub_abs_le_abs_sub cen.c s.c; linarith
  have hcd' : |cen.d| ≤ E + ρ := by
    have := abs_sub_abs_le_abs_sub cen.d s.d; linarith
  -- the numerator
  have hnum : cen.denMax ≤ E + 2 * ρ := by
    have h1 : cen.d ≤ s.d + ρ := by
      have := abs_le.mp hd; linarith [this.2]
    have h2 : cen.c + cen.d ≤ (s.c + s.d) + 2 * ρ := by
      have h3 := abs_le.mp hc
      have h4 := abs_le.mp hd
      linarith [h3.2, h4.2]
    have hs1 : s.d ≤ E := le_trans (le_max_left _ _) hE
    have hs2 : s.c + s.d ≤ E := le_trans (le_max_right _ _) hE
    rw [denMax]
    exact max_le (by linarith) (by linarith)
  -- the determinant
  have hdet : |s.det| - 4 * ρ * (E + ρ) ≤ |cen.det| := by
    have hkey : |cen.det - s.det| ≤ 4 * ρ * (E + ρ) := by
      set p1 : ℝ := cen.a * (cen.d - s.d) with hp1
      set p2 : ℝ := s.d * (cen.a - s.a) with hp2
      set p3 : ℝ := cen.b * (cen.c - s.c) with hp3
      set p4 : ℝ := s.c * (cen.b - s.b) with hp4
      have hexp : cen.det - s.det = (p1 + p2) - (p3 + p4) := by
        simp only [MapState.det, hp1, hp2, hp3, hp4]; ring
      have b1 : |p1| ≤ (E + ρ) * ρ := by
        rw [hp1, abs_mul]; exact mul_le_mul hca hd (abs_nonneg _) (by linarith)
      have b2 : |p2| ≤ E * ρ := by
        rw [hp2, abs_mul]; exact mul_le_mul hsd ha (abs_nonneg _) hEnn
      have b3 : |p3| ≤ (E + ρ) * ρ := by
        rw [hp3, abs_mul]; exact mul_le_mul hcb hc (abs_nonneg _) (by linarith)
      have b4 : |p4| ≤ E * ρ := by
        rw [hp4, abs_mul]; exact mul_le_mul hsc hb (abs_nonneg _) hEnn
      have c1 := abs_le.mp b1
      have c2 := abs_le.mp b2
      have c3 := abs_le.mp b3
      have c4 := abs_le.mp b4
      have hsq : (0:ℝ) ≤ ρ * ρ := mul_nonneg hρ hρ
      rw [abs_le]
      constructor <;> rw [hexp] <;> nlinarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2]
    have h2 := abs_sub_abs_le_abs_sub s.det cen.det
    rw [abs_sub_comm s.det cen.det] at h2
    linarith
  have hcendet : (0:ℝ) < |cen.det| := lt_of_lt_of_le hpos hdet
  rw [pullLip, div_le_div_iff₀ hcendet hpos]
  have hcm := cen.denMax_pos
  have hsq2 : cen.denMax ^ 2 ≤ (E + 2 * ρ) ^ 2 := by nlinarith [hnum, hcm]
  calc cen.denMax ^ 2 * (|s.det| - 4 * ρ * (E + ρ))
      ≤ (E + 2 * ρ) ^ 2 * (|s.det| - 4 * ρ * (E + ρ)) :=
        mul_le_mul_of_nonneg_right hsq2 hpos.le
    _ ≤ (E + 2 * ρ) ^ 2 * |cen.det| :=
        mul_le_mul_of_nonneg_left hdet (by positivity)

end MapState

section Audit

#print axioms MapState.abs_entries_le_denMax
#print axioms MapState.denMax_sq_le_of_denRatio
#print axioms MapState.pullLip_le_of_near

end Audit

end NormalNumbers.VandeheyS7
