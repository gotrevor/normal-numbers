/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.RoundTwoPilotTargets

/-!
# Radical pilot: relative-norm compensation

Proves `RelativeNormCancellation`, refutes `UniformSiblingLoss` (witness a = 0),
and proves that the depth-`N` product over all signed square-root branches is a
formal telescoping identity `= 2 - a` for every seed `a ∈ [-2, 2]`.  Hence iterated
relative norms add no restriction beyond the seed itself.  See
`docs/pi-routes/pilots/radical-result.md`.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots

@[blueprint (title := "Relative radical factors exactly compensate (proved)")]
theorem relativeNormCancellation : RelativeNormCancellation := by
  intro a ha
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 + a by linarith)
  nlinarith [h]

/-- Positive control a = 0: product is exactly 2 = 2 - 0. -/
theorem relativeNorm_zero :
    (2 - Real.sqrt 2) * (2 + Real.sqrt 2) = 2 := by
  have := relativeNormCancellation 0 (by norm_num)
  simpa using this

@[blueprint (title := "No uniform sibling loss (refuted)")]
theorem not_uniformSiblingLoss : ¬ UniformSiblingLoss := by
  rintro ⟨c, hc, h⟩
  have h0 := h 0 ⟨by norm_num, by norm_num⟩
  rw [relativeNormCancellation 0 (by norm_num)] at h0
  linarith

/-- Product of `2 - x` over all `2^N` signed branches `±√(2 + ·)` below seed `x`. -/
noncomputable def branchNorm : ℕ → ℝ → ℝ
  | 0, x => 2 - x
  | n + 1, x => branchNorm n (Real.sqrt (2 + x)) * branchNorm n (-Real.sqrt (2 + x))

@[blueprint (title := "Depth-N signed-branch product telescopes to 2 - seed")]
theorem branchNorm_eq (n : ℕ) : ∀ x : ℝ, -2 ≤ x → x ≤ 2 → branchNorm n x = 2 - x := by
  induction n with
  | zero => intro x _ _; rfl
  | succ n ih =>
    intro x h1 h2
    have hs0 : 0 ≤ Real.sqrt (2 + x) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (2 + x) ≤ 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 + x by linarith)
      nlinarith
    simp only [branchNorm]
    rw [ih _ (by linarith) hs2, ih _ (by linarith) (by linarith)]
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 + x by linarith)
    nlinarith [h]

/-- Any loss bound on the full depth-`N` branch product that depends only on the
seed through `2 - a` is impossible: the product equals `2 - a` exactly. -/
theorem not_uniform_branchLoss (n : ℕ) :
    ¬ ∃ c : ℝ, c < 1 ∧ ∀ a ∈ Set.Ico (-2 : ℝ) 2, branchNorm n a ≤ c * (2 - a) := by
  rintro ⟨c, hc, h⟩
  have h0 := h 0 ⟨by norm_num, by norm_num⟩
  rw [branchNorm_eq n 0 (by norm_num) (by norm_num)] at h0
  linarith

end NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots
