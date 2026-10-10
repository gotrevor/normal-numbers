/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ZeroOneBases

/-!
# Review of the zero endpoint in the literature counting premise

The first transcription of `BurrellYuFourFive` counted zero but bounded its counting function by
`C * n ^ ε` even at `n = 0`, so it was false.  That form is kept here as
`BurrellYuFourFiveUnrestricted` with its refutation; `Literature.BurrellYuFourFive` now quantifies
over `n ≥ 1`.
-/

namespace NormalNumbers.ZeroOneBases.Review

/-- The first transcription, without `1 ≤ n`. -/
def BurrellYuFourFiveUnrestricted : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
    (((Finset.range (n + 1)).filter fun k =>
        NormalNumbers.Literature.DigitsOfPowers.ZeroOneIn 4 k ∧
          NormalNumbers.Literature.DigitsOfPowers.ZeroOneIn 5 k).card : ℝ) ≤
      C * (n : ℝ) ^ ε

/-- The unrestricted form fails at `ε = 1`, `n = 0`: it asserts `1 ≤ 0`. -/
theorem not_burrellYuFourFiveUnrestricted : ¬ BurrellYuFourFiveUnrestricted := by
  intro h
  obtain ⟨C, hC⟩ := h 1 (by norm_num)
  have hz := hC 0
  norm_num [NormalNumbers.Literature.DigitsOfPowers.ZeroOneIn] at hz

end NormalNumbers.ZeroOneBases.Review
