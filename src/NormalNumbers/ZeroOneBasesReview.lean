/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ZeroOneBases

/-!
# Review of the zero endpoint in the literature counting premise

The current `BurrellYuFourFive` premise counts zero but bounds its counting function by
`C * n ^ ε` even at `n = 0`.  This refutes that transcription, not the published theorem.
The intended repair is to restrict the bound to positive `n`, or use `n + 1` on the right.
The original declaration is left intact for review by its owning session.
-/

namespace NormalNumbers.ZeroOneBases.Review

/-- The recorded counting premise fails at `ε = 1`, `n = 0`: it asserts `1 ≤ 0`. -/
theorem not_burrellYuFourFive : ¬ Literature.BurrellYuFourFive := by
  intro h
  obtain ⟨C, hC⟩ := h 1 (by norm_num)
  have hz := hC 0
  norm_num [NormalNumbers.Literature.DigitsOfPowers.ZeroOneIn] at hz

end NormalNumbers.ZeroOneBases.Review
