/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinEndpoint

/-!
# Step 1′: the shifted growing-moment criterion (personal-c5, 2026-10-25)

Statements are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never edit them.  The
paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Heavy neighbours", and the
plan is in `EB-SHIFT-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint

/-- The shifted divisor variance mass `Σ_{j₀ ≤ j ≤ J} b^{−2j} W(n + j)` (Step 1′). -/
noncomputable def shiftedVarianceMass (v : ℕ → ℝ) (b j₀ J P n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc j₀ J, ((b : ℝ) ^ (2 * j))⁻¹ * divisorVarianceMass v P (n + j)

/-- **Target (positive side, no arithmetic input): Step 1′, the shifted growing-moment criterion.**
A divisor `d > P₀` of `n_i + j` contributes `1 − 4v_d sin²(π h b^{−j})` to the `2k`-th moment.  So
Step 1's proof runs with the collision window `K` replaced by `2J + K`; collisions cost
`O(k²J²/P₀)`.  The binder `j₀` is needed: for `b^j ∣ h` the angle is an integer and nothing
contracts.  The proof uses `b^{j₀} ≥ 2|h|`.  Confidence 85%. -/
theorem ebRandom_ae_normal_of_shiftedVariance_diverges
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (J : ℕ → ℕ) (hJ : ∀ᶠ N : ℕ in atTop, (J N : ℝ) ≤ Real.log (Real.log N))
    (hdiv : ∀ b : ℕ, 2 ≤ b → ∀ j₀ : ℕ, ∀ T : ℝ, Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass (fun m => delta m * (1 - delta m)) b j₀ (J N)
          (collisionCutoff N) n ≤ T)).card : ℝ) / N) atTop (𝓝 0)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinShift
