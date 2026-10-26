/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinSubpowerAux

/-!
# Non-normality below the sub-power weight, `c > 3` (personal-c5, 2026-10-25)

Statements are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never edit them.  The
paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Heavy neighbours", and the
plan is in `EB-SUBPOWER-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinSubpower

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinRandom

/-- The sub-power weight `(log m)^{−ln 2} · exp(−ln 2 · √(c·u·log u))`, with `u = log log m`.  Where
`c·u·log u < 0` (small `m`), `Real.sqrt` returns `0` and the weight is `(log m)^{−ln 2}`. -/
noncomputable def subpowerWeight (c : ℝ) (m : ℕ) : ℝ :=
  Real.rpow (Real.log m) (-Real.log 2) *
    Real.exp (-(Real.log 2) * Real.sqrt (c * Real.log (Real.log m) * Real.log (Real.log (Real.log m))))

/-- **Target (negative side, elementary): non-normal below the sub-power weight at `c > 3`.**
Marginal-only, with no literature input.  The proof has three steps.
* The log-moment criterion: if `Σ_j dens{μ_M > ε b^{j/2}} → 0` as `M → ∞`, uniformly in `N`, then
  the series is non-normal.
* A per-dyadic-block Chernoff bound with `s_ℓ = √(c log u/u)/ln 2`, using the uniform moment bound
  for `τ(n_y)^s`.
* The block sum `Σ_ℓ ℓ^{1/2 − c/2}/√(log ℓ)`, finite iff `c > 3`.
The heuristic threshold is `c = 1`.  Reaching it needs a maximal inequality inside geometric blocks,
i.e. the Kubilius model.  This is strictly stronger than `ebRandom_ae_not_normal`.  Confidence 80%. -/
theorem ebRandom_ae_not_normal_subpower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c C : ℝ) (hc : 3 < c)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinSubpower
