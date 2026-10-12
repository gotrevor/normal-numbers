/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinPositive

/-!
# Random Erdős–Borwein subseries: the growing-moment criterion

Statements copied VERBATIM from the private KB packet `NNErdosBorweinRandom.lean` at 2a0cfb6c
(namespace relocated).  Paper argument: `nn-erdos-borwein-random-2026-10-12.md`, section "The
endpoint resolved", Step 1.  LOCAL-ONLY branch.

Step 1 only: if the selection-variance mass over the divisors of `n + a₀` above
`P₀(N) = exp((log log N)²)` diverges in density, then a.s. `E_b` is normal in every base.  The
endpoint input (Step 2, Erdős–Kac walk maximum) is NOT in this module.
-/

namespace NormalNumbers.ErdosBorweinEndpoint

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive

/-- Selection-variance mass over the divisors of `n` above `P`: `Σ_{m ∣ n, m > P} v_m`. -/
noncomputable def divisorVarianceMass (v : ℕ → ℝ) (P n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => P < m), v m

/-- The collision cutoff `P₀(N) = ⌊exp((log log N)²)⌋`. -/
noncomputable def collisionCutoff (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (Real.log N) ^ 2)⌋₊

/-- **Growing-moment criterion.**  If the variance divisor mass above `P₀(N)` of `n + a₀` diverges
in density, for every shift `a₀`, then a.s. `E_b` is normal in every base.  Proof:
1. Weyl moments factor over the independent coins.
2. A good `m` (dividing exactly one `n_i + a₀`, every other coordinate outside the last `K`
   residues) has `‖θ_m‖ ≥ |h| b^{-a₀}/2`.
3. On the no-collision event every `m > P₀` dividing some `n_i + a₀` is good, giving `φ_N^{2k}`.
   The collision count has expectation `≤ 4k²K(3/P₀ + 4/N)`.
4. Borel–Cantelli with `k_j = ⌈log j⌉`, then interpolation. -/
@[blueprint (title := "Diverging divisor variance mass forces random Erdős–Borwein normality")]
theorem ebRandom_ae_normal_of_divisorVariance_diverges
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (hdiv : ∀ a₀ : ℕ, ∀ T : ℝ, Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass (fun m => delta m * (1 - delta m)) (collisionCutoff N) (n + a₀)
          ≤ T)).card : ℝ) / N) atTop (𝓝 0)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinEndpoint
