/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinMultiShiftAux
import NormalNumbers.CoefmassErdosBorweinShift

/-!
# Normal above the sub-power weight for every `c < 1`, given the `J`-shift Kubilius model
(personal-c5, 2026-10-26)

All definitions and the headline are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never
edit them.  `MultiShiftKubiliusTV` is a named hypothesis: never prove, weaken or axiomatize it.
The paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Normal for c < 1 given
the J-shift Kubilius model"; the plan is in `EB-MULTISHIFT-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinMultiShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint NormalNumbers.ErdosBorweinShift

/-- The sub-power weight `(log m)^{−ln 2} · exp(−ln 2 · √(c·u·log u))`, with `u = log log m`.  Where
`c·u·log u < 0` (small `m`), `Real.sqrt` returns `0` and the weight is `(log m)^{−ln 2}`. -/
noncomputable def subpowerWeight (c : ℝ) (m : ℕ) : ℝ :=
  Real.rpow (Real.log m) (-Real.log 2) *
    Real.exp (-(Real.log 2) * Real.sqrt (c * Real.log (Real.log m) * Real.log (Real.log (Real.log m))))

/-- The primes in `(P, y]`. -/
def primesIoc (P y : ℕ) : Finset ℕ := (Finset.Ioc P y).filter Nat.Prime

/-- The `J`-shift prime pattern of `n`: for each shift `j < J`, the primes in `(P, y]` that divide
`n + j + 1`. -/
def multiShiftPattern (P y J n : ℕ) : Fin J → Finset ℕ :=
  fun j => (n + j + 1).primeFactors.filter (fun p => P < p ∧ p ≤ y)

open Classical in
/-- Mass of `A` under the `J`-shift Kubilius model.  Each prime `p ∈ (P, y]` independently picks the
shift `j` with probability `1/p` (for each `j < J`), or no shift with probability `1 − J/p`. -/
noncomputable def multiShiftMass (P y J : ℕ) (A : Set (Fin J → Finset ℕ)) : ℝ :=
  ∑ σ : (primesIoc P y) → Option (Fin J),
    if (fun j => ((Finset.univ.filter (fun p : primesIoc P y => σ p = some j)).map
        (Function.Embedding.subtype _))) ∈ A then
      ∏ p : primesIoc P y, (match σ p with
        | none => 1 - (J : ℝ) / (p : ℕ)
        | some _ => 1 / ((p : ℕ) : ℝ))
    else 0

open Classical in
/-- **Hypothesis (sieve, dimension `J`): the `J`-shift Kubilius model.**  This is the natural
`J`-dimensional extension of `KubiliusTV`.  It is expected from the fundamental lemma of sieve theory
in dimension `J` at level `N^{1/2}`.  The large-pattern mass is `e^{−u/2 + 2J}` by Rankin, and the
remainder is `≤ N^{−1/2}(log N)^J`.  Searched for (2026-10-26) and not found in print: Tenenbaum
1999, Ford 2025 (IMRN rnaf079) and Gorodetsky (arXiv 2608.14190, Thm 2.3 and Cor 2.5) treat a single
sequence.  A named hypothesis, not an axiom.  Confidence 85% in this form. -/
def MultiShiftKubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y J P : ℕ, 1 ≤ J → J ≤ P → 2 ≤ y → y ≤ N →
    C * J * Real.log (J + 2) ≤ Real.log N / Real.log y →
    ∀ A : Set (Fin J → Finset ℕ),
      |(((Finset.Icc 1 N).filter (fun n => multiShiftPattern P y J n ∈ A)).card : ℝ) / N -
          multiShiftMass P y J A| ≤
        C * (Real.exp (-(Real.log N / Real.log y) / C) + Real.log N ^ J / Real.sqrt N)

/-- **Target (positive side): normal above the sub-power weight for every `c < 1`, given the
`J`-shift Kubilius model.**  This is `EBLogWindow`'s normal half at its conjectured threshold.
Step 1′ (`ebRandom_ae_normal_of_shiftedVariance_diverges`) is fed by heavy-neighbour coverage.
Take `J ≍ √L` and `y₀ = N^{1/u}` with `u = J (log L)³`.  The heavy event for shift `j` is
`#{p ∈ (P₀, y₀] : p ∣ n+j} ≥ mean + ψ(L₀) + 2j log₂ b + B log L`, giving
`W(n+j) ≥ T b^{2j}` by the chain bound.  In the model, couple to independent shifts (cost
`J²/P₀`) and use a tilted-Chebyshev moderate-deviation lower bound.  Then
`P(no heavy) ≤ exp(−Σ_j p_j)` with `Σ_j p_j ≳ L^{−c(1+ε)/2}√(L/log L) → ∞`.  One TV application
transfers the event.  Draft: "Normal for c < 1 given the J-shift Kubilius model".  Confidence 70%. -/
theorem ebRandom_ae_normal_subpower_of_multiShift (hM : MultiShiftKubiliusTV)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c c₀ : ℝ) (hc : c < 1) (hc₀ : 0 < c₀)
    (hdelta : ∀ m : ℕ, 2 ≤ m → c₀ * subpowerWeight c m ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinMultiShift
