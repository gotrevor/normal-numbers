/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinMultiShift

/-!
# Normal above the sub-power weight for every `c < 1`, given only the pair Kubilius model
(personal-c5, 2026-10-26)

All definitions and the headline are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never
edit them.  `PairShiftKubiliusTV` is a named hypothesis: never prove, weaken or axiomatize it.  Do not
use `MultiShiftKubiliusTV` (the point of this file is to avoid it).  The paper argument is in
`nn-erdos-borwein-random-2026-10-12.md`, section "Normal for c < 1 from a pair model only"; the plan
is in `EB-PAIRSHIFT-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinPairShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint NormalNumbers.ErdosBorweinShift
open NormalNumbers.ErdosBorweinMultiShift

/-- The primes in `(P, y]` that divide `m`. -/
def primePatternIoc (P y m : ℕ) : Finset ℕ := m.primeFactors.filter (fun p => P < p ∧ p ≤ y)

open Classical in
/-- Mass of `A` under the pair Kubilius model.  Each prime `p ∈ (P, y]` independently divides the
first shift (`some false`) with probability `1/p`, the second (`some true`) with probability `1/p`,
or neither with probability `1 − 2/p`. -/
noncomputable def pairShiftMass (P y : ℕ) (A : Set (Finset ℕ × Finset ℕ)) : ℝ :=
  ∑ σ : (primesIoc P y) → Option Bool,
    if ((Finset.univ.filter (fun p : primesIoc P y => σ p = some false)).map
          (Function.Embedding.subtype _),
        (Finset.univ.filter (fun p : primesIoc P y => σ p = some true)).map
          (Function.Embedding.subtype _)) ∈ A then
      ∏ p : primesIoc P y, (match σ p with
        | none => 1 - 2 / ((p : ℕ) : ℝ)
        | some _ => 1 / ((p : ℕ) : ℝ))
    else 0

open Classical in
/-- **Hypothesis (sieve, dimension 2): the pair Kubilius model.**  For two shifts `a < b ≤ N` with
`b − a ≤ P`, every prime `p > P` divides at most one of `n + a`, `n + b`.  The joint pattern of the
primes in `(P, y]` dividing them, for `n ≤ N` uniform, is within `C(e^{−u/C} + (log N)²/√N)` of the
pair model, `u = log N / log y`.  Expected from the fundamental lemma in fixed dimension `2` with
Rankin truncation.  A named hypothesis, not an axiom.  Confidence 92%. -/
def PairShiftKubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y P a b : ℕ, 2 ≤ P → a < b → b - a ≤ P → b ≤ N → 2 ≤ y → y ≤ N →
    ∀ A : Set (Finset ℕ × Finset ℕ),
      |(((Finset.Icc 1 N).filter (fun n =>
          (primePatternIoc P y (n + a), primePatternIoc P y (n + b)) ∈ A)).card : ℝ) / N -
          pairShiftMass P y A| ≤
        C * (Real.exp (-(Real.log N / Real.log y) / C) + Real.log N ^ 2 / Real.sqrt N)

/-- **Target: normal above the sub-power weight for every `c < 1`, given only the pair model.**  The
same conclusion as `ebRandom_ae_normal_subpower_of_multiShift`.  Count the heavy shifts
`Z = Σ_j 1[H_j]` and apply Chebyshev: in the pair model the heavy events are independent up to
`2/P₀`, so `Var Z/(E Z)² ≤ 1/Σ q_j + 2J²/(P₀ (Σ q_j)²) → 0`, using only the lower bound on `q_j`
and `Σ q_j → ∞`.  Draft: "Normal for c < 1 from a pair model only".  Confidence 85%. -/
theorem ebRandom_ae_normal_subpower_of_pairShift (hP : PairShiftKubiliusTV)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c c₀ : ℝ) (hc : c < 1) (hc₀ : 0 < c₀)
    (hdelta : ∀ m : ℕ, 2 ≤ m → c₀ * subpowerWeight c m ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinPairShift
