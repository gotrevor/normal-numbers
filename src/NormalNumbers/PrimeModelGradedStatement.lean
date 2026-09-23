/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelFamilyGraded

/-!
# The audit surface for Theorem C′ (the square-root fresh-mass criterion)

`isNormal_subsetLambert_of_sqrtFreshMassZero` is restated here with **every** abbreviation
unwound: no `SqrtFreshMassZero`, no `DivergentRecip`, no `recipSumIoc`, no `subsetLambert`,
no `IsNormal`.  An auditor reads only `Nat.primeFactors`, `Nat.sqrt`, `Finset.Ioc`, a `tsum`,
the digit map `⌊x·4^{i+1}⌋ mod 4` and the word-frequency limit.

In words:

> Let `P` be a set of primes such that
>   (a) `∑_{p ∈ P, √N < p ≤ N} 1/p → 0` as `N → ∞`, and
>   (b) `∑_{p ∈ P} 1/p = ∞`.
> Then the real number `c_P = ∑_{n} #{p ∈ P : p ∣ n} / 4ⁿ` is **normal in base 4**: every
> finite word `w` over the digits `{0,1,2,3}` occurs in the base-4 expansion of `c_P` with
> asymptotic frequency exactly `4^{−|w|}`.

Note (a) is a *hypothesis about `P` alone*, and it is implied both by the older fresh-mass
condition (`sqrtFreshMassZero_of_freshMassZero`) and by relative density zero
(`sqrtFreshMassZero_of_relDensityZero`), so the audit form below is the strongest of the three.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyGraded

open NormalNumbers NormalNumbers.G4Sparse NormalNumbers.PrimeLambert

/-- **Audit form of Theorem C′.**  Definitionally equal to
`isNormal_subsetLambert_of_sqrtFreshMassZero`, with every definition of the chain unfolded. -/
theorem audit_isNormal_subsetLambert_of_sqrtFreshMassZero
    (P : ℕ → Prop) [DecidablePred P]
    -- (a) the square-root fresh reciprocal mass of `P` vanishes
    (hS : Tendsto
      (fun N : ℕ => ∑ p ∈ (Finset.Ioc (Nat.sqrt N) N).filter (fun p => p.Prime ∧ P p),
        (1 : ℝ) / p) atTop (𝓝 0))
    -- (b) the reciprocals of `P` diverge
    (hP : ¬ Summable (fun p : ℕ => if p.Prime ∧ P p then (1 : ℝ) / p else 0)) :
    ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < 4) →
      Tendsto
        (fun n : ℕ => (countOccurrences w ((List.range n).map
            (fun i : ℕ => (⌊Int.fract (∑' m : ℕ, ((m.primeFactors.filter P).card : ℝ) / (4 : ℝ) ^ m)
              * (4 : ℝ) ^ (i + 1)⌋).toNat % 4)) : ℝ) / n)
        atTop (𝓝 (((4 : ℝ) ^ w.length)⁻¹)) := by
  have hrw : (∑' m : ℕ, ((m.primeFactors.filter P).card : ℝ) / (4 : ℝ) ^ m)
      = subsetLambert P 4 := rfl
  rw [hrw]
  exact isNormal_subsetLambert_of_sqrtFreshMassZero P hS hP

end NormalNumbers.PrimeModel.FamilyGraded
