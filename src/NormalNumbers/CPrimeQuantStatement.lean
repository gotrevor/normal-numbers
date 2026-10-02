/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelFamilyGraded

/-!
# Quantitative C′: the frozen statements

Theorem C′ (`isNormal_subsetLambert_of_sqrtFreshMassZero`) makes `∑_{p∈P} 1/(4ᵖ−1)` normal when
the square-root fresh mass `r_P(N) = ∑_{√N<p≤N, p∈P} 1/p` tends to `0`.  This file freezes what
the same proof gives when `r_P` stays **bounded by `ρ > 0`**: an orbit discrepancy of order
`ρ·log³(1/ρ)`.  Primes `≡ a (mod q)` have `ρ = log 2/φ(q)`, so every base-4 word of fixed length
has positive lower frequency in `∑_{p≡a (q)} 1/(4ᵖ−1)` once `q` is large.

Paper derivation, constants and the review targets: `docs/CPRIME-QUANTITATIVE-2026-09-30.md`.

## Guard rule

**Content locator.**  At `ρ → 0` the discrepancy bound tends to `0`, which is C′ itself; the new
content is entirely the bounded-`ρ` bookkeeping (a FIXED schedule parameter `u` in place of
`u_N → ∞`).

**Degenerate cases.**  All primes have `ρ = log 2`, outside `ρ ≤ ρ₀`: the statement says nothing
about G₄, as it must not; small moduli are excluded by `q₀ ≤ q`.  A finite `P` has
`ρ = 0` eventually but fails `DivergentRecip`, which the discrepancy form assumes; its Lambert
constant is rational and its orbit is periodic, so the hypothesis is load-bearing.  The empty
word has frequency `1` and positive lower frequency trivially.
-/

namespace NormalNumbers.PrimeModel.Quant

open Filter

/-- The multiply-by-4 orbit of `x` has asymptotic interval discrepancy at most `D`: for every
`[a,c) ⊆ [0,1]` the visit frequency is eventually within `D + ε` of `c − a`. -/
def OrbitDefectLe (x D : ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    |(visitCount (orbit 4 x) a c n : ℝ) / n - (c - a)| ≤ D + ε

/-- The square-root fresh mass of `P` is eventually at most `ρ + ε`, for every `ε > 0`. -/
def SqrtFreshMassLe (P : ℕ → Prop) [DecidablePred P] (ρ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in atTop, G4Sparse.recipSumIoc P (Nat.sqrt N) N ≤ ρ + ε

/-- **Quantitative C′ (frozen).**  Bounded square-root fresh mass `ρ ≤ ρ₀` and a divergent
reciprocal sum give orbit discrepancy `≤ C·ρ·log³(1/ρ)`. -/
def CPrimeQuant : Prop :=
  ∃ C ρ₀ : ℝ, 0 < C ∧ 0 < ρ₀ ∧ ρ₀ < 1 ∧
    ∀ (P : ℕ → Prop) [DecidablePred P], G4Sparse.DivergentRecip P →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → SqrtFreshMassLe P ρ →
        OrbitDefectLe (PrimeLambert.subsetLambert P 4) (C * ρ * Real.log (1 / ρ) ^ 3)

/-- **Residue-class richness (frozen corollary).**  For each word length `L` there is `q₀` such
that, for every modulus `q ≥ q₀` and unit `a`, every base-4 word of length `L` has positive lower
frequency in the digits of `∑_{p ≡ a (q)} 1/(4ᵖ−1)`. -/
def CPrimeResidueRich : Prop :=
  ∀ L : ℕ, ∃ q₀ : ℕ, ∀ q a : ℕ, q₀ ≤ q → Nat.Coprime a q →
    ∀ w : List ℕ, w.length = L → (∀ d ∈ w, d < 4) →
      ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        c ≤ (countOccurrences w ((List.range n).map
          (digitOf 4 (Int.fract (PrimeLambert.subsetLambert (fun p => p % q = a % q) 4)))) : ℝ) / n

end NormalNumbers.PrimeModel.Quant
