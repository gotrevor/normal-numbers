/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive
import NormalNumbers.PiBBP

/-!
# Route 2: fresh BBP prime denominators

Route 2 of three experimental routes to disjunctivity of π.
See `NormalNumbers.PiDisjunctiveRoutes` for the shared framing and evidence tiers.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set

/-- The part of the BBP rational head carried by prime denominators > 4n.
Such a denominator occurs only once in the four denominator families below
8n.  The odd families are 8j+1 (coefficient 4) and 8j+5 (coefficient -1).
All other terms remain in `bbpResidual`; nothing is discarded. -/
noncomputable def bbpPrimeReservoir (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (16 : ℝ) ^ (n - j) *
    ((if Nat.Prime (8 * j + 1) ∧ 4 * n < 8 * j + 1 then
        4 / (8 * (j : ℝ) + 1) else 0) -
     (if Nat.Prime (8 * j + 5) ∧ 4 * n < 8 * j + 5 then
        1 / (8 * (j : ℝ) + 5) else 0))

noncomputable def bbpResidual (n : ℕ) : ℝ :=
  (16 : ℝ) ^ n * piPartial n - bbpPrimeReservoir n

/-- The same BBP head as an exact rational, for denominator arithmetic. -/
def bbpRationalHead (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (16 : ℚ) ^ (n - j) *
    (4 / (8 * (j : ℚ) + 1) - 2 / (8 * (j : ℚ) + 4) -
      1 / (8 * (j : ℚ) + 5) - 1 / (8 * (j : ℚ) + 6))

/-- Frozen elementary argument, 99% confidence, not yet Lean-proved.
A prime in this strip divides exactly one displayed denominator (all are
< 8n); its numerator is 4 or -1 times a power of 16, prime to p.  All
other terms are p-integral, so the pole survives in the reduced rational.
This certifies an arithmetic source, NOT independence modulo one. -/
@[blueprint (title := "Fresh BBP prime denominators survive reduction of the whole head")]
theorem fresh_prime_dvd_head_den {n p : ℕ} (hp : Nat.Prime p)
    (hlo : 4 * n < p) (hhi : p < 8 * n) (hclass : p % 8 = 1 ∨ p % 8 = 5) :
    p ∣ (bbpRationalHead n).den := by
  sorry

/-- Exact split; the residual retains the whole unselected rational head. -/
theorem bbp_split (n : ℕ) :
    bbpPrimeReservoir n + bbpResidual n = (16 : ℝ) ^ n * piPartial n := by
  simp [bbpResidual]

/-- Every open rectangle in the two-torus is visited arbitrarily late.
Confidence in truth: 70%, speculative arithmetic decoupling, untested.
This is stronger than support of the sum.  Separate uniform marginals do
not suffice: a rational telescoping control can lock the sum on a diagonal.
There is no conditioning on the exact residual, which could encode n. -/
@[blueprint (title := "Fresh BBP prime denominators have joint support with the residual")]
def PiPrimeReservoirSupport : Prop :=
  ∀ a c d e : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    0 ≤ d → d < e → e ≤ 1 → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧
      Int.fract (bbpPrimeReservoir n) ∈ Ioo a c ∧
      Int.fract (bbpResidual n) ∈ Ioo d e

/-- Frozen transfer, 99% confidence, not yet Lean-proved.
Choose a rectangle whose sum modulo one lies strictly inside the desired
cylinder.  Hit it at n large enough that the BBP tail O(n^-2) is smaller
than the boundary margin.  The exact split then gives a genuine π hit. -/
theorem pi_disjunctive_of_primeReservoirSupport (hπ : PiBBP)
    (h : PiPrimeReservoirSupport) : IsDisjunctive 16 Real.pi := by
  sorry

/-- The fresh-prime convention is tested on hand-checkable known answers. -/
example : 5 ∣ (bbpRationalHead 1).den := by decide +kernel
example : 13 ∣ (bbpRationalHead 2).den := by decide +kernel
example : 17 ∣ (bbpRationalHead 3).den := by decide +kernel

end NormalNumbers.PiDisjunctiveRoutes
