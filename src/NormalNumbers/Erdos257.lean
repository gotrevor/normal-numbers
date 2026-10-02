/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetAssembly
import NormalNumbers.DisjunctiveCorollaries
import NormalNumbers.PrimeModelFamilyGraded

/-!
# Erdős #257 for `A = k·S` (campaign launched 2026-10-02)

Erdős #257 (erdosproblems.com/257; formal-conjectures `Erdos257.erdos_257`, open): for infinite
`A ⊆ ℕ`, is `Σ_{n∈A} 1/(2ⁿ − 1)` irrational?  Source of this lane:
`docs/OPEN-PROBLEMS-SWEEP-2026-10-02.md`, rank 1 (Tao–Teräväinen arXiv:2512.01739 settle primes
and call other prime-like sets "likely"; no checked source lists a dilated prime set).

**The identity.**  `ω_S(n) = #{p ∣ n prime : S p}`, so
`subsetLambert S b = Σ_n ω_S(n)/bⁿ = Σ_{p∈S} Σ_{j≥1} b^{−pj} = Σ_{p∈S} 1/(bᵖ − 1)`.  At `b = 2ᵏ`
this is `Σ_{n∈k·S} 1/(2ⁿ − 1)`, and `n ↦ k·n` is injective.  So:
* `isDisjunctive_subsetLambert` (any `S` with a Mertens rate, base `≥ 3`) gives disjunctivity,
  hence irrationality, for every `k ≥ 2`;
* C′ (`isNormal_subsetLambert_of_sqrtFreshMassZero`, base 4) gives normality in base 2 at `k = 2`
  (base change `4 = 2²`).

## Frozen statements (do not edit; prove them)

* `kMulPrimes_infinite`, `erdos257_kMul`, `erdos257_kMul_primes`, `erdos257_kMul_residueClass`,
  `erdos257_twoMul_normal`.

## Guard rule

**Content locator.**  `k = 1`, `S` = all primes is Tao–Teräväinen's theorem, which base 2 puts out
of reach of the fixed-base machinery (`3 ≤ b` fails); the dilation `k ≥ 2` is exactly what moves
the constant into base `2ᵏ ≥ 4`.  **Degenerate cases.**  A finite `S` gives a finite `A`, excluded
from #257 and by the Mertens rate (which forces divergence); `k = 0` collapses `A` to `{0}`; `k = 1`
is the open base-2 case, not claimed.
-/

namespace NormalNumbers.Erdos257

open Filter

/-- `k·S = {k·p : p prime, S p}`. -/
def kMulPrimes (S : ℕ → Prop) (k : ℕ) : Set ℕ := {n | ∃ p, p.Prime ∧ S p ∧ n = k * p}

variable {S : ℕ → Prop} [DecidablePred S]

/-- A set with a Mertens rate has infinitely many primes, so `k·S` is infinite for `k ≥ 1`. -/
theorem kMulPrimes_infinite {c C : ℝ} (hm : G4.MertensAP.MertensRate S c C) {k : ℕ}
    (hk : 1 ≤ k) : (kMulPrimes S k).Infinite := by
  sorry

/-- **Erdős #257 for `A = k·S`, `k ≥ 2`.**  Any prime set with a Mertens rate. -/
theorem erdos257_kMul {c C : ℝ} (hm : G4.MertensAP.MertensRate S c C) {k : ℕ} (hk : 2 ≤ k) :
    Irrational (∑' n : kMulPrimes S k, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry

/-- All primes: `Σ_p 1/(2^{kp} − 1)` is irrational for every `k ≥ 2`. -/
theorem erdos257_kMul_primes {k : ℕ} (hk : 2 ≤ k) :
    Irrational (∑' n : kMulPrimes (fun _ => True) k, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry

/-- Primes in a residue class: `Σ_{p ≡ a (q)} 1/(2^{kp} − 1)` is irrational for `k ≥ 2`. -/
theorem erdos257_kMul_residueClass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {k : ℕ}
    (hk : 2 ≤ k) :
    Irrational (∑' n : kMulPrimes (fun p => (p : ZMod q) = a) k, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry

/-- **Normality at `k = 2`.**  For a C′ set (vanishing square-root fresh mass, divergent
reciprocal sum), `Σ_{n∈2·P} 1/(2ⁿ − 1)` is normal in base 2. -/
theorem erdos257_twoMul_normal (hS : PrimeModel.SqrtFresh.SqrtFreshMassZero S)
    (hP : G4Sparse.DivergentRecip S) :
    IsNormal 2 (∑' n : kMulPrimes S 2, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry

end NormalNumbers.Erdos257
