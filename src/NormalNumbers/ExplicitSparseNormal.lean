/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.PrimeModelFamilyGraded
import NormalNumbers.PrimeModelKMT

/-!
# An explicit sparse prime set whose Lambert constant is normal in base 4

`exists_sparse_normal_unconditional` proves that *some* prime set `S` with `Σ_{p∈S} 1/p = ∞` has a
base-4-normal Lambert constant `Σ_{p∈S} 1/(4^p − 1)`, through Theorem C′
(`isNormal_subsetLambert_of_sqrtFreshMassZero`): divergent reciprocal mass plus vanishing
`√N`-fresh mass `Σ_{√N<p≤N, p∈S} 1/p → 0`.  This file names an explicit, decidable set that
satisfies both, using only the full-prime-set Mertens asymptotics (no primes-in-progressions input).

## The set

Let `k = k(p) := ⌊log₂ ⌊log₂ p⌋⌋` (`loglogScale`).  Then `p ∈ P` iff `k ≥ 1` and
`⌊log₂ p⌋ · k < 2^k · (k + 1)`, i.e. `⌊log₂ p⌋ ∈ [2^k, 2^k(1 + 1/k))`: the binary length of `p`
lies in the first `1/k`-fraction (in log scale) of its dyadic block of lengths.  Equivalently
`P = ⋃_k {p prime : 2^{2^k} ≤ p < 2^{2^k(1+1/k)}}` up to the integer rounding of `⌊log₂ p⌋`.

## Mechanism (paper, 2026-11-03, Ren)

With `L(p) = log p`, the block `k` is `log₂ L ∈ [k, k + log₂(1 + 1/k))`, of log-log width
`≍ 1/k`.  Mertens' second theorem with error term, `Σ_{x<p≤y} 1/p = log(log y/log x) + O(1/log x)`
(from PNT+: `pi_asymp` / `chebyshev_asymptotic` by partial summation, or an explicit Mertens if the
repo already has one), gives:

* **Divergence.**  Block `k` carries mass `log(1 + 1/k) + O(e^{−2^k}) ≥ 1/(2k)` for `k` large, and
  `Σ_k 1/(2k) = ∞`.
* **Fresh mass.**  The primes in `(√N, N]` have `log₂ p ∈ (log₂ N − 1, log₂ N]`, a window of
  log-width `1` that meets at most two blocks; `P ∩ (√N, N]` sits inside the `1/k`-initial segments,
  so its mass is `≤ 2 log(1 + 1/k) + O(1/log N) → 0`, with `k ≍ log log N`.

Both are elementary once the Mertens asymptotic is in hand.  Note the schedule's `√N` cutoff is
`Nat.sqrt N` in `SqrtFreshMassZero`.

## Status

Frozen: `isNormal_explicitSparseLambert` (the headline, proved from the two lemmas below).
`divergentRecip_explicitSparseSet` and `sqrtFreshMassZero_explicitSparseSet` are the two leaves
(sorry, confidence 95% each).  Do not restate them.  If the repo lacks a usable Mertens-with-error
statement and PNT+ cannot supply it within a lap, plant `Literature.MertensSecond` as a named
hypothesis `Prop` with the exact cited statement (Tenenbaum, *Introduction to analytic and
probabilistic number theory*, Thm I.1.10) and prove the leaves from it; say so in the handoff.
-/

namespace NormalNumbers.PrimeModel.Explicit

open NormalNumbers.PrimeLambert NormalNumbers.PrimeModel.SqrtFresh NormalNumbers.G4Sparse

/-- `k(p) = ⌊log₂ ⌊log₂ p⌋⌋`, the dyadic scale of the binary length of `p`. -/
def loglogScale (p : ℕ) : ℕ := Nat.log 2 (Nat.log 2 p)

/-- The explicit sparse prime set: `⌊log₂ p⌋` lies in the first `1/k`-fraction of its dyadic
block, `k = loglogScale p ≥ 1`.  (Primality is imposed by the consumers, as in `DivergentRecip`.) -/
def explicitSparseSet (p : ℕ) : Prop :=
  1 ≤ loglogScale p ∧ Nat.log 2 p * loglogScale p < 2 ^ loglogScale p * (loglogScale p + 1)

instance : DecidablePred explicitSparseSet := fun p => by
  unfold explicitSparseSet
  infer_instance

/-- Teeth: `17` has `⌊log₂ 17⌋ = 4`, `k = 2`, `4·2 < 4·3`; `67` has `⌊log₂ 67⌋ = 6`, `k = 2`,
`6·2 = 12 ≮ 12`; `1031` has `⌊log₂⌋ = 10`, `k = 3`, `30 < 32`; `2053` has `11`, `k = 3`, `33 ≮ 32`. -/
example : explicitSparseSet 17 := by decide +kernel
example : ¬ explicitSparseSet 67 := by decide +kernel
example : explicitSparseSet 1031 := by decide +kernel
example : ¬ explicitSparseSet 2053 := by decide +kernel

/-- **Leaf 1 (frozen).**  Divergent reciprocal mass: block `k` carries mass `≍ 1/k`. -/
theorem divergentRecip_explicitSparseSet : DivergentRecip explicitSparseSet := by
  sorry

/-- **Leaf 2 (frozen).**  Vanishing `√N`-fresh mass: the window `(√N, N]` meets `P` in a set of
log-log width `O(1/log log N)`. -/
theorem sqrtFreshMassZero_explicitSparseSet : SqrtFreshMassZero explicitSparseSet := by
  sorry

/-- **Headline (frozen, 2026-11-03).**  The explicit prime Lambert constant
`Σ_{p prime, p ∈ P} 1/(4^p − 1)` is normal in base 4, unconditionally via Theorem C′. -/
@[blueprint (title := "An explicit sparse prime Lambert constant is normal in base 4")]
theorem isNormal_explicitSparseLambert : IsNormal 4 (subsetLambert explicitSparseSet 4) :=
  FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero explicitSparseSet
    sqrtFreshMassZero_explicitSparseSet divergentRecip_explicitSparseSet

end NormalNumbers.PrimeModel.Explicit
