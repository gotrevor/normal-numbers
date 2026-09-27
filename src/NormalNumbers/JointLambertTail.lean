/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.JointLambertPrimeSelection

set_option maxHeartbeats 1000000

/-!
# Joint Lambert: the shared binary tail majorant

Paper: `papers/2026-09-26-joint-lambert-disjunctivity.md`, §3 (divisor averaging) and the
tail-control step of §4.

`JointLambertPrimeSelection.exists_joint_prime_candidates` supplies a progression
`n_m = R + mA` whose divisor counts are prescribed at the slots `j < k` and a quantitative
supply of *candidate* indices `m` (those with `u + mB` prime, so that the survivor slot
really has `τ(n_m + r) = 2a`).  What is still missing is that the **unprescribed** slots
`j ≥ k` do not contribute: their divisor counts must be small enough that the binary tail

  `∑_{t} τ(n + k + t) / 2^(k+t)`

is below any prescribed `ε`.  That is the content of `exists_joint_small_tail` below, and
`joint_small_tail_base_majorant` then transfers the single binary bound to **every** base
`b ≥ 2` at once, which is why one common `n` serves all coordinates.

No new analytic input is admitted: `AGP` and `PrimeIntervalSupply` are exactly the two
`Prop`s of `JointLambertPrimeSelection`, passed as hypotheses, and everything else is
elementary (divisor pairing at `√`, counting along coprime progressions, harmonic sums,
geometric decay).
-/

namespace NormalNumbers.JointLambert

open Finset

/-- **The shared binary tail majorant** (target of this module).

Given the two analytic inputs, `c ≥ 2`, `a ≥ 2`, `r ≥ 1`, any `ε > 0` and any natural
cutoffs `K`, `N`, there is a *single* integer `n ≥ max(1, N)` and a height `k ≥ K` with
`r < k` such that

* every killed slot `j < k`, `j ≠ r` has `c^(j+1) ∣ τ(n + j)`;
* the survivor slot has exactly `τ(n + r) = 2a`;
* the whole binary tail from index `k` onwards is `< ε`.

`ε` is fixed *before* the prime-selection height, so the tail bound is genuinely uniform:
one `n`, every later base. -/
theorem exists_joint_small_tail (hagp : AGP) (hpis : PrimeIntervalSupply)
    {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) (K N : ℕ) :
    ∃ k n : ℕ, K ≤ k ∧ r < k ∧ 1 ≤ n ∧ N ≤ n ∧
      (∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ NormalNumbers.SwingC2.tau (n + j)) ∧
      NormalNumbers.SwingC2.tau (n + r) = 2 * a ∧
      ∑' t : ℕ, (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) < ε := by
  sorry

end NormalNumbers.JointLambert
