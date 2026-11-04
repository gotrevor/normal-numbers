# KICKOFF 2026-11-03: an explicit sparse prime set with a base-4-normal Lambert constant

**This kickoff supersedes `DIRECTION.md` and every older `HANDOFF-*.md` on this branch**
(`wip/explicit-cprime`, worktree `~/src/nn-explicit-cprime`, based on `wip/g5-prime-subset` @
0e94e820).  Operator: Ren (Claude), attended session 2026-11-03/04.  Lane: new mathematics.

## The target

File: `src/NormalNumbers/ExplicitSparseNormal.lean` (planted, builds green with two `sorry`s).

    def loglogScale (p : ℕ) : ℕ := Nat.log 2 (Nat.log 2 p)
    def explicitSparseSet (p : ℕ) : Prop :=
      1 ≤ loglogScale p ∧ Nat.log 2 p * loglogScale p < 2 ^ loglogScale p * (loglogScale p + 1)

    theorem divergentRecip_explicitSparseSet : DivergentRecip explicitSparseSet
    theorem sqrtFreshMassZero_explicitSparseSet : SqrtFreshMassZero explicitSparseSet
    theorem isNormal_explicitSparseLambert : IsNormal 4 (subsetLambert explicitSparseSet 4)

The headline is already proved from the two leaves through Theorem C′
(`FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero`).  All three statements are FROZEN:
never weaken, restate or re-hypothesise.  Host gate:
`--done-when sorry-free:src/NormalNumbers/ExplicitSparseNormal.lean`.  The file is NOT imported from
the root `src/NormalNumbers.lean` yet (the root runs `#barrier_audit`, which fails on an untagged
open sorry).  **Add the import to the root only once the file is sorry-free**, then full `lake build`.

## Why this is the right target

`exists_sparse_normal_unconditional` (PrimeModelKMT.lean) is an existential: *some* prime set with
divergent reciprocal sum has a normal Lambert constant, the set living inside a `Good₂`/`BlockData`
structure.  This file replaces "some set" by a one-line decidable definition: the primes whose binary
length `⌊log₂ p⌋` lies in the first `1/k`-fraction (log scale) of its dyadic block, `k = ⌊log₂ ⌊log₂ p⌋⌋`.
The result is an **explicit, elementary, unconditional normal number built from primes**:
`Σ_{p ∈ P} 1/(4^p − 1)` is normal in base 4.  Only full-prime-set Mertens asymptotics are needed:
no primes-in-progressions input of any kind.

## The proof (execute; commit after each green lemma)

Read first: the module docstring of `ExplicitSparseNormal.lean`, then
`PrimeModelSqrtFresh.lean` (`SqrtFreshMassZero`, `recipSumIoc`, its monotonicity/splitting lemmas),
`G4WiringSparse.lean` (`DivergentRecip`, `recipSumIoc`), `G4Mertens.lean`,
`G4MertensAP.lean`, `TwoPointMertensLower.lean`, `G4Base2Mertens.lean` (`mertens_window`), and the
PNT+ package (`PrimeNumberTheoremAnd/Consequences.lean`: `pi_asymp`, `chebyshev_asymptotic`,
`chebyshev_asymptotic_finsum`; `BrunTitchmarsh.lean`).

0. **Mertens with vanishing error.**  Establish, in whatever form is most convenient,
   `Σ_{x < p ≤ y} 1/p = log(log y / log x) + o(1)` as `x → ∞`, uniformly in `y ≥ x`; equivalently
   `Σ_{p ≤ x} 1/p − log log x` converges.  Sources, in order of preference: (i) an existing repo
   lemma (grep `mertens`, `sum_inv_prime`, `log_log`); (ii) PNT+ `pi_asymp` (`π(x) ~ x/log x`) plus
   Abel/partial summation; (iii) `chebyshev_asymptotic` (`θ(x) ~ x`) plus partial summation.
   If none closes within the lap, plant `Literature.MertensSecond : Prop` with the exact statement
   `∃ M : ℝ, Tendsto (fun x => Σ_{p ≤ x} 1/p − log log x) atTop (𝓝 M)` (Mertens 1874; Tenenbaum,
   *Introduction to analytic and probabilistic number theory*, Thm I.1.10), prove the leaves from it,
   and say so prominently in the handoff.  Prefer (i)/(ii)/(iii): the headline should be unconditional.
1. **Block structure.**  For `k ≥ 1` let `B_k = {p : loglogScale p = k}` = primes with
   `2^{2^k} ≤ p < 2^{2^{k+1}}`, and `P ∩ B_k` = those with `⌊log₂ p⌋ < 2^k (k+1)/k`, i.e.
   `2^{2^k} ≤ p < 2^{⌈2^k(k+1)/k⌉}` (be careful with the integer rounding; prove the exact interval
   form of `explicitSparseSet` as a lemma).
2. **Divergence.**  By step 0 the mass of `P ∩ B_k` is `log(⌈2^k(k+1)/k⌉ / 2^k) + o(1) ≥ 1/(2k)`
   for `k ≥ k₀`; sum over `k` (harmonic divergence; `Real.tendsto_sum_range_one_div_nat_succ_atTop`
   or `Real.not_summable_natCast_inv`).  Translate to `¬ Summable` of the indicator-weighted
   `1/p` sequence: if it were summable, the partial sums over the blocks would be bounded.
3. **Fresh mass.**  Primes in `(Nat.sqrt N, N]` have `⌊log₂ p⌋ ∈ [⌊log₂ N⌋/2 − 1, ⌊log₂ N⌋]`, so they
   meet at most two blocks `B_k`, `B_{k+1}` with `k ≥ loglogScale N − 2`.  Within each, `P` occupies
   `⌊log₂ p⌋ < 2^k(1 + 1/k)`, so the `P`-mass in `(√N, N]` is at most the mass of primes in two
   windows of log-ratio `≤ 1 + 1/k` plus the `o(1)` of step 0: `≤ 2 log(1 + 1/k) + o(1) → 0`.
   Use `recipSumIoc` monotonicity in the endpoints (lemmas in `PrimeModelSqrtFresh.lean`).

If step 0 turns out to need PNT+ machinery that does not fit a lap, plant the `Literature` Prop
(step 0's fallback) and finish the leaves conditionally; do not leave the leaves open.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment.
- Do not edit statements in other files; new helper lemmas go in this file or a new
  `ExplicitSparseNormalAux.lean`.
- Handoff: `HANDOFF-2026-11-03-explicit-sparse-normal.md` with
  `#print axioms isNormal_explicitSparseLambert` recorded (expect only `propext`,
  `Classical.choice`, `Quot.sound`; if a `Literature` Prop was planted, say which theorem carries it).
- Lines ≤ 100 chars; docstrings on every new theorem.
