# HANDOFF 2026-10-11: `CoefmassTSWDirect` (TSW from prime Siegel–Walfisz)

Branch `wip/tsw-direct`.  Attended owner: Opus (NN coefmass lane).  Referee: Astra.

## Goal

Make `src/NormalNumbers/CoefmassTSWDirect.lean` sorry-free, leaving `Literature.PrimeCharacterSW`
as the only analytic input.  Paper proof: `docs/notes/tsw-y-uniformity-2026-10-11.md`, section
"Primary route", refereed both ways.  Each sorried theorem's docstring is its English proof.

## Frozen: do not change

- Every statement in `CoefmassTSWDirect.lean`: the defs `PrimeCharacterSW`, `smoothCount`,
  `LargestPrimeTransfer`, `SmoothCountRankin`, `UniformZTSW`, and the signatures of all theorems.
  The defs are under the referee's statement review.  Add helper lemmas freely; never weaken a
  statement.  If a statement looks false, stop and write `knowledge/outbox`-style evidence in this
  file instead of editing it.
- `twistedSiegelWalfisz` and `TwistedSiegelWalfisz` in `CPrimeSiteFactorization.lean`.
- No new `axiom`.  No `native_decide`.  No new `maxHeartbeats` above 400000 without a comment.

## Order of work (easiest first)

1. **`largestPrimeTransfer`** (elementary; no analysis beyond `Σ_{m≤X} 1/m ≤ 1 + log X`).
   Suggested decomposition:
   - a partition lemma: `Icc 1 X` = smooth ∪ repeated-top-prime ∪ simple-top-prime, using
     `Nat.primeFactors`/`Finset.max'` for `P⁺(n)`;
   - a bijection, `{n : simple top prime > W}` ≃ `{(m, p) : p prime, max W P⁺(m) < p, m p ≤ X}`;
   - the squareful count, `#{n ≤ X : ∃ p > W, p² ∣ n} ≤ X/(W−1)`, by a union bound and
     `Σ_{p>W} p⁻² ≤ Σ_{k>W} 1/(k(k−1)) = 1/W`;
   - the harmonic bound (Mathlib: `harmonic_le_one_add_log`).
2. **`smoothCount_rankin`** (Rankin).  Mertens upper bound:
   `Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le` (dependency `lean-proofs-latest`).
3. **`uniformZTSW_of_primeSW`** (assembly).  Character expansion of `1_{p ≡ a (q₀)}`: look for
   Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq` / orthogonality.  `χψ` is nonprincipal
   mod `r q₀` (CRT; `ZMod.chineseRemainder`).  The interval bound is the difference of two
   `PrimeCharacterSW` evaluations.

## Done when

`lean-treadmill --done-when sorry-free:src/NormalNumbers/CoefmassTSWDirect.lean`, and
`#print axioms twistedSiegelWalfisz_of_primeSW` shows only `propext, Classical.choice, Quot.sound`.
When a sorry closes, remove its waiver in `BarrierAudit.lean`: the audit fails the build
otherwise.
