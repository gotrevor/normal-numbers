# Vandehey Theorem 5.1 lap 18: Proposition 4.1 and Theorem 5.1 proved

## Concrete advance

- Completed Vandehey's Proposition 4.1 as
  `VandeheyKorobov.norm_power_sum_le_step`.  The proof now contains the rounded-modulus
  natural wrapper, equations (12)--(13), the exact two squared monomials, square-root
  extraction, and both trivial branches surrounding the nontrivial rounded-divisor branch.
- The adversarial review corrected the route at the decisive normalization: the needed bound is
  `mbar ≤ M(P) * τ`, obtained by applying Lemma 2.1 to `mbar` and using Claim 4.4's order
  identity.  Claim 4.6's different bound `mbar ≤ M(P) * m'` is not substituted there.
- Proved the recursive invariants used by Theorem 5.1: `0 < alpha k < 1`, the alpha and log-factor
  successor identities, `0 ≤ gamma k ≤ 1`, `1 ≤ nu k ≤ 2`, `nu k ≤ 1 + gamma k`, and
  `1 ≤ B_k`.  The last invariant justifies dropping the paper's redundant `max {sqrt D, 1}`.
- Replaced the sole `sorry` in `VandeheyProof.lean` by induction on `k`.  The induction handles
  zero-length reduced sums and modulus `1` explicitly, reindexes all other divisor bounds, and
  instantiates Proposition 4.1 with the frozen `alpha`/`expPair`/`constPair` recursion.
- Removed the discharged `BarrierAudit` waiver.  The frozen definition of `VandeheyThm51` and
  all three unconditional corollary statements remain unchanged.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovStep.lean`: passed.
- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyProof.lean`: passed.
- `lake build +NormalNumbers.VandeheyKorobovStep:olean`: passed (8888 jobs).
- `lake build +NormalNumbers.VandeheyProof:olean`: passed (8936 jobs).
- `lake build +NormalNumbers.BarrierAudit:olean`: passed (10377 jobs); audit reports 34 barriers,
  25 linked cruxes, 77 waivers, and no stale Vandehey waiver.
- `lean-green --target NormalNumbers.VandeheyProof --axioms ...`: passed separately for all four
  declarations in `VandeheyProof.lean`; each prints exactly
  `[Classical.choice, Quot.sound, propext]` and ends `FORMALIZE-TIER GREEN`.
- `lean-green /Users/gotrevor/src/nn-vandehey`: full default build passed (10868 jobs), final
  verdict `FORMALIZE-TIER GREEN`.
- `rg` finds no `sorry`, `admit`, or axiom declaration in `VandeheyProof.lean` or the step module.
- `git diff 0807f767 -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean`: empty.

## Current blocker

None.  The host predicate `sorry-free:src/NormalNumbers/VandeheyProof.lean`, the kickoff's four
axiom checks, and the BarrierAudit obligation are all discharged.

## Next highest-value attack

No further in-scope attack: stop this campaign after the full default green gate and committed
checkpoint.  Any later strengthening is stretch work and must not delay host completion.

The pre-existing untracked `TestVand.lean` was left unchanged.
