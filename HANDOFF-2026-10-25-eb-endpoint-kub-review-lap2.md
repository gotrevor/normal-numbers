# HANDOFF: EB endpoint Kubilius route, review lap 2

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate remains
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any frozen statement in the target file, and keep
`KubiliusTV` exactly as the named hypothesis: never prove, weaken, or axiomatize it.

## Adversarial review verdict

The route still reaches the headline. A word diff from planting commit `e2d05168` confirms that
`KubiliusTV`, `divisorVariance_diverges_at_ln2_of_kubilius`, and
`ebPowerCandidateNormal_of_kubilius` retain their planted signatures. The assembly theorem is
already proved and depends on the single open Step 2 theorem through
`ebRandom_ae_normal_of_divisorVariance_diverges`; there is no second hidden target-file debt.

The fixed-`K` independent-block route remains sound, but the plan's former claim
`P(Delta >= sigma/2) >= q` did not follow from mean/variance/fourth-moment control alone. This lap
proved the sufficient replacement
`P(Delta >= sigma/8) >= 1/64` and updated `EB-ENDPOINT-KUB-NEXT.md`. The constant order is unchanged:
choose `K`, then `M`, then enlarge `r` by a fixed numerical factor so the `sigma/8` gain dominates
the start deficit and the logarithmic cap.

The repository-wide `DIRECTION.md`, `STATUS.md`, and `PENDING_WORK.md` predate this private endpoint
branch and contain no competing Kubilius directive. The branch-local plan and newest handoff are
therefore the live campaign record.

## Concrete advance

`CoefmassErdosBorweinEndpointKubAux.lean` now contains the full finite moment/crossing layer:

- `bernoulliSubsetExpectation_insert` and `..._insert_of_invariant` split off one coordinate;
- `bernoulliSubsetExpectation_inter` and `bernoulliSubsetMass_inter` prove marginalization of
  cylinder observables/events to a coordinate block;
- `bernoulliSubset_centeredSum_expectation` and `..._secondMoment` prove exact mean zero and
  variance `sum q(p)(1-q(p))`;
- `bernoulliSubset_centeredSum_fourthMoment_le` proves
  `E X^4 <= 3 (sum q(1-q))^2 + sum q(1-q)` by the exact one-coordinate fourth-moment recurrence;
- `bernoulliSubsetMass_centeredSum_abs_ge_le` is the direct Chebyshev event bound;
- `finite_centered_fourth_upperTail` proves the one-sided finite-law estimate from two weighted
  Cauchy--Schwarz inequalities, with no measure-space encoding;
- `bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth` packages the result inside any larger
  Bernoulli universe: if a block variance is at least one, its centered increment is at least
  `sqrt(V)/8` with mass at least `1/64`.

The target module specializes the last result as
`kubiliusMass_blockCenteredSum_ge_sqrt_eighth` for prime blocks with parameters `q(p)=1/p`.
No pre-existing statement was changed. No axiom, `native_decide`, or new hypothesis was added.

## Verification

Narrow builds:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKubAux
lake build NormalNumbers.CoefmassErdosBorweinEndpointKubAux \
  NormalNumbers.CoefmassErdosBorweinEndpointKub
```

Both completed successfully. The target file still has exactly one proof-debt warning, at
`divisorVariance_diverges_at_ln2_of_kubilius`.

Formal gate and axiom audit:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --import NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubset_centeredSum_secondMoment \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubset_centeredSum_fourthMoment_le \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.finite_centered_fourth_upperTail \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_blockCenteredSum_ge_sqrt_eighth
```

Verdict: `FORMALIZE-TIER GREEN`. Every audited theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`.

The commit hook's repository-wide `lake build` also completed successfully (`10847 jobs`).

## Current blocker

The only scoped sorry is still `divisorVariance_diverges_at_ln2_of_kubilius`. Its model-side
one-block crossing estimate is now closed. The remaining load-bearing pieces are:

1. turn disjoint block coordinates into the fixed-`K` product bound `(63/64)^K` (the marginal
   cylinder law is proved, but the joint cylinder-event independence packaging is not);
2. use Mertens to bound each geometric block variance below and the prefix/cardinality variances
   above, with the necessary cutoff/floor comparisons;
3. package the deterministic no-crossing event, the shift from `[1,N]` to `[1,N+a0]`, the
   `KubiliusTV` error tending to zero, and the final epsilon assembly.

## Next highest-value attack

Prove finite joint independence for pairwise-disjoint block cylinder events and derive the exact
fixed-`K` failure bound from `bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth`. This is the
shortest remaining bridge from the landed one-block estimate to the model event `A_N`. Then prove
the Mertens block-variance lower bound and only afterward enter the large asymptotic Step 2 proof.
