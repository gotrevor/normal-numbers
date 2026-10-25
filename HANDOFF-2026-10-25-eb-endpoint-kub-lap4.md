# HANDOFF: EB endpoint Kubilius route, lap 4

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate remains
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any frozen statement in the target file, and keep
`KubiliusTV` exactly as the named hypothesis: never prove, weaken, or axiomatize it.

## Concrete advance

The Mertens-to-finite-block bridge requested by lap 3 is now proved. In
`CoefmassErdosBorweinEndpointKub.lean`:

- `primesUpTo_eq_filter_Iic` identifies the model's natural cutoff with the cutoff used by
  `RS_prime.mertens_second_theorem'`;
- `mertens_primeReciprocalSum_bound` specializes Mertens to `primesUpTo y`;
- `primeReciprocalSum_block_eq_sub` expresses the reciprocal-prime mass on `(a,b]` as the
  difference of prefix masses;
- `mertens_primeReciprocalSum_block_lower` gives the block lower bound
  `log log b - log log a - 2C`;
- `mertens_primeVariance_block_lower` converts that to the Bernoulli variance lower bound with
  factor `1/2`, using `p >= 2`;
- `mertens_primeVariance_prefix_upper` gives the prefix variance upper bound `log log y + C`.

The finite model is also connected to the events needed later in Step 2:

- `bernoulliCenteredSum_eq_card_inter_sub_sum` identifies a centered membership sum with selected
  cardinality minus its reciprocal-prime mean;
- `kubiliusMass_blockCenteredSum_abs_ge_le` is Chebyshev for any coordinate block inside the full
  Kubilius universe;
- `kubiliusMass_card_deviation_ge_le` packages the resulting selected-cardinality deviation bound.

Together with lap 3's fixed-block failure estimate, both probabilistic inputs from the operator
plan are now available: `(63/64)^K` for missed positive block increments and a variance-over-square
bound for an abnormally negative block start or an oversized selected-prime count.

No pre-existing statement in `CoefmassErdosBorweinEndpointKub.lean` was changed. In particular,
the signatures of `KubiliusTV`, `divisorVariance_diverges_at_ln2_of_kubilius`, and
`ebPowerCandidateNormal_of_kubilius` remain as planted. No axiom, `native_decide`, or new hypothesis
was added.

## Verification

Narrow build:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKubAux \
  NormalNumbers.CoefmassErdosBorweinEndpointKub
```

Completed successfully. The target file still has exactly one proof-debt warning, at
`divisorVariance_diverges_at_ln2_of_kubilius`.

Formal gate and axiom audit:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --import NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliCenteredSum_eq_card_inter_sub_sum \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.mertens_primeReciprocalSum_bound \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.primeReciprocalSum_block_eq_sub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.mertens_primeReciprocalSum_block_lower \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.mertens_primeVariance_block_lower \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.mertens_primeVariance_prefix_upper \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_blockCenteredSum_abs_ge_le \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_card_deviation_ge_le
```

Verdict: `FORMALIZE-TIER GREEN`. Every audited theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`.

## Current blocker

The sole scoped sorry remains `divisorVariance_diverges_at_ln2_of_kubilius`. The analytic
prime-sum estimates and finite-probability inequalities needed by the model crossing argument are
now closed. The remaining load-bearing work is their asymptotic/deterministic assembly:

1. choose natural cutoff endpoints representing fixed geometric blocks in `u = log log p`, and
   prove the floor/log comparisons, nesting, disjointness, containment below the Kubilius cutoff,
   and variance-at-least-one hypotheses;
2. instantiate the fixed-`K` failure bound and Chebyshev start/cardinality bounds so the model
   no-crossing event has mass at most `(63/64)^K + K/M^2 + o(1)`;
3. formalize the deterministic prime-jump no-crossing event, the shift from `[1,N]` to
   `[1,N+a0]`, the `KubiliusTV` error tending to zero, and the final epsilon assembly.

## Next highest-value attack

Define the natural block cutoff schedule and prove its eventual interface in one package: for fixed
`K`, `M`, and sufficiently large ratio `r`, produce pairwise-disjoint blocks `(a_i,b_i]` below
`floor (exp ((log N)^(1-eta)))`, prove each variance is at least one via
`mertens_primeVariance_block_lower`, and prove the start-prefix variance is `O(u_i)` via
`mertens_primeVariance_prefix_upper`. This is the shortest remaining route to an actual invocation
of `kubiliusMass_all_blockCenteredSum_lt_sqrt_eighth_le` in the Step 2 proof.
