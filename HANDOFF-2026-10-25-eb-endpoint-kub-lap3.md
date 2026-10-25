# HANDOFF: EB endpoint Kubilius route, lap 3

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate remains
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any frozen statement in the target file, and keep
`KubiliusTV` exactly as the named hypothesis: never prove, weaken, or axiomatize it.

## Concrete advance

The finite joint-independence/product layer is now complete. In
`CoefmassErdosBorweinEndpointKubAux.lean`:

- `bernoulliSubsetExpectation_mul_inter_disjoint` proves that arbitrary observables on two
  disjoint coordinate blocks factor;
- `bernoulliSubsetMass_two_cylinders` turns this into exact product mass for two cylinder events;
- `bernoulliSubsetMass_cylinders` proves exact finite joint independence for a pairwise-disjoint
  family of coordinate blocks;
- `bernoulliSubsetMass_cylinders_le_pow` and
  `bernoulliSubsetMass_cylinder_complements_le_pow` package common per-block upper/lower bounds;
- `bernoulliSubsetMass_all_blockCenteredSum_lt_sqrt_eighth_le` combines joint independence with
  the existing one-block fourth-moment estimate: if every pairwise-disjoint block has variance at
  least one, the mass on which all centered increments miss `sqrt(V)/8` is at most
  `(63/64)^I.card`.

The target module specializes the last theorem as
`kubiliusMass_all_blockCenteredSum_lt_sqrt_eighth_le`. This discharges item 1 from the previous
handoff: the exact fixed-`K` failure bound required by the operator plan is available directly in
the Kubilius model.

No pre-existing statement in `CoefmassErdosBorweinEndpointKub.lean` was changed. In particular,
the signatures of `KubiliusTV`, `divisorVariance_diverges_at_ln2_of_kubilius`, and
`ebPowerCandidateNormal_of_kubilius` remain as planted. No axiom, `native_decide`, or new
hypothesis was added.

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
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetExpectation_mul_inter_disjoint \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_two_cylinders \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_cylinders \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_cylinder_complements_le_pow \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_all_blockCenteredSum_lt_sqrt_eighth_le \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_all_blockCenteredSum_lt_sqrt_eighth_le
```

Verdict: `FORMALIZE-TIER GREEN`. Every audited theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`.

## Current blocker

The sole scoped sorry remains `divisorVariance_diverges_at_ln2_of_kubilius`. The probabilistic
fixed-block amplification is no longer a blocker. The remaining load-bearing pieces are:

1. use `RS_prime.mertens_second_theorem'` to prove lower bounds for each geometric block variance
   and upper bounds for prefix/cardinality variance, including the real/natural cutoff and floor
   comparisons;
2. choose fixed `K`, then `M`, then a sufficiently large ratio `r`, and show the block increment
   from the new `(63/64)^K` theorem dominates both the Chebyshev-controlled start deficit and the
   logarithmic walk cap;
3. package the deterministic no-crossing event, the shift from `[1,N]` to `[1,N+a0]`, the
   `KubiliusTV` error tending to zero, and the final epsilon assembly.

## Next highest-value attack

Formalize the Mertens-to-block-variance bridge first. Define a prime block by inequalities in
`log (log p)` (or an equivalent natural cutoff whose membership rewrites cleanly), and prove that
its sum of `(1/p)(1-1/p)` is eventually bounded below by a fixed positive multiple of the block's
`log log` length. Also prove the corresponding prefix upper bound needed by Chebyshev. This is now
the shortest route to instantiating `kubiliusMass_all_blockCenteredSum_lt_sqrt_eighth_le` inside
the Step 2 event.
