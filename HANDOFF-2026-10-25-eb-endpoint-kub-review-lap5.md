# HANDOFF: EB endpoint Kubilius route, review lap 5

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate remains
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any frozen statement in the target file, and keep
`KubiliusTV` exactly as the named hypothesis: never prove, weaken, or axiomatize it.

## Review finding and concrete advance

A fresh audit reconstructed the route from the planted source and the FDEK deterministic bridge.
The frozen signatures of `KubiliusTV`, `divisorVariance_diverges_at_ln2_of_kubilius`, and
`ebPowerCandidateNormal_of_kubilius` are unchanged; the target still has exactly one `sorry`, in
`divisorVariance_diverges_at_ln2_of_kubilius`.

The review found a useful simplification of the planned crossing argument. Control the centered
reciprocal-prime prefix at a block start directly, rather than first converting it to the
`omega - log log` walk. Then the block endpoint identity spends the Mertens error only once, at the
endpoint. This removes a start-point Mertens loss and avoids floor/log bookkeeping at the start.
`EB-ENDPOINT-KUB-NEXT.md` now records this corrected formulation.

The complete finite crossing bridge is now proved:

- `bernoulliCenteredSum_union` makes centered sums additive across disjoint coordinate blocks.
- `primeFactors_filter_inter_primesUpTo`,
  `bernoulliCenteredSum_primesUpTo_primeFactors`, and
  `bernoulliCenteredSum_primesUpTo_eq_add_block` identify the Kubilius coordinates of an integer
  with the deterministic `omegaUpTo` prefixes and split a prefix at a block boundary.
- `kubiliusMass_union_le` and `kubiliusMass_exists_mem_le_sum` supply the finite union bound.
- `kubiliusBlockBadEvent` packages exactly three exceptional events: selected-prime cardinality
  above `2L`, every block missing its positive increment, or some centered start prefix at most
  `-R_i`.
- `kubiliusMass_blockBadEvent_le` proves
  `(63/64)^#I + Var(card)/D^2 + sum_i Var(prefix_i)/R_i^2` for that event, using the already-proved
  independent-block lower tail and Chebyshev bounds.
- `divisorVarianceMass_gt_of_kubilius_block_crossing` proves that one good block forces
  `T < divisorVarianceMass`. It invokes the existing deterministic prime-jump cap, rules out its
  early-equality branch from the strictly positive block increment, and contradicts its cap branch
  from the centered start, block increment, and a single endpoint Mertens bound.
- `primeFactorSet_mem_kubiliusBlockBadEvent_of_divisorVarianceMass_le` takes the contrapositive:
  every integer with divisor-variance mass at most `T` belongs to the fixed-block bad event.

No existing Lean statement was edited: the target diff consists of 358 insertions and zero
deletions. No axiom, `native_decide`, or additional hypothesis was introduced.

## Verification

The narrow build completed successfully:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKubAux \
  NormalNumbers.CoefmassErdosBorweinEndpointKub
```

The source census is still exactly one scoped proof debt:

```text
rg -n "\bsorry\b" \
  src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean \
  src/NormalNumbers/CoefmassErdosBorweinEndpointKubAux.lean
```

It reports only line 637 of the target, the body of
`divisorVariance_diverges_at_ln2_of_kubilius`. `git diff --check` is clean.

The real formal gate was run as:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --import NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliCenteredSum_union \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.primeFactors_filter_inter_primesUpTo \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliCenteredSum_primesUpTo_primeFactors \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliCenteredSum_primesUpTo_eq_add_block \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_union_le \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_exists_mem_le_sum \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_blockBadEvent_le \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.divisorVarianceMass_gt_of_kubilius_block_crossing \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.primeFactorSet_mem_kubiliusBlockBadEvent_of_divisorVarianceMass_le
```

Verdict: `FORMALIZE-TIER GREEN`. Every audited declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Current blocker

The finite probabilistic and deterministic logic is closed. The sole scoped `sorry` now reduces to
constructing an eventual natural-cutoff schedule and carrying its explicit error bound through
`KubiliusTV`:

1. choose fixed `K`, start-tail multiplier `M`, and then a sufficiently large geometric ratio `r`;
2. for large sample size, define natural endpoints representing consecutive intervals
   `[u_i,r*u_i]` in `u = log log p`, starting at `u_0 = (log L)^3`;
3. prove endpoint order, pairwise block disjointness, containment below the Kubilius cutoff,
   `P <= a_i`, block variance at least one, the crossing dominance inequality, and the three error
   terms tending to their desired bounds;
4. transfer the bad event with `KubiliusTV`, use `card_filter_Icc_add_le` for the fixed shift, and
   finish the epsilon/Tendsto assembly.

The difficult part is now analytic floor/log control, not the crossing event or its probability.

## Next highest-value attack

Formalize one eventual schedule-interface lemma, rather than unfolding the cutoffs throughout the
final theorem. A clean concrete choice is `M_sample = N + a0`, `L = log log M_sample`,
`y = floor(exp(sqrt(log M_sample)))`, `D = L/2`, `u_0 = (log L)^3`,
`u_i = r^i*u_0`, and endpoints near `floor(exp(exp u_i))`. For fixed `K,M,r`, the last block is
eventually below `(1/2)L`, while `u_0` is eventually above the `collisionCutoff N` scale; Mertens
then supplies the variance and mean bounds. Package precisely the hypotheses consumed by
`kubiliusMass_blockBadEvent_le` and
`primeFactorSet_mem_kubiliusBlockBadEvent_of_divisorVarianceMass_le`. After that lemma, the only
remaining work should be the standard fixed-parameter epsilon choices, the TV error limit, and the
shifted-cardinality algebra.
