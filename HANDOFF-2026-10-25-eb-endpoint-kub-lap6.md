# HANDOFF: EB endpoint Kubilius route, lap 6

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate remains
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any frozen statement in the target file, and keep
`KubiliusTV` exactly as the named hypothesis: never prove, weaken, or axiomatize it.

## Concrete advance

This lap removed the analytic floor/log ambiguity in the eventual block schedule and replaced the
earlier `(log L)^3` start by a simpler proportional-to-`L` geometric schedule. No pre-existing Lean
statement was changed.

The following helpers are now proved in
`src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`:

- `half_le_natFloor` bounds a natural floor below by half of its argument.
- `log_log_natFloor_exp_log_rpow_bounds` proves, for
  `z = floor(exp((log M)^s))`,
  `s log log M - log 2 <= log log z <= s log log M` under one explicit growth condition.
- `eventually_log_log_natFloor_exp_log_rpow_bounds` discharges that condition eventually for every
  fixed positive exponent, after the sample shift `M=N+a`.
- `natFloor_exp_log_rpow_mono` and
  `eventually_collisionCutoff_le_natFloor_exp_log_rpow_add` prove cutoff ordering and eventual
  domination of the deterministic collision cutoff.
- `kubiliusGeometricExponent K i r = r^i/(4r^K)` and
  `kubiliusGeometricCutoff` implement the new schedule. Its exponents are positive and monotone,
  obey `s_(i+1)=r*s_i`, and end at `s_K=1/4`.
- `kubiliusGeometricBlocks_disjoint` proves all distinct schedule blocks are pairwise disjoint.
- `mertens_kubiliusGeometricBlock_variance_lower` gives the explicit block lower bound
  `(1/2)((r-1)s_i L - log 2 - 2C)`.
- `mertens_kubiliusGeometricPrefix_variance_upper` gives the prefix upper bound `s_i L+C`.

These declarations close endpoint order, pairwise disjointness, natural-floor double-log control,
collision-cutoff domination, and the two Mertens estimates from the previous handoff's schedule
checklist. The target still has exactly one `sorry`, in
`divisorVariance_diverges_at_ln2_of_kubilius`.

## Verification

The narrow build passed:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKub
```

The real formal gate was run with the target module and axiom audits for every new load-bearing
helper. Its verdict was `FORMALIZE-TIER GREEN`; each audited theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`.

`git diff --check` passed. The scoped census remains one `sorry`, the frozen final Step 2 body.

## Current blocker

The remaining schedule assembly must choose fixed `K`, then a start-tail multiplier `B`, then
`r` large enough. For `I=range K`, use:

- `a_i = kubiliusGeometricCutoff M K r i`, `b_i=a_(i+1)`;
- `y=floor(exp((log M)^(1/2)))`;
- `R_i=B*sqrt(s_i*L)` and `D=L/2`.

The proved Mertens estimates reduce the start-tail term to
`(s_i L+C)/(B^2 s_i L) -> 1/B^2`, while the block variance is asymptotic to
`((r-1)s_i/2)L`. Choose `r` so its square-root coefficient divided by `8` exceeds the start-loss
coefficient `B`; the residual walk cap and constants are `o(sqrt L)`. The terminal cardinality
term is `O(L)/D^2=O(1/L)`.

After packaging these eventual inequalities, apply
`kubiliusMass_blockBadEvent_le`, transfer the resulting event with `KubiliusTV`, use
`primeFactorSet_mem_kubiliusBlockBadEvent_of_divisorVarianceMass_le` plus
`card_filter_Icc_add_le`, and finish the epsilon/Tendsto assembly.

## Next highest-value attack

Prove one `eventually_kubiliusGeometricSchedule` theorem returning exactly the hypotheses of the
two finite bridge theorems and an explicit error upper bound
`(63/64)^K + o(1) + K*(1/B^2+o(1))`. Keep `K,B,r` fixed outside the `N -> infinity` limit. Then the
final frozen theorem is routine transfer and epsilon bookkeeping.
