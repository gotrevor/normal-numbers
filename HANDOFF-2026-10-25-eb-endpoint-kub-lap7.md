# HANDOFF: EB endpoint Kubilius route, lap 7

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate remains
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any frozen statement in the target file, and keep
`KubiliusTV` exactly as the named hypothesis: never prove, weaken, or axiomatize it.

## Concrete advance

This lap closed four analytic bookkeeping components of the final schedule assembly. No
pre-existing statement was changed.

New proved declarations in
`src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`:

- `exists_mertens_kubiliusUnified_bound` takes the maximum of the three previously independent
  Mertens constants and supplies one nonnegative constant controlling endpoint centering, geometric
  block variance, and geometric prefix variance.
- `kubiliusBlock_variance_and_domination` proves the load-bearing square-root calculation. From
  the geometric Mertens lower bound, `(32*B)^2 <= r-1`, and two eventual scalar inequalities, it
  returns both `1 <= V` and exactly the `hdom` inequality required by
  `primeFactorSet_mem_kubiliusBlockBadEvent_of_divisorVarianceMass_le`.
- `eventually_walk_cap_add_const_le_sqrt` absorbs the fixed unified Mertens constant into the
  already-proved logarithmic walk cap.
- `eventually_kubiliusGeometric_startError_le` proves uniformly for every `i < K` that the
  block-start Chebyshev summand with `R_i = B*sqrt(s_i*L)` is eventually at most `2/B^2`.
- `eventually_kubiliusHalfCutoff_bounds` treats the terminal cutoff
  `y=floor(exp((log M)^(1/2)))`: it proves `2 <= y <= M`, positivity of `D=L/2`, the mean condition
  for `kubiliusMass_blockBadEvent_le`, and the terminal-cardinality error bound `<= 4/L`.
- `tendsto_kubiliusHalfCutoff_error` proves the explicit `KubiliusTV` error tends to zero. The key
  elementary estimate is `u >= sqrt(log M)` and hence, once `u >= 2`, `u^(-u) <= 1/u`.

Together these remove all asymptotic probability-error work except choosing `K` and `B`, and all
TV-cutoff analysis. The target still has exactly one `sorry`, the frozen final Step 2 body.

## Verification

The source file was repeatedly checked directly with:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean
```

It passes with only the pre-existing warning on
`divisorVariance_diverges_at_ln2_of_kubilius`. The narrow module build passed:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKub
```

The real gate passed:

```text
~/personal/bin/lean-green . \
  --target NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --import NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.tendsto_kubiliusHalfCutoff_error
```

Its verdict was `FORMALIZE-TIER GREEN`. A separate scratch import ran `#print axioms` on all six
new declarations; every result uses only `propext`, `Classical.choice`, and `Quot.sound`.
`git diff --check` passed. The statement diff contains only new helpers inserted before the frozen
theorem; its statement and the named `KubiliusTV` hypothesis are unchanged.

## Current blocker

The remaining proof must package the structural/eventual block hypotheses and perform the final
epsilon transfer. Fix `K`, then choose `B` so `2*K/B^2` is small, and set for example
`r = (32*B)^2 + 2`. For `I=range K`, `s_i=kubiliusGeometricExponent K i r`,
`a_i=kubiliusGeometricCutoff M K r i`, `b_i=a_(i+1)`, and
`R_i=B*sqrt(s_i*L)`:

- use the minimum exponent `s_0` to discharge all growth conditions uniformly;
- use `eventually_collisionCutoff_le_natFloor_exp_log_rpow_add` at `s_0`, monotonicity of the
  schedule, `kubiliusGeometricExponent_le_quarter`, and
  `kubiliusGeometricBlocks_disjoint` for `hPa`, `hab`, `hby`, and `hdisj`;
- feed the unified block lower bound plus eventual loss/unit inequalities into
  `kubiliusBlock_variance_and_domination` for `hV` and `hdom`;
- apply `kubiliusMass_blockBadEvent_le`; the two new error lemmas reduce its right side to
  `(63/64)^K + 4/L + 2*K/B^2`;
- transfer the deterministic subevent through `KubiliusTV`, use
  `tendsto_kubiliusHalfCutoff_error`, then use `card_filter_Icc_add_le` and `M/N <= 2`.

## Next highest-value attack

Prove one `eventually_kubiliusGeometric_bridgeHypotheses` lemma containing the six structural
hypotheses above. Then fill the frozen theorem directly: all analytic error terms and the TV limit
now have dedicated lemmas, so only the finite `K,B` epsilon choice and shift-factor arithmetic
remain.
