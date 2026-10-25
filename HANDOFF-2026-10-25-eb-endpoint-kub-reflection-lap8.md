# HANDOFF: EB endpoint Kubilius route, reflection lap 8 — COMPLETE

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean` is now satisfied. The frozen
statements in that file, including `KubiliusTV`,
`divisorVariance_diverges_at_ln2_of_kubilius`, and
`ebPowerCandidateNormal_of_kubilius`, remain unchanged from the planted commit `e2d05168`.
`KubiliusTV` remains exactly a named hypothesis; it was not proved, weakened, or axiomatized.

## Reflection finding

The seven preceding laps had not drifted into an island or a cargo-culted route. They had closed
the genuine dependency chain in the right order: finite Bernoulli laws, independent block
crossing, the deterministic prime-jump bridge, natural-floor cutoff estimates, Mertens bounds,
and the TV error. The one missing abstraction was the eventual interface connecting the fixed
geometric schedule to the finite bridge theorems. Once that interface was stated, the remaining
proof was the expected epsilon transfer rather than new probability or number theory.

The semantic audit also found no hidden shift mismatch. The proof applies `KubiliusTV` on
`[1,N+a₀]`, embeds the shifted sample from `[1,N]` with `card_filter_Icc_add_le`, and pays the
eventual factor `(N+a₀)/N ≤ 2`. The deterministic bridge continues to use
`collisionCutoff N`, exactly as required by the frozen conclusion.

## Concrete advance

The sole scoped proof debt is discharged. New proved declarations in
`src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean` are:

- `exists_kubiliusGeometric_error_parameters`, choosing fixed `K`, `B`, and
  `r = (32B)^2 + 2` so both `(63/64)^K` and `2K/B^2` are arbitrarily small while the block
  domination scale holds;
- `eventually_kubiliusGeometric_bridgeHypotheses`, packaging cutoff containment, endpoint order,
  containment below the half-power Kubilius cutoff, pairwise block disjointness, variance at least
  one, walk-cap domination, and endpoint Mertens control for every block;
- a complete proof of `divisorVariance_diverges_at_ln2_of_kubilius`, combining those hypotheses
  with `kubiliusMass_blockBadEvent_le`, transferring the event through `KubiliusTV`, and handling
  the fixed additive shift;
- consequently, the already-wired `ebPowerCandidateNormal_of_kubilius` is now sorry-free and
  axiom-clean.

No `native_decide`, new axiom, or additional hypothesis was introduced. The target and its Aux
file have no `sorry`.

## Verification

Direct source elaboration passed:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean
```

The requested module build passed:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKub
```

It completed successfully with 9015 jobs. The real gate was:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --import NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.exists_kubiliusGeometric_error_parameters \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.eventually_kubiliusGeometric_bridgeHypotheses \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.divisorVariance_diverges_at_ln2_of_kubilius \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.ebPowerCandidateNormal_of_kubilius
```

Verdict: `FORMALIZE-TIER GREEN`. Every audited declaration reports exactly
`[Classical.choice, Quot.sound, propext]`. In addition:

```text
rg -n '\bsorry\b' \
  src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean \
  src/NormalNumbers/CoefmassErdosBorweinEndpointKubAux.lean
git diff --check
```

Both produced no findings.

## Current blocker and next attack

There is no remaining blocker or in-scope proof obligation. The host should accept the scoped
completion predicate. No stretch objective was requested, so the next action is to stop rather
than modify unrelated parts of the repository.
