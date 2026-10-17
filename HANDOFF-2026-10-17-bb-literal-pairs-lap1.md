# Literal Bailey--Borwein pairs lap 1 — power-growth analytic engine (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order.  The host gate is
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`.  Its two ratified theorems,
`isNormal_stonehamAlpha_add` and `isNormal_stonehamAlpha_sub`, remain the only scoped sorries;
their statements and `VandeheyThm51` were not changed.

## Concrete crux advance

Kickoff step 1 is complete.  New module `StonehamPairsAnalytic.lean` generalizes the analytic
half of Theorem A from the former linear reduced-denominator hypothesis

```text
n <= A * den(state n)
```

to the referee-required positive-power hypothesis

```text
n^rho <= C0 * den(state n),    rho > 0, C0 > 0.
```

The new arithmetic interface is `StonehamStateDenPowerLower`.  The proof carries this weaker
bound through square blocking: on a good block the Vandehey factor is bounded by
`((J^rho)/C0)^(-delta)`, whose logarithmically weighted contribution tends to zero because
`rho*delta > 0`.  The completed chain is:

- `stonehamState_block_den_bounds_of_powerLower`;
- `stoneham_den_neg_rpow_le_of_powerLower`;
- `stonehamState_square_bound_of_powerLower`;
- `tendsto_stoneham_power_analytic_rate`;
- `stonehamState_square_mean_tendsto_of_powerLower`;
- `stonehamState_mean_tendsto_of_powerLower`;
- `stonehamCombination_mean_tendsto_of_powerLower`.

`stonehamState_den_powerLower_one_of_linearLower` embeds the old linear interface at exponent
one, so this is a genuine generalization.  Theorem A and every statement in
`StonehamSumsNormal.lean` remain unchanged.  `StonehamPairsNormal.lean` now imports the new
module so later arithmetic work is checked on the scoped target's actual import path.

## Verification

The narrow module check passed:

```text
lake env lean src/NormalNumbers/StonehamPairsAnalytic.lean
```

The real target gate was run as:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsAnalytic \
  --axioms NormalNumbers.StonehamSumsNormal.stonehamCombination_mean_tendsto_of_powerLower \
  --axioms NormalNumbers.StonehamSumsNormal.stonehamState_square_mean_tendsto_of_powerLower
```

It completed 8,775 jobs and ended `FORMALIZE-TIER GREEN`.  Both audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`.  The two reported target sorries are the
unchanged binding obligations.

## Current blocker

Kickoff step 2, the arithmetic half (Lemma 3-prime), is now the sole route-decisive blocker.
One must prove that every literal two-family state which is not the trivial equal-family
difference has a positive-power reduced-denominator lower bound.  This includes overlapping
prime support and same multiplicative classes; pairwise coprimality cannot be reintroduced.

## Next highest-value attack

Formalize the finite-level Teichmueller congruence (K), beginning with an odd prime `ell`:
for `ell | N`, compare `b^N` modulo `ell^(v_ell(N)+1)` with the finite representative
`w = b^(ell^K) mod ell^(K+1)`.  Then prove the `ell = 2` lifting variant.  Package the resulting
polar/periodic tail for exactly one or two literal families, prove the top-digit never-silent
lemma for coefficients in `{1}` or `{+1,-1}`, and derive `StonehamStateDenPowerLower` for the
sum and unequal difference states.  Once those bounds exist, feed them directly to
`stonehamCombination_mean_tendsto_of_powerLower` and the existing Weyl criterion.

