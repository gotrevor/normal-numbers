# Erdős–Borwein multishift — lap 1

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement.  `MultiShiftKubiliusTV` remains a named hypothesis.  The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

Added `CoefmassErdosBorweinMultiShiftAux.lean`, proving the exact finite probability layer for
Step 5 of `EB-MULTISHIFT-NEXT.md`:

- `bernoulliTiltParameter` and `bernoulliTiltNormalizer`;
- positivity and `[0,1]` bounds for tilted parameters;
- `bernoulliTiltDenominator_bounds`, `bernoulliTiltParameter_sub`,
  `bernoulliTiltParameter_variance`, and `bernoulliTiltParameter_sub_bounds`;
- `bernoulliSubsetWeight_eq_tilted`, the exact Radon–Nikodym identity;
- `bernoulliSubsetExpectation_exp_card`, the exact cardinality MGF identity;
- `bernoulliSubsetMass_tiltedWindow_lower`, which combines the change of measure with the existing
  Bernoulli-subset Chebyshev bound to lower-bound an original-law cardinality window by the tilted
  mean/variance/normalizer expression.

The auxiliary module is imported both by the frozen target (import-only edit) and the root module.
No target statement changed; no `native_decide`, axiom, or auxiliary `sorry` was introduced.

## Exact verification

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShiftAux
```

Passed: 8707 jobs.

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed, with only the expected warning for the target's original headline `sorry`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --import NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --axioms NormalNumbers.ErdosBorweinMultiShift.bernoulliSubsetMass_tiltedWindow_lower
```

Passed: `FORMALIZE-TIER GREEN`, 8707 jobs.  The load-bearing theorem's axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs.  The existing repository proof debt is reported but is
not a gate failure at this tier.

## Current blocker

Step 5 is not yet the asymptotic moderate-deviation theorem.  The exact tilted-window lower bound
now reduces it to scalar estimates, uniformly for `q p = 1/p`:

1. choose `theta` and show the tilted mean puts a fixed-width (in tilted standard deviations)
   window above the requested threshold;
2. upper-bound the tilted variance;
3. lower-bound
   `bernoulliTiltNormalizer U q theta * exp (-theta * (tiltedMean + radius))`
   by the required Gaussian exponent.

After that theorem, follow the binding order: Step 4 product/conditioned-model coupling, then the
deterministic heavy-prime bridge, exceptional set, transfer, and Step 1′ assembly.

## Next highest-value attack

Prove a finite moderate-deviation corollary specialized enough for prime parameters: for
`q p ≤ 1/2`, `theta ≤ 1`, and deviation `x` small compared with the Bernoulli mean/variance, derive
an explicit lower bound of the form `exp (-(1+epsilon) * x^2 / (2*mu))`.  Reuse
`bernoulliTiltParameter_sub_bounds` to locate the tilted mean and
`bernoulliSubsetMass_tiltedWindow_lower` for the probability step; the remaining new work should
be scalar `exp`/`log` Taylor bounds, not finite probability bookkeeping.
