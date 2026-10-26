# Erdős–Borwein multishift — lap 2

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement.  `MultiShiftKubiliusTV` remains a named hypothesis.  The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

Completed the finite scalar-estimate layer around the lap-1 exponential tilt in
`CoefmassErdosBorweinMultiShiftAux.lean`:

- `sub_sq_le_log_one_add`: `s - s² ≤ log(1+s)` for `s ≥ 0`;
- `bernoulliTiltMean_sub_bounds`: the total tilted-mean displacement is trapped between the
  original variance times `1-exp(-theta)` and `exp(theta)-1`;
- `bernoulliTiltVariance_le`: tilted variance is at most `exp(theta)` times original variance;
- `bernoulliTiltNormalizer_lower`: the full product normalizer is at least
  `exp((exp(theta)-1)μ - (exp(theta)-1)² Σq²)`;
- `bernoulliSubsetMass_card_ge_tilt_lower`: a one-sided finite upper-tail lower bound combining
  the product estimate, tilted Chebyshev, and event monotonicity.  Its only side conditions are
  that the tilted mean clears the requested threshold by `radius` and that `radius²` dominates
  `exp(theta)` times the original variance.

No statement in `CoefmassErdosBorweinMultiShift.lean` changed.  No `native_decide`, axiom, or new
`sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShiftAux.lean
```

Passed.

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShiftAux
```

Passed: 8707 jobs.

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed, with only the expected warning for the frozen headline's original `sorry`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --import NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --axioms NormalNumbers.ErdosBorweinMultiShift.bernoulliSubsetMass_card_ge_tilt_lower
```

Passed: `FORMALIZE-TIER GREEN`, 8707 jobs.  The new load-bearing theorem's axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs.  The existing repository proof debt was reported but
is not a gate failure at this tier.

## Current blocker

Step 5 is now reduced to parameter selection and asymptotic scalar simplification.  For prime
parameters `q p = 1/p`, choose `theta` near `x/μ` and `radius` a fixed multiple of the tilted
standard deviation.  It remains to prove, uniformly in the moderate-deviation range:

1. the lower mean-displacement bound puts `tiltedMean - radius` above `μ+x`;
2. `radius² ≥ exp(theta) · variance`;
3. the exponent in `bernoulliSubsetMass_card_ge_tilt_lower` is at least
   `-(1+ε)x²/(2μ)`, using `Σq² = O(1/P₀)` and `theta → 0`;
4. the remaining Chebyshev factor is bounded below by a fixed positive constant.

The exact product correction has therefore been isolated; no finite-probability bookkeeping
remains in Step 5.

## Next highest-value attack

Prove small-`theta` scalar inequalities, preferably in an abstract lemma parameterized by
`μ`, variance, and `Σq²`: lower-bound `1-exp(-theta)`, upper-bound `exp(theta)-1`, and simplify
the exponent from `bernoulliSubsetMass_card_ge_tilt_lower`.  Then specialize to `q p = 1/p` and
the moderate range used by the multishift argument.  After Step 5 closes, follow the binding order:
Step 4 conditioned/product coupling, deterministic heavy-prime bridge, exceptional set, transfer,
and Step 1′ assembly.
