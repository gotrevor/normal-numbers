# Erdős–Borwein multishift — lap 10

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still has
its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

This lap proved the finite deterministic/TV transfer into the already-factored model and removed
the planned separate probability branch at `c <= 0`.

- `low_shiftedVarianceMass_pattern_noHeavy` proves the exact Step 3 deterministic event inclusion.
  On an active shift `j + 1 >= j0`, threshold many block primes imply the actual-cardinality scalar
  bound and lap 8's `shiftedVarianceMass_gt_of_heavyColumn` contradicts low shifted mass. On an
  inactive shift, the adjusted threshold `card (primesIoc P y) + 1` is impossible because the
  concrete column is a subset of `primesIoc P y`.
- `low_shiftedVarianceMass_density_le_model` is the generic finite TV transfer: deterministic
  containment plus the absolute TV inequality bounds the low-mass density by model mass plus TV
  error. Thus the eventual proof can apply `hM` exactly once.
- `multiShiftColumnMass_ge_moderate_of_baseline` derives the existing moderate theorem's
  large-deviation and absorption hypotheses from one square-root baseline condition
  `A^2 * mean <= x^2`. Choose fixed `A` with `6 <= eta^2 A^2` and
  `4 log 2 <= eps A^2`.
- This gives a unified threshold for all `c < 1`: add `A * sqrt(mean)` to the displacement. When
  `c <= 0`, the subpower square-root penalty vanishes but the added baseline gives a fixed positive
  probability for each of order `sqrt L` columns. When `c > 0`, the baseline is lower order than
  `sqrt(c L log L)`, so the required `L^{-c(1+eps)/2}` exponent is unchanged. The separate
  fixed-probability central-tail lemma requested by laps 8–9 is therefore retired.
- `multiShiftScheduleJ N = ceil(sqrt(log log N))` is now defined.
  `eventually_multiShiftScheduleJ_le_log_log` discharges Step 1's schedule hypothesis and
  `tendsto_multiShiftScheduleJ` proves that the shift supply grows.

No packet-verbatim definition or theorem statement changed. No `native_decide`, axiom, heartbeat
increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; only the original headline `sorry` was reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.low_shiftedVarianceMass_pattern_noHeavy
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

The same target-specific gate with
`--axioms NormalNumbers.ErdosBorweinMultiShift.multiShiftColumnMass_ge_moderate_of_baseline`
also passed with exactly the same standard axioms.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt was reported but is
outside this scoped target; the root module still does not import the open packet target, so the
target-specific gates above are the checks covering this campaign file.

## Current blocker

Only the scalar/asymptotic schedule and final assembly remain. For `L = log log N` and
`J = ceil(sqrt L)`, define a variable cutoff of the planned size
`y = floor(exp(log N / (J * (log L)^3)))`. The next bundled eventual theorem must establish:

1. `collisionCutoff N <= y <= N`, `J <= collisionCutoff N`, and the `hM` sieve inequality;
2. Mertens mean `mu = sum_{P<p<=y} 1/p = L - O(log L)`, in particular `mu` comparable to `L`;
3. for active `j`, the threshold
   `ceil(mu + sqrt(max c 0 * L * log L) + A * sqrt(mu) + 2(j+1) log b/log 2 + B log L)`
   implies the explicit prime-chain scalar inequality;
4. uniformly on a long active interval, the baseline-moderate hypotheses and a summable lower
   bound whose column sum diverges;
5. the collision and `hM` errors tend to zero.

The finite event containment, one-use TV transfer, model product factorization, and both signs of
`c` now need no further case-specific probability machinery.

## Next highest-value attack

Define the variable cutoff and prove a first bundled cutoff/mean theorem. Reuse the floor bounds in
`CoefmassErdosBorweinEndpointKub.lean` (`half_le_natFloor` and the log-log cutoff proofs), but adapt
them to the variable exponent `1 / (J * (log L)^3)`. Aim first for coarse eventual bounds
`L / 2 <= mean <= 2L`; they are sufficient for all moderate-deviation side conditions and for the
square-root baseline. Then prove the sharper upper exponent needed for the column-sum divergence.
