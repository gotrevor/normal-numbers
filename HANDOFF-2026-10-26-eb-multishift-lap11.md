# Erdős–Borwein multishift — lap 11

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still has
its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

This lap formalized the variable prime cutoff and the first bundled asymptotic schedule requested by
lap 10.

- `natFloor_exp_log_bounds` is the reusable variable-exponent natural-floor estimate. If
  `2 log 2 <= x`, for `z = floor(exp x)` it proves `2 <= z`, `x/2 <= log z <= x`, and
  `log x - log 2 <= log log z <= log x`.
- `multiShiftScheduleU N` is exactly `J(N) * (log log log N)^3`, and
  `multiShiftCutoffY N` is exactly `floor(exp(log N / u(N)))`.
- `eventually_multiShiftScheduleU_bounds` proves `0 < u(N) <= sqrt(log N)`. The proof uses the
  deliberately coarse bound `u <= (log log N)^4` and `(log x)^8 = o(x)`.
- `eventually_multiShiftCutoffY_bounds` proves
  `collisionCutoff N <= y(N) <= N`, `2 <= y(N)`, and the sharp one- and two-log bounds above with
  `x = log N/u(N)`.
- `eventually_log_multiShiftScheduleU_le` proves `1 <= u` and
  `log u <= 4 log(log log N)`.
- `eventually_multiShiftLogBlock_bounds` proves
  ```text
  L - 6 log L - log 2
    <= log log y - log log (collisionCutoff N)
    <= L + log 2.
  ```
  This is the sharp `L - O(log L)` estimate needed to preserve the final moderate-deviation
  exponent.
- `eventually_multiShiftPrimeMean_bounds` combines that result with `mertens_primesIoc_bound` and
  proves the coarse uniform estimate `L/2 <= mu <= 2L` for the reciprocal-prime mean. This is enough
  for positivity, square-mass, baseline, and small-tilt side conditions.
- `eventually_multiShiftSieveGeometry` packages `1 <= J <= collisionCutoff N`, `2 <= y <= N`, and
  `u <= log N/log y <= 2u`.

The source diff is addition-only (`422` added lines, no deleted lines), so none of the
packet-verbatim declarations or the headline statement changed. No `native_decide`, new axiom,
heartbeat increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; only the original headline `sorry` was reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.eventually_multiShiftPrimeMean_bounds
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

The same target-specific gate with
`--axioms NormalNumbers.ErdosBorweinMultiShift.eventually_multiShiftSieveGeometry` also passed,
with the same standard axioms.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt remains outside this
scoped target.

## Current blocker

The cutoff bookkeeping is closed. The open work is the constant-dependent schedule and final
probability sum:

1. For the `C` supplied by `hM`, prove eventually
   `C * J * log(J+2) <= log N/log y`. The new geometry reduces this to
   `C log(J+2) <= (log L)^3`.
2. Prove the transfer errors tend to zero:
   `exp(-(log N/log y)/C)`, `(log N)^J/sqrt N`, and the collision cost `J^2/P`.
3. Choose fixed `eps`, `eta`, and baseline constant `A`; define the active threshold as the ceiling
   of `mu + x_j`, with the square-root subpower penalty, `A sqrt(mu)`, the shift cost, and a
   `B log L` buffer.
4. Bundle the explicit scalar premise of `shiftedVarianceMass_gt_of_heavyColumn` and all hypotheses
   of `multiShiftColumnMass_ge_moderate_of_baseline` uniformly on a long active interval.
5. Prove the sum of column lower bounds diverges, send the no-heavy product to zero, apply `hM` once
   through `low_shiftedVarianceMass_density_le_model`, and discharge Step 1'.

## Next highest-value attack

Prove a constant-parameter theorem bundling item 1 and the three vanishing error terms. Then define
the threshold schedule and attack the deterministic scalar inequality. Keep
`eventually_multiShiftLogBlock_bounds` in the hypotheses rather than replacing it by the coarse
`mu >= L/2` estimate when bounding the moderate-deviation exponent; the coarse loss would destroy
the desired threshold `c < 1`.
