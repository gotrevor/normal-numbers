# Erdős–Borwein multishift — lap 12

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still has
its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

This lap closed the constant-dependent sieve schedule and every transfer/coupling loss identified
by lap 11.

- `eventually_multiShiftSieveDepth C hC` proves eventually
  ```text
  C * J(N) * log(J(N)+2) <= log N / log(y(N)).
  ```
  The proof bounds `log(J+2)` by `2 log L`, absorbs the fixed constant into `(log L)^3`, and then
  uses `u <= log N/log y` from `eventually_multiShiftSieveGeometry`.
- `tendsto_multiShiftSieveExpError` proves the Rankin term
  `exp(-(log N/log y)/C)` tends to zero. The lower bound `log N/log y >= u >= log L` is enough.
- `tendsto_multiShiftSievePowerError` proves `(log N)^J/sqrt N -> 0`. It rewrites the quotient as
  `exp(J L - log N/2)` and uses `J <= L` together with `(log(log N))^2 = o(log N)`.
- `tendsto_multiShiftCollisionError` proves the exact concrete coupling cost
  `2 J(J-1)/collisionCutoff N -> 0`. From `log P >= L^2/2` and the exponential series it gets
  `P >= L^4/8`, hence the cost is at most `16/L^2`.
- `tendsto_multiShiftTransferError` packages exactly the sum of the `hM` total-variation error and
  the collision loss for the final transfer.

The source diff is addition-only, so no packet-verbatim declaration or headline statement changed.
No `native_decide`, axiom, heartbeat increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; only the original headline `sorry` was reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.tendsto_multiShiftTransferError
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

The same target-specific gate with
`--axioms NormalNumbers.ErdosBorweinMultiShift.eventually_multiShiftSieveDepth` also passed, with
the same standard axioms.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt remains outside this
scoped target.

## Current blocker

The sieve geometry, depth, and vanishing error bookkeeping are closed. The remaining analytic core
is the heavy-column threshold and probability sum:

1. Fix constants `eps`, `eta`, `A`, and `B`; define the active threshold as the ceiling of the
   reciprocal-prime mean plus the subpower square-root penalty, `A sqrt(mean)`, the shift cost, and
   `B log L`.
2. Prove uniformly on a long active shift interval the explicit scalar premise of
   `shiftedVarianceMass_gt_of_heavyColumn`.
3. Prove uniformly the side conditions of `multiShiftColumnMass_ge_moderate_of_baseline`.
4. Use the sharp mean lower estimate `L - O(log L)`, not only `L/2`, to show the sum of the resulting
   column probabilities diverges for every `c < 1`.
5. Send the no-heavy product to zero, apply `hM` once through
   `low_shiftedVarianceMass_density_le_model`, and discharge Step 1'.

## Next highest-value attack

Define the threshold schedule and prove the deterministic scalar inequality first. This pins the
exact square-root and logarithmic buffers before the moderate-deviation exponent is estimated. Use
an active interval of order `sqrt(L/log L)` if needed to keep the shift cost at the same order as
the subpower penalty; the available `J ~ sqrt L` contains it.
