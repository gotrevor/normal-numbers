# Erdős–Borwein multishift — lap 14

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis and is not to be
proved, weakened, or axiomatized. The target still has its original single `sorry`, in
`ebRandom_ae_normal_subpower_of_multiShift`.

The file differs from planting commit `b774314f` by additions only (`1953` insertions, `0`
deletions), so the packet definitions, hypothesis, and headline remain verbatim.

## Concrete advance

This lap closed the full moderate-deviation side-condition and event-shape adapter for the exact
threshold.

- `multiShiftDeviation c A b N j` is the exact threshold displacement: subpower penalty at `2N`,
  the `A*sqrt(mean)` baseline, shift cost, logarithmic buffer, and a final `+1` for the ceiling.
- `eventually_multiShiftDeviation_smallTilt` proves, for every fixed `c < 1`, `A`, `b >= 2`, and
  `eta > 0`, uniformly for **all** `j : Fin (multiShiftScheduleJ N)`,

  ```text
  (1 + 4*eta) * multiShiftDeviation c A b N j / multiShiftPrimeMean N <= eta.
  ```

  This is stronger than the lap-13 plan's active prefix `K ~ sqrt(L/log L)`: no column truncation
  is required. The proof bounds the exact subpower radicand by `4 L log L`, the baseline and shift
  costs by `o(L)`, and uses the sharp definition `J = ceil(sqrt L)`.
- `eventually_multiShiftModerateSideConditions` packages all variable side conditions for
  `multiShiftColumnMass_ge_moderate_of_baseline`: positive mean and displacement, reciprocal-square
  mass, small tilt, and `A^2*mean <= deviation^2`.
- `eventually_multiShiftColumnMass_ge_deviation` applies that theorem uniformly on every scheduled
  column and then uses `bernoulliSubsetMass_mono` to pass from the real event
  `mean + deviation <= card` to the exact packet threshold event
  `multiShiftThreshold ... <= card`. The final `+1` in the displacement absorbs `Nat.ceil`.

No existing declaration was edited. No new `sorry`, axiom, `native_decide`, or heartbeat override
was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; only the original frozen headline `sorry` was reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.eventually_multiShiftColumnMass_ge_deviation
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt remains outside this
scoped target.

## Current blocker

The remaining analytic core is the exponent and divergent-sum estimate. The finite probability
theorem, every side condition, the ceiling conversion, and the exact target event shape are now
closed.

1. Choose fixed `eps > 0`, `eta <= 1/100`, and sufficiently large `A`, with
   `c*(1+eps) < 1` when `c > 0`. For `c <= 0`, the exact penalty is eventually zero.
2. Uniformly in all `j < J`, upper-bound
   `(1+eps)*deviation_j^2/(2*mean)`. The main term is
   `(1+eps)*c*log L/2`; the baseline, shift, buffer, and mean loss are `o(log L)`.
3. Deduce that the sum of the `J ~ sqrt L` exponential lower bounds tends to infinity. Since the
   full shift schedule is available, it suffices to obtain any exponent strictly below `1/2`.
4. Apply `multiShiftMass_noHeavy_le_prod_one_sub`, bound the product by the exponential of the
   negative sum, and add `tendsto_multiShiftTransferError`.
5. Feed the resulting density limit through `low_shiftedVarianceMass_density_le_model`, the
   deterministic scalar theorem, and Step 1'
   `ebRandom_ae_normal_of_shiftedVariance_diverges`.

## Next highest-value attack

Prove one explicit uniform exponent upper bound using `eventually_multiShiftPrimeMean_lower`; do
not replace the denominator by the coarse `mean >= L/2`, which would double the main exponent and
lose the `c < 1` threshold. A convenient form is to choose `alpha` with
`c*(1+eps)/2 < alpha < 1/2` and prove eventually, for every scheduled `j`,

```text
(1+eps) * multiShiftDeviation c A b N j^2 /
    (2 * multiShiftPrimeMean N) <= alpha * log L.
```

Then every column probability is at least `L^(-alpha)`, and
`J * L^(-alpha) -> infinity` follows from `J >= sqrt L` and `alpha < 1/2`.
