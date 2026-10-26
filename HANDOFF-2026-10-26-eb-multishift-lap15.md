# Erdős–Borwein multishift — lap 15

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis and is not to be
proved, weakened, or axiomatized. The target still has its original single `sorry`, in
`ebRandom_ae_normal_subpower_of_multiShift`.

The file differs from planting commit `b774314f` by additions only (`2488` insertions, `0`
deletions), so the packet definitions, hypothesis, and headline remain verbatim.

## Concrete advance

This lap closed the sharp exponent, divergent-sum, and full independent-product parts of the
probability argument.

- `eventually_multiShiftDeviation_sq_le` proves uniformly for every scheduled column that
  `multiShiftDeviation c A b N j^2 <= d * L * log L` for every `d > max c 0`. The proof keeps the
  exact `2N` subpower penalty and absorbs every lower-order threshold term into arbitrary slack.
- `eventually_multiShiftDeviation_exponent_le` combines that estimate with the sharp Mertens lower
  bound, giving any exponent coefficient strictly above `(1+eps)*max(c,0)/2`.
- `tendsto_multiShiftExpColumnSum` proves that the sum of the full `J = ceil(sqrt L)` exponential
  lower bounds tends to infinity whenever the coefficient is below `1/2`.
- `multiShiftScheduledColumnMass` and `multiShiftScheduledNoHeavyProduct` name the exact Bernoulli
  quantities used by the concrete coupling theorem, with their probability bounds proved.
- `prod_one_sub_le_exp_neg_sum` and `tendsto_multiShiftScheduledNoHeavyProduct` show that the full
  independent no-heavy product tends to zero.

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
  --axioms NormalNumbers.ErdosBorweinMultiShift.tendsto_multiShiftScheduledNoHeavyProduct
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt remains outside this
scoped target.

## Current blocker

Only final assembly remains. Step 1' quantifies over a fixed lower shift `j0`. The deterministic
event from `low_shiftedVarianceMass_pattern_noHeavy` uses

```text
if j0 <= j+1 then multiShiftThreshold ... j else card (primesIoc P y) + 1
```

whereas `tendsto_multiShiftScheduledNoHeavyProduct` currently uses the heavy threshold in every
column. The finitely many inactive columns are harmless, but the exact mixed-threshold adapter is
not yet formalized.

## Next highest-value attack

Prove a tail version of `tendsto_multiShiftScheduledNoHeavyProduct` for the mixed threshold above.
For `j+1 < j0`, the exponential summand is at most `1`, and `Fin.card_filter_val_lt` bounds the
number of such columns by `j0`; hence the active-column sum is at least the already-divergent full
sum minus `j0`. Prove separately that the Bernoulli event with threshold
`card(primesIoc)+1` has mass zero, so the concrete product from
`multiShiftMass_noHeavy_le_prod_one_sub` is the mixed product.

Then choose fixed constants and combine the mixed no-heavy product limit with
`eventually_multiShiftThreshold_scalar`, `low_shiftedVarianceMass_density_le_model`, one use of
`hM`, `tendsto_multiShiftTransferError`, and
`ebRandom_ae_normal_of_shiftedVariance_diverges`.
