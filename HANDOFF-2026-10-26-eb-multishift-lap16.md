# Erdős–Borwein multishift — lap 16 (complete)

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. Keep `MultiShiftKubiliusTV` as a named hypothesis, with no
`native_decide`, new axiom, or push.

## Concrete advance

The objective is complete.

- `tendsto_multiShiftActiveExpColumnSum` proves that removing the fixed initial columns below
  Step 1's lower shift `j₀` preserves divergence. Each deleted exponential summand is at most one,
  and `Fin.card_filter_val_lt` bounds their number by `j₀`.
- `multiShiftMixedThreshold`, `multiShiftMixedColumnMass`, and
  `multiShiftMixedNoHeavyProduct` encode the exact mixed event used by the deterministic transfer.
  `tendsto_multiShiftMixedNoHeavyProduct` proves its independent no-heavy probability tends to
  zero.
- `exists_multiShiftModerateParameters` chooses compatible `eps`, `eta`, `A`, and `alpha` for
  every `c < 1` and discharges all fixed moderate-deviation inequalities.
- `ebRandom_ae_normal_subpower_of_multiShift` now applies Step 1', builds the exact mixed event,
  invokes `MultiShiftKubiliusTV` once, bounds its model mass by the mixed product plus collision
  loss, and sends all terms to zero.

The planting-commit audit

```text
git diff b774314f --unified=0 -- \
  src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean | rg '^-[^-]'
```

returns only `-  sorry`. Thus all packet-verbatim statements remain unchanged. The scoped file
contains no `sorry`, `native_decide`, or declared axiom.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed with no declaration-uses-sorry warning.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.ebRandom_ae_normal_subpower_of_multiShift
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. The headline axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing proof debt elsewhere in the repository is
outside this scoped objective.

## Current blocker

None for the scoped objective. `MultiShiftKubiliusTV` intentionally remains the packet's named
hypothesis and was neither proved, weakened, nor axiomatized.

## Next highest-value attack

No further attack is required for the host predicate
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean`. Preserve this green checkpoint
and move only under a new operator objective.
