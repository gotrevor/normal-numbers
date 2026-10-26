# Erdős–Borwein multishift — grind lap 4

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement.  `MultiShiftKubiliusTV` remains a named hypothesis.  The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

Proved the direct finite tensorization layer for Step 4 in
`CoefmassErdosBorweinMultiShiftAux.lean`.

- `finiteProductWeight`, `finiteProductMass`, and `finiteProductWeight_sum_one` give the finite
  product-law model used by the comparison.
- `finiteProductWeight_l1_le` proves that product-law `L¹` distance is at most the sum of the
  coordinatewise distances.
- `two_mul_abs_finiteProductMass_sub_le_l1` and
  `abs_finiteProductMass_sub_le_half_l1` recover the sharp event/total-variation factor `1/2`.
- `categoricalShiftWeight` is the one-prime law used by `multiShiftMass`.
  `clearedIndependentShiftWeight` is the law that keeps the singleton outcomes from `J`
  independent Bernoulli-`q` coordinates and merges all nonsingletons into `none`.
- `categorical_cleared_l1_eq` proves their exact one-prime `L¹` distance is twice the singleton
  deficit `Jq(1-(1-q)^(J-1))`.
- `categorical_cleared_product_comparison` tensorizes this and applies
  `independentSingletonDefect_le`, giving for every event the exact route-level bound

  ```text
  |P_categorical(A) - P_cleared-independent(A)|
    <= Σ_i J(J-1)q_i².
  ```

This uses the corrected direct comparison, not the refuted conditioned-product identity.  No
statement in `CoefmassErdosBorweinMultiShift.lean` changed.  No `native_decide`, axiom, heartbeat
increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShiftAux.lean
```

Passed with no output.

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShiftAux
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed: 8707 jobs; the target emitted only the expected warning for its original headline `sorry`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --import NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --axioms NormalNumbers.ErdosBorweinMultiShift.categorical_cleared_product_comparison
```

Passed: `FORMALIZE-TIER GREEN`, 8707 jobs.  The theorem's axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs.  Existing repository proof debt was reported but is
not a gate failure at this tier.

## Current blocker

The categorical-to-cleared tensorization is closed, but the cleared law is not yet connected in
Lean to the fully independent `J`-shift Bernoulli product whose heavy events factor across shifts.
The remaining finite bridge is to push forward a `Finset (Fin J)` coordinate by keeping a singleton
and clearing every other outcome, prove that the pushforward weights are exactly
`clearedIndependentShiftWeight`, and bound the probability that clearing changes a coordinate
(a collision).  The same reciprocal-square sum gives `O(J²/P₀)`, so this is formal plumbing rather
than a new probabilistic estimate.

After that, Step 4 still needs the explicit per-shift factorization for the no-heavy event.  Steps
1, 2, 3 and final asymptotic assembly remain open.

## Next highest-value attack

Define the singleton-clearing map on `Finset (Fin J)` and prove its one-coordinate pushforward law.
Lift it coordinatewise to the finite product, bound the event discrepancy by the collision event,
and use the existing `bernoulliSubsetMass_cylinders` machinery (or an equivalent product identity)
to prove

```text
P_fully-independent(no shift is heavy) = Π_j (1 - p_j).
```

Then specialize `q_i = 1/p_i`; the two Step 4 error terms are both controlled by the
reciprocal-square tail and can be absorbed into `O(J²/P₀)`.
