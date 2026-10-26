# Erdős–Borwein multishift — lap 9

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

This lap connected the abstract moderate-deviation theorem to the packet's concrete multishift
model.

- `primesIoc_eq_primesUpTo_filter` identifies the packet's `(P,y]` block with the natural-cutoff
  block used by `CoefmassErdosBorweinEndpointKub`.
- `mertens_primesIoc_bound` proves, for one nonnegative constant `C`,

  ```text
  |sum_{P<p<=y} 1/p - (log log y - log log P)| <= 2C.
  ```

- `sum_primeIndex_inv_eq_primesIoc` and `sum_shiftArrayColumn_inv_eq_primesIoc` transport that
  exact mean through `primeIndexEquiv` and into every independent shift column.
- The generic auxiliary theorem `sum_shiftArrayColumn_fst` identifies a column sum with its prime
  coordinate sum. Together with the existing reciprocal-square tail it yields
  `sum_shiftArrayColumn_inv_sq_le`, namely square-mass at most `1/P` in every column.
- `multiShiftColumnMass_ge_moderate` applies
  `bernoulliSubsetMass_card_ge_moderate_lower` on one column support and then uses
  `bernoulliSubsetMass_inter` to restore the full `Fin n x Fin J` universe. Its conclusion is in
  exactly the Bernoulli law occurring in `multiShiftMass_noHeavy_le_prod_one_sub`.

Consequently the finite-model bookkeeping between Steps 4 and 5 is closed for `c > 0`. For the
eventual integer threshold `ceil(mean + x_j)`, `Nat.ceil_le` rewrites the heavy event directly to
the real-cardinality event in `multiShiftColumnMass_ge_moderate`.

No packet-verbatim definition or theorem statement changed. No `native_decide`, axiom, heartbeat
increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShiftAux.lean
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; the target emitted only the expected warning for its original headline `sorry`.

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShift
```

Passed: 9019 jobs; only existing publish-tier warnings and the target's original headline `sorry`
were reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.multiShiftColumnMass_ge_moderate
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

The same target-specific gate with
`--axioms NormalNumbers.ErdosBorweinMultiShift.mertens_primesIoc_bound` also passed with exactly
the same standard axioms.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt was reported but is
not a gate failure at this tier. As in the preceding multishift laps, the root module imports the
auxiliary file but not the still-open packet target, so the target-specific gates above are the
checks that cover this campaign file.

## Current blocker

The headline still needs the asymptotic schedule and transfer assembly. In the `c > 0` branch the
finite probability theorem is no longer a blocker, but one must define `J(N)`, `u(N)`, `y0(N)` and
the column thresholds, then prove eventually:

1. the sieve side conditions for `hM` and the collision error `J^2/P -> 0`;
2. the explicit scalar premise of `shiftedVarianceMass_gt_of_heavyColumn` at every heavy column;
3. the five scalar hypotheses of `multiShiftColumnMass_ge_moderate` uniformly over the relevant
   shifts; and
4. divergence of the sum of those column lower bounds, hence decay of the no-heavy product.

The `c <= 0` branch remains separate: its displacement is only `O(log L + j)`, so the moderate
theorem's large-deviation premise is the wrong tool. It needs a fixed-probability central-tail
lower bound on the initial range of shifts.

## Next highest-value attack

Define the schedule functions and the integer heavy threshold in Lean, then prove a bundled
eventual scalar theorem for the `c > 0` branch. Start with the deterministic inequality: show
`ceil(mean + x_j)` primes make

```text
T * b^(2*(j+1)) < 2^(threshold_j-1) * c0 * subpowerWeight c (2*N).
```

Use `mertens_primesIoc_bound` to replace `mean` by `log log y0 - log log P + O(1)`. Once this is
green, reuse the same schedule estimates to discharge the moderate-deviation hypotheses and the
sum-of-column-probabilities divergence. Do not reintroduce an `omega(n+j)` cap.
