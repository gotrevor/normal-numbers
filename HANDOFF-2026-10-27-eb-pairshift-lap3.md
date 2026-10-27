# Erdős–Borwein pair shift — review lap 3 (complete)

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinPairShift.lean` sorry-free without changing its frozen
definitions or headline statement.  Keep `PairShiftKubiliusTV` as a named hypothesis, never use
`MultiShiftKubiliusTV`, and import PairShift from the root only after the barrier is clear.

## Review verdict and concrete advance

The route was reconstructed from the actual statements, git history, and kernel checks.  It still
reaches the headline: a companion shift `(0,j+1)` gives every marginal, sorted distinct shifts give
every off-diagonal pair, and the fixed pair categorical law is within collision distance of two
independent Bernoulli columns.  This was the route-decisive seam, not auxiliary cleanup.

The scoped objective is complete.

- `CoefmassErdosBorweinPairShiftAux.lean` now proves the square-schedule weighted pair-sieve limits,
  the combined error limit
  `pairShiftSecondError C N = J(N)^2 (pairShiftSieveError C N + 4/P(N)) → 0`, and convergence of the
  resulting theoretical-mean Chebyshev quotient.
- A concrete coupling wrapper bounds the packet's Bool pair-tail mass by the product of its two
  independent column tails with error `4/P`.
- The headline proof builds the scheduled heavy-count variable, obtains marginal estimates from
  `(0,j+1)`, obtains pair estimates after sorting `(i+1,j+1)`, sums them with the finite first/second
  moment lemmas, and applies finite Chebyshev.
- `low_shiftedVarianceMass_pattern_noHeavy` converts low shifted variance into zero heavy count,
  completing the input to `ebRandom_ae_normal_of_shiftedVariance_diverges`.
- The original headline `sorry` is gone.  The frozen declarations and headline statement are
  unchanged.  `PairShiftKubiliusTV` is still an explicit parameter and was neither proved,
  weakened, nor axiomatized.
- With the file sorry-free, the root barrier was opened by adding
  `import NormalNumbers.CoefmassErdosBorweinPairShift` to `src/NormalNumbers.lean`.

## Verification

Passed:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShiftAux.lean
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShift.lean
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinPairShift \
  --import NormalNumbers.CoefmassErdosBorweinPairShift \
  --axioms NormalNumbers.ErdosBorweinPairShift.ebRandom_ae_normal_subpower_of_pairShift
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

The scoped axiom gate reports exactly `[Classical.choice, Quot.sound, propext]` and ends
`FORMALIZE-TIER GREEN`.  The full gate builds 10973 jobs and also ends `FORMALIZE-TIER GREEN`.

The forbidden-input audit finds no `sorry`, `native_decide`, or new `axiom` in either pair file.
The only textual occurrence of `MultiShiftKubiliusTV` is the module-doc prohibition; the proof does
not reference it.

## Current blocker

None in scope.  The host predicate is met.

## Next highest-value attack

No further proof attack belongs to this scoped campaign.  Preserve the completed root import and
the frozen statements; any later work should begin from a new operator objective.
