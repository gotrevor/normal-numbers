# Erdős–Borwein pair shift — lap 1

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinPairShift.lean` sorry-free without changing any frozen
statement.  Keep `PairShiftKubiliusTV` as a named hypothesis, never use `MultiShiftKubiliusTV`, and
keep PairShift out of the root import until complete.

## Concrete advance

The finite second-moment and pair-model layer is proved.

- New auxiliary module `src/NormalNumbers/CoefmassErdosBorweinPairShiftAux.lean` proves finite
  Chebyshev (`card_filter_eq_zero_div_le_secondMoment`) and exact indicator first/second moment
  expansions (`sum_finiteEventCount`, `sum_finiteEventCount_sq`).
- `abs_categoricalShiftProduct_event_sub_independent_le` generalizes the existing collision
  coupling from no-heavy events to arbitrary events preserved by singleton clearing.
- `abs_pairBoolCountMass_sub_independent_le` specializes the coupling to the frozen Bool pair law:
  the joint tail differs from the product of independent Bernoulli column tails by at most
  `4 * Σ q_p²`.
- The local proved helper `pairShiftMass_count_eq` in the headline proof identifies the frozen
  concrete `pairShiftMass` count event with that abstract product model.  It handles the
  `primesIoc` enumeration and the Bool state relabeling exactly.

The planting diff changes no line of `primePatternIoc`, `pairShiftMass`, `PairShiftKubiliusTV`, or
the headline statement.  The target still has its original one `sorry`; no new proof debt was
introduced.

## Exact verification

```text
lake build NormalNumbers.CoefmassErdosBorweinPairShiftAux
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShift.lean
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

All passed.  The full gate ended `FORMALIZE-TIER GREEN` (10971 jobs); the direct target check
reports only the pre-existing headline `sorry`.

Forbidden-input audit:

```text
rg -n 'MultiShiftKubiliusTV|native_decide|^axiom ' \
  src/NormalNumbers/CoefmassErdosBorweinPairShift{,Aux}.lean
```

Only the docstring saying not to use `MultiShiftKubiliusTV` matches.  PairShift remains absent from
`src/NormalNumbers.lean`.

## Current blocker

The asymptotic assembly is still open: define the active heavy-count `Z_N`, transfer each marginal
and off-diagonal joint count with `PairShiftKubiliusTV`, estimate its empirical variance, and show
the Chebyshev quotient tends to zero.  This is hard but in-scope, not an operator blocker.

## Next highest-value attack

Copy the deterministic setup from the multishift headline through `low_shiftedVarianceMass_pattern_noHeavy`.
For each active column `j`, obtain its marginal using the legal pair `(j+1, J+1)`; for `i < j`, use
the sorted pair `(i+1, j+1)`.  Rewrite the model terms with `pairShiftMass_count_eq`, apply
`abs_pairBoolCountMass_sub_independent_le` plus `sum_primeIndex_inv_sq_le`, then use
`sum_finiteEventCount{,_sq}` and `card_filter_eq_zero_div_le_secondMoment`.  Finish the scalar limit
from `tendsto_multiShiftActiveExpColumnSum`, `tendsto_multiShiftCollisionError`, and the existing
pair-compatible sieve exponential/power estimates.
