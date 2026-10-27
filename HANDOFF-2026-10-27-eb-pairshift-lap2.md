# Erdős–Borwein pair shift — lap 2

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinPairShift.lean` sorry-free without changing any frozen
statement.  Keep `PairShiftKubiliusTV` as a named hypothesis, never use `MultiShiftKubiliusTV`, and
keep PairShift out of the root import until complete.

## Concrete advance

The theoretical-mean second-moment interface and the fixed-pair scheduled marginal are proved.

- `card_filter_eq_zero_div_le_centeredSecondMoment` bounds the zero set while centering at any
  positive theoretical mean.
- `card_filter_eq_zero_div_le_of_moments` consumes only aggregate first- and second-moment bounds.
- `sum_pair_le_sq_add` exactly separates the diagonal from the ordered off-diagonal sum, retaining
  the sharp `Q` diagonal term and `|I|(|I|-1)d` pair-error term.
- `bernoulliSubsetMass_relabel` is a general coordinate-relabeling theorem for finite Bernoulli
  subset laws.  Its pair specialization `pairIndependentColumnMass_zero_eq_one` proves that the
  false/true pair columns have identical cardinality-tail laws, resolving the orientation issue
  created by sorting two shifts before applying `PairShiftKubiliusTV`.
- `pairScheduledColumnMass` packages that fixed two-column tail.  Its nonnegativity and unit upper
  bound are proved.  `eventually_pairColumnMass_ge_deviation` ports the existing sharp
  moderate-deviation estimate into the fixed pair space, and `tendsto_pairActiveColumnMassSum`
  proves the sum over active shifts tends to infinity.

No line of the frozen PairShift definitions or headline was changed.  The target still has its
original single headline `sorry`; no proof debt was added.

## Verification

Passed:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShiftAux.lean
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShift.lean
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

The full gate ended `FORMALIZE-TIER GREEN` (10971 jobs).  The direct target check reports only the
pre-existing headline `sorry`.  The forbidden-input audit
still finds only the docstring occurrence of `MultiShiftKubiliusTV`; there is no `native_decide` or
new `axiom`, and PairShift remains absent from `src/NormalNumbers.lean`.

## Current blocker

The headline must still instantiate the proved interface: transfer each active marginal and
off-diagonal joint count with `PairShiftKubiliusTV`, sum the bounds, apply theoretical-mean
Chebyshev, and show the resulting scheduled error quotient tends to zero.  This is hard but
in-scope, not an operator blocker.

## Next highest-value attack

Inside the headline, use `(a,b)=(0,j+1)` for a marginal and sorted `(i+1,j+1)` for `i≠j`.  Rewrite
pair-model masses with `pairShiftMass_count_eq`; use
`abs_pairBoolCountMass_sub_independent_le`, `sum_primeIndex_inv_sq_le`, and
`pairIndependentColumnMass_zero_eq_one` to obtain the termwise hypotheses of
`sum_pair_le_sq_add`.  Feed its aggregate bound and the summed marginal lower bound to
`card_filter_eq_zero_div_le_of_moments`.  Finally prove the dedicated limit
`J(N)^2 * C(exp(-u/C) + log(N)^2/sqrt(N)) → 0`; the exponential term follows from
`eventually_multiShiftSieveDepth (2*C)`, and the power term can be dominated by
`tendsto_multiShiftSievePowerError` once `J≥4`.
