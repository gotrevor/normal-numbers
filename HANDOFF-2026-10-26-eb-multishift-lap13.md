# Erdős–Borwein multishift — review lap 13

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still has
its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Fresh review verdict

The route still reaches the frozen headline and the work remains on the route-decisive crux.

- The packet definitions, `MultiShiftKubiliusTV`, and the headline were compared with planting
  commit `b774314f`; their statements are unchanged.
- The multishift indexing is correct: `multiShiftPattern P y J n j` records divisors of
  `n + j.val + 1`, exactly the `j+1` summand of `shiftedVarianceMass` used by
  `low_shiftedVarianceMass_pattern_noHeavy` and Step 1'.
- Steps 3–5 already provide the finite TV transfer, categorical-to-independent coupling, exact
  column factorization, and a finite moderate-deviation lower bound. The remaining load-bearing
  work is therefore the threshold asymptotics and divergent probability sum, not more finite-model
  scaffolding.
- The exact penalty at the deterministic global cutoff should be retained until the probability
  estimate. Replacing it early by `sqrt(c*L*log L)` would create an unnecessary approximation debt.

The repository-level `DIRECTION.md`, `PENDING_WORK.md`, and `STATUS.md` describe older branch
campaigns and contain no multishift directive. `EB-MULTISHIFT-NEXT.md` and the scoped operator
instructions are the live campaign documents.

## Concrete advance

This lap fixed the threshold schedule and closed its deterministic scalar inequality.

- `multiShiftPrimeMean N` names the exact reciprocal-prime mean on the scheduled block.
- `multiShiftSubpowerPenalty c N` is the exact square-root exponent occurring in
  `subpowerWeight c (2*N)`.
- `multiShiftThreshold c A b N j` is the ceiling of the mean plus that exact penalty,
  `A*sqrt(mean)`, the exact shift cost `2(j+1) log b / log 2`, and `8 log L`.
- `eventually_multiShiftPrimeMean_lower` retains the sharp Mertens estimate
  `mean >= L - 6 log L - O(1)`; the earlier coarse `mean >= L/2` bound would lose the final
  exponent.
- `eventually_log_log_two_mul_le` controls the global cutoff by
  `log log (2N) <= L + log 2`.
- `tendsto_multiShiftBufferedMean` proves
  `mean + 8 log L - log log (2N) -> infinity`.
- `eventually_multiShiftThreshold_scalar` combines these facts with exact exponential algebra and
  proves uniformly for every natural shift index `j`

  ```text
  T*b^(2*(j+1))
    < 2^(multiShiftThreshold c A b N j - 1)
        * (c0 * subpowerWeight c (2*N)).
  ```

  This is precisely the scalar premise needed by
  `shiftedVarianceMass_gt_of_heavyColumn`/`low_shiftedVarianceMass_pattern_noHeavy`. The theorem
  allows arbitrary real `c`, arbitrary `T`, every `A >= 0`, and every fixed `c0 > 0`; no high-shift
  cutoff is needed on the deterministic side.

All source changes are additions. No packet-verbatim declaration or headline statement changed,
and no `native_decide`, axiom, heartbeat increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; only the original frozen headline `sorry` was reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.eventually_multiShiftThreshold_scalar
```

Passed: `FORMALIZE-TIER GREEN`, 9019 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt remains outside this
scoped target.

## Current blocker

The deterministic threshold is closed. The remaining analytic core is to turn the same threshold
into enough independent heavy columns.

1. Choose constants `eps > 0`, `eta <= 1/100`, and a fixed sufficiently large `A`, with
   `c*(1+eps) < 1` in the positive-`c` branch.
2. Define an active prefix `K(N)` of order `sqrt(L/log L)` and prove `K(N) <= J(N)` eventually.
3. For every active `j`, prove the square-mass, small-tilt, baseline, and absorption hypotheses of
   `multiShiftColumnMass_ge_moderate_of_baseline` for the displacement inside
   `multiShiftThreshold`.
4. Bound the exact `2N` penalty by `(1+o(1))*sqrt(c*L*log L)` when `0 < c < 1`; for `c <= 0` it is
   eventually zero. Show the summed lower bounds diverge in both cases.
5. Convert the ceiling event to the natural threshold event, send the product to zero, add the
   already-vanishing collision/TV error, and feed the resulting density limit to Step 1'.

## Next highest-value attack

Prove one uniform active-prefix side-condition bundle for
`multiShiftColumnMass_ge_moderate_of_baseline`. Start with the small-tilt estimate
`x_j / mean -> 0` uniformly for `j < K(N)`: it forces the useful choice of `K`, and the same bounds
will feed the exponent estimate. Do not weaken to the coarse `mean >= L/2` when estimating the
final exponential rate; use `eventually_multiShiftPrimeMean_lower` there.

