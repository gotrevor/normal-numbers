# EB c < 1 from the pair model only: plan (personal-c5, 2026-10-26)

**Target:** `src/NormalNumbers/CoefmassErdosBorweinPairShift.lean` sorry-free.  The headline is
`ebRandom_ae_normal_subpower_of_pairShift (hP : PairShiftKubiliusTV)`, the same conclusion as the
proved `ebRandom_ae_normal_subpower_of_multiShift`, without `MultiShiftKubiliusTV`.

## Frozen
- Never change `primePatternIoc`, `pairShiftMass`, `PairShiftKubiliusTV` or the headline statement
  (verbatim from the KB packet).  `PairShiftKubiliusTV` is a named hypothesis: never prove, weaken or
  axiomatize it.  **Do not use `MultiShiftKubiliusTV` anywhere in this proof.**
- Do not edit `CoefmassErdosBorweinMultiShift*.lean` or other existing files.  New lemmas go in
  `CoefmassErdosBorweinPairShiftAux.lean` (new).  You may *reuse* any proved lemma from them.
- The root `src/NormalNumbers.lean` runs a barrier audit that rejects untagged open sorries, so the
  PairShift file stays OUT of the root import list until it is sorry-free.  Add
  `import NormalNumbers.CoefmassErdosBorweinPairShift` to the root only once it is, then run the full
  `lake build`.
- No `native_decide`, no new `axiom`.  Commit locally; NEVER git push.

## Route (paper: draft section "Normal for c < 1 from a pair model only")
Copy the multishift headline's skeleton: `ebRandom_ae_normal_of_shiftedVariance_diverges` with the
same `multiShiftScheduleJ`, cutoffs, thresholds and `exists_multiShiftModerateParameters`.  The
deterministic part is unchanged: `low_shiftedVarianceMass_pattern_noHeavy` (low shifted variance ⇒
no heavy shift).  Replace the product-decay / single-TV step by Chebyshev:
1. `Z(n) = #{j ∈ active columns : H_j(n)}`, with `H_j` the heavy event of shift `j` (a function of
   `primePatternIoc P₀ y₀ (n + j + 1)` only; relate it to `multiShiftPattern` columns).
2. Chebyshev on `[1, N]`: `#{Z = 0}/N ≤ (E Z² − (E Z)²)/(E Z)²`.  It is a finite counting identity,
   with `E` = average over `n ∈ Icc 1 N`.
3. `E Z = Σ_j P_N(H_j)` and `E Z² = Σ_{i,j} P_N(H_i ∧ H_j)`.  Apply `PairShiftKubiliusTV` with
   `a = i+1`, `b = j+1` (`b − a ≤ J ≤ P₀`, `b ≤ N`), and with the single-shift marginal (a pair with
   `A = S ×ˢ univ`).  Each term is within `err(N) = C(e^{−u/C} + (log N)²/√N)` of the pair model.
4. Pair model: couple to two independent Bernoulli coordinates, TV `≤ Σ_{p > P₀} 1/p² ≤ 2/P₀`
   (reuse `sum_primeIndex_inv_sq_le`).  The single-coordinate law is the column law already used, so
   `q_j ≥ multiShiftScheduledColumnMass`-type lower bounds hold, and `Σ_j q_j → ∞`
   (`tendsto_multiShiftActiveExpColumnSum` / mixed variants).
5. Conclude `Var/E² ≤ 1/E Z + (J²·(2/P₀ + 2·err) + J·err)/(E Z)² → 0`.  `J²/P₀ → 0` is already
   proved (`tendsto_multiShiftCollisionError`), and `J²·err → 0` follows from
   `tendsto_multiShiftSieveExpError` / `...PowerError` with `J ↦ 2`.
Record a dated lap checkpoint at the bottom of this file each lap.

## Lap 1 checkpoint (2026-10-26)

The route-decisive finite layer is now kernel-checked in
`CoefmassErdosBorweinPairShiftAux.lean`:

- `card_filter_eq_zero_div_le_secondMoment` is the exact finite Chebyshev inequality for the
  zero-heavy-count event.
- `sum_finiteEventCount` and `sum_finiteEventCount_sq` expand the first and second moments into
  single and pair event counts.
- `abs_categoricalShiftProduct_event_sub_independent_le` gives a two-sided arbitrary-event
  categorical/independent comparison away from collisions.
- `abs_pairBoolCountMass_sub_independent_le` specializes this to the packet's Bool-indexed pair
  law, bounding a joint cardinality tail by the product of its two independent column masses with
  collision error `4 * Σ_p p⁻²`.

Inside the still-open headline proof, the local lemma `pairShiftMass_count_eq` now proves that the
frozen concrete `pairShiftMass` cardinality event is exactly the abstract Bool categorical mass,
including both prime and state reindexing.  This was the uncertain model-identification crux; it
does not use `MultiShiftKubiliusTV`.

Exact checks passed:

```text
lake build NormalNumbers.CoefmassErdosBorweinPairShiftAux
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShift.lean
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

The full gate ended `FORMALIZE-TIER GREEN` (10971 jobs).

The target still has its original single headline `sorry`; the root import barrier remains in
place.  Next: assemble the scheduled heavy-count function, apply `PairShiftKubiliusTV` to marginals
using companion shift `J+1` and to off-diagonal pairs in sorted order, feed the resulting moment
bounds to finite Chebyshev, and close the limit using `tendsto_multiShiftActiveExpColumnSum`,
`tendsto_multiShiftCollisionError`, and the pair-error analogues of the existing sieve limits.

## Lap 2 checkpoint (2026-10-27)

The remaining finite/model interface is now substantially narrower and kernel-checked in
`CoefmassErdosBorweinPairShiftAux.lean`:

- `card_filter_eq_zero_div_le_centeredSecondMoment` and
  `card_filter_eq_zero_div_le_of_moments` center Chebyshev at the theoretical model mean.  The
  caller now needs only aggregate empirical first- and second-moment bounds; there is no fragile
  division by the empirical mean.
- `sum_pair_le_sq_add` performs the exact diagonal/off-diagonal summation.  Diagonal terms cost one
  copy of the first moment, while off-diagonal errors cost exactly `|I|(|I|-1)`.
- `bernoulliSubsetMass_relabel` proves finite Bernoulli laws invariant under coordinate
  equivalences, and `pairIndependentColumnMass_zero_eq_one` specializes it to the two pair
  columns.  Thus sorting a pair of shifts does not change either scheduled marginal.
- `pairScheduledColumnMass` is the exact independent two-column tail used by the pair coupling.
  It is in `[0,1]`; `eventually_pairColumnMass_ge_deviation` gives the existing sharp scheduled
  moderate-deviation lower bound in this fixed pair space; and
  `tendsto_pairActiveColumnMassSum` proves the active theoretical mean tends to infinity.

Exact narrow checks passed:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShiftAux.lean
lake env lean src/NormalNumbers/CoefmassErdosBorweinPairShift.lean
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

The full gate ended `FORMALIZE-TIER GREEN` (10971 jobs).

The target still has its original single headline `sorry`, and its frozen statement section was
not edited.  PairShift remains outside the root import.  Next: in the headline, define the active
heavy events and use `PairShiftKubiliusTV` with `(0,j+1)` for marginals and the sorted
`(i+1,j+1)` for off-diagonal pairs.  Rewrite the model terms with `pairShiftMass_count_eq`,
`abs_pairBoolCountMass_sub_independent_le`, and
`pairIndependentColumnMass_zero_eq_one`; then feed the termwise estimates through
`sum_pair_le_sq_add` and `card_filter_eq_zero_div_le_of_moments`.  The remaining analytic leaf is
to prove `J(N)^2` times the fixed-dimension pair TV error tends to zero (use the existing sieve
depth estimate with `2C` for the exponential term and dominate the `log(N)^2` term by the proved
multishift power error).
