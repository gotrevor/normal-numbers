# HANDOFF — Track D3 missing-word Hausdorff dimension

Updated 2026-08-26 by the autonomous Track D lap.

## Concrete advance

1. Closed the explicit API gap in `Disjunctive.lean`:
   `NormalNumbers.IsNormal.isDisjunctive {b x} (h : IsNormal b x) (hb : 2 ≤ b)`.
   The proof extracts an actual occurrence of every nonempty valid word from
   its positive limiting normal frequency; the empty word is vacuous.  The
   aggregator already imports `Disjunctive.lean`.  Roadmap and landscape docs
   were updated.  This green checkpoint is commit `b755fd5`.
2. Added `QuadraticDisjunctive.lean` and wired it into `NormalNumbers.lean`.
   It contains:
   - faithful `IsQuadraticIrrational` (irrational integral quadratic root with
     nonzero leading coefficient);
   - `QuadraticHypothesisM b`, a named uninhabited `Prop`, not a Lean axiom;
   - the explicit endpoint-safe `circleMissingWordSubshift b w`, with proved
     closedness, forward invariance, and membership for a point missing `w`;
   - the axiom-clean dynamical assembly
     `quadratic_irrationals_disjunctive_of_hypothesisM_of_missingWordDimension`;
   - the reusable Hausdorff cover lemma `dimH_lt_one_of_finite_covers`;
   - `missingWordExponent_lt_one`, proving the decisive strict entropy gap
     `log(b^L-1)/log(b^L) < 1` for `b ≥ 2`, `L ≥ 1`.
3. Landed the next aligned-cover brick, axiom-clean:
   - `AllowedWordBlock` removes exactly the forbidden block from the
     `b^|w|`-element one-block alphabet;
   - `AlignedMissingWordPrefix` has exact cardinality
     `(b^|w|-1)^q`, and `alignedPrefixWord_block_ne` verifies the flattened
     digit word avoids `w` in every aligned block;
   - `circleClosedWordCylinder` and `circleAlignedPrefixCylinder` have the
     kernel-checked mesh bound `ediam ≤ b^(-q|w|)` via the 1-Lipschitz
     quotient map `ℝ → ℝ/ℤ`.

## Exact verification run

- `lake env lean src/NormalNumbers/Disjunctive.lean` — passed.
- Guarded `#print axioms NormalNumbers.IsNormal.isDisjunctive` —
  `[propext, Classical.choice, Quot.sound]`.
- `lake build` after the API checkpoint — passed, 8765 jobs.
- Pre-commit build for `b755fd5` — passed, 8765 jobs.
- `lake env lean src/NormalNumbers/QuadraticDisjunctive.lean` — passed.

- Guarded `#print axioms` for
  `isClosed_circleMissingWordSubshift`,
  `mapsTo_circleMap_circleMissingWordSubshift`,
  `mem_circleMissingWordSubshift_of_not_occursAt`,
  `dimH_lt_one_of_finite_covers`, `missingWordExponent_lt_one`, and the D3
  assembly — each returned exactly
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake build` with the new aggregator import — passed, 8766 jobs.
- `lake env lean src/NormalNumbers/QuadraticDisjunctive.lean` after the aligned
  prefix/cardinality/cylinder brick — passed.
- Guarded `#print axioms` for `card_allowedWordBlock`,
  `card_alignedMissingWordPrefix`, `alignedPrefixWord_block_ne`,
  `lipschitzWith_coe_disjunctiveCircle`,
  `ediam_circleClosedWordCylinder_le`, and
  `ediam_circleAlignedPrefixCylinder_le` — each returned exactly
  `[propext, Classical.choice, Quot.sound]`.
- Full `lake build` after that brick — passed, 8766 jobs.

## Current blocker

`MissingWordSubshiftDimensionBound b` is intentionally uninhabited and is the
only missing premise between `QuadraticHypothesisM b` and the exact documented
D3 conclusion.  It is not a disguised disjunctivity statement: it explicitly
says that each closed circle set avoiding one nonempty valid word has
Hausdorff dimension below one.

The mathematical route is fixed.  For `L = |w|`, the nonendpoint part is now
covered by exactly `(b^L-1)^q` aligned closed cylinders of diameter at most
`b^(-qL)`.  The remaining subtlety is genuine: `circleMissingWordSubshift`
avoids an **open** cylinder so it is closed, hence a point whose aligned orbit
lands exactly on a cylinder boundary is not represented by the naïve
forbidden-symbol count.  Add the relevant b-adic grid points as singleton
covers (their `d`-cost is zero), prove the resulting cover, then show the
geometric non-singleton cost tends to zero for an exponent strictly between
`log(b^L-1)/(L log b)` and `1`.

## Next highest-value attack

Prove the endpoint-safe cover dichotomy at scale `q`: every point in
`circleMissingWordSubshift b w` either has all `q` aligned canonical blocks
different from `w` (hence belongs to one landed
`circleAlignedPrefixCylinder`) or one aligned orbit hits the lower boundary
of the open word cylinder (hence is a b-adic grid point).  Index all grid
points at depth `qL` by a finite type and cover them by singletons.  Then
evaluate the finite Hausdorff sum and close its geometric limit before
applying `dimH_lt_one_of_finite_covers`.

Do not touch the two known-false `CFScheduleA.lean` sorries.  Do not mark D3
complete until `QuadraticHypothesisM b` alone yields every quadratic
irrational `b`-disjunctive and guarded axioms show only the trust triple.

## Final checkpoint

The D3 brick, docs, status, and this handoff are committed together in the
green checkpoint immediately following `b755fd5`; inspect `git log -1` for its
hash.  The full-build and guarded-axiom receipts are recorded above.
