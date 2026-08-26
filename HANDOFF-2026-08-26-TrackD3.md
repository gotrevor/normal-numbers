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
4. Closed the endpoint-safe finite-cover obstruction:
   - `orbit_eq_wordCylinder_left_of_occursAt_of_not_mem_open` isolates the
     only way a canonical forbidden block can survive open-cylinder
     avoidance;
   - `exists_mem_circleAlignedPrefixCylinder_of_avoids_boundary` covers the
     nonendpoint branch by the exact aligned alphabet;
   - `eq_circleBadicGridPoint_of_orbit_eq_wordCylinder_left` proves an
     exceptional aligned boundary hit is torsion and hence a depth-`q|w|`
     b-adic grid point;
   - `circleMissingWordSubshift_subset_iUnion_missingWordCoverSet` gives the
     full finite cover by aligned cylinders plus grid singletons, and
     `ediam_missingWordCoverSet_le` proves its mesh bound.  The singletons
     have zero Hausdorff cost, so they do not spoil the entropy exponent.
5. Discharged the remaining Hausdorff-cost limit and exact D3 wrapper:
   - `missingWordCoverCost_le` splits the endpoint-safe `Sum` cover, erases
     the singleton half at positive exponent, and bounds the aligned half;
   - `missingWordCoverGeometric_eq`, `missingWordMesh_tendsto`, and
     `missingWordCostRatio_lt_one` turn that bound into a decaying geometric
     sequence at any exponent above `log(b^L-1)/log(b^L)`;
   - `missingWordSubshiftDimensionBound` chooses the midpoint exponent below
     one and proves the independent missing-word Hausdorff-dimension theorem;
   - `quadratic_irrationals_disjunctive_of_hypothesisM` now proves the exact
     documented implication from `QuadraticHypothesisM b` alone.

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
- `lake env lean src/NormalNumbers/QuadraticDisjunctive.lean` after the full
  endpoint-safe cover — passed.
- `lake build NormalNumbers.QuadraticDisjunctive` — passed, 8716 jobs.
- Guarded `#print axioms` for
  `orbit_eq_wordCylinder_left_of_occursAt_of_not_mem_open`,
  `exists_mem_circleAlignedPrefixCylinder_of_avoids_boundary`,
  `eq_circleBadicGridPoint_of_orbit_eq_wordCylinder_left`,
  `ediam_missingWordCoverSet_le`, and
  `circleMissingWordSubshift_subset_iUnion_missingWordCoverSet` — each
  returned exactly `[propext, Classical.choice, Quot.sound]`.
- Full `lake build` after the endpoint-safe cover and documentation update —
  passed, 8766 jobs.
- `lake env lean GuardD3.lean` after the completed Hausdorff-cost proof —
  passed; guarded `#print axioms` for `IsNormal.isDisjunctive`,
  `missingWordSubshiftDimensionBound`, and
  `quadratic_irrationals_disjunctive_of_hypothesisM` each returned exactly
  `[propext, Classical.choice, Quot.sound]`.
- Final `lake build` after the exact D3 theorem and aggregator import —
  passed, 8766 jobs.

## Current blocker

None for the boxed Track D objective.  The named M_b hypothesis remains a
mathematical hypothesis, as intended; the implication demanded by D3 and its
independent missing-word geometric input are both proved without `sorry` or
extra axioms.

## Next highest-value attack

The supervisor may choose the next roadmap track.  Preserve the completed D3
API and do not touch the two known-false `CFScheduleA.lean` sorries.

## Final checkpoint

The initial D3 reduction is `166b2f5`, the aligned alphabet/cylinder brick is
`04f398d`, and the endpoint-safe full finite cover is `ac66b92`.  The final
Hausdorff-cost theorem, exact wrapper, documentation, and this completion
receipt are the next green commit.  Full-build and guarded-axiom receipts are
recorded above.
