# BRIEF — close `UniformTV.lean`

## Goal

Discharge the three remaining `sorry`s in `src/NormalNumbers/UniformTV.lean`.
Nothing else in the repo is in scope.  Done gate: that file is sorry-free and
its declarations are axiom-clean (standard three).

## Frozen — do not restate, weaken, or rename

`UniformDigitTV`, `isNormal_of_uniform_digitTV_pow`, and
`isAbsolutelyNormal_of_uniformDigitTV` are frozen as written.  If a statement
looks unprovable, that is a finding to record in a handoff, not a licence to
edit the statement.  No new axioms.  No `native_decide`.

## Already proved and axiom-clean (do not redo)

* `digitTV_diag_eq`
* `abs_expectation_sub_le_two_mul_digitTV` — total variation controls any
  `[0,1]`-valued statistic of a digit.  This is the workhorse for item 1.
* `simplyNormal_iff_digitTV_tendsto`

## Item 1 — `isNormal_of_uniform_digitTV_pow` (the engine)

The mathematical content is a *uniform* Pillai.  `Pillai.lean` already holds
the whole skeleton; reuse it rather than rebuilding.

Route:

1. Fix a block `w` of length `m` and `ε > 0`.  Choose the exponent `r` large
   enough that the straddling term is below `ε / 2`, then choose the sampling
   ratio `L` from the hypothesis so the histogram term is below `ε / 2`.
   Note the order: `r` first, then `L`.  `r` must not depend on `L`.
2. A base-`b ^ r` digit is an aligned length-`r` block of base-`b` digits:
   `digitOf_pow_eq_blockNatVal`, with `digitOf_pow_slice_eq_blockNatVal` for
   the slice form.
3. Occurrences of `w` at a fixed phase inside one `b ^ r` digit are counted by
   `card_matchingValues`.  Normalise that count by `r - m + 1` to land in
   `[0,1]` and feed it to `abs_expectation_sub_le_two_mul_digitTV`.  This is
   the step that replaces `phaseWindowFreq_tendsto`: the same conclusion, but
   from an `ε`-bound uniform in `r` rather than a limit at fixed `r`.
4. Boundary-straddling occurrences are already bounded by
   `card_straddling_phases`; combine via `windowCount_eq_sum_phaseCount` and
   the sandwich in `windowCount_div_sandwich`.
5. Conclude `IsNormalSequence b (digitOf b (Int.fract x))`, matching how
   `pillai` closes at `Pillai.lean:846`.

Watch: `IsNormal` is stated through `Int.fract x`, so the reduction to
`y ∈ Set.Ico 0 1` must happen before the digit work, exactly as `pillai` does.

## Item 2 — `isAbsolutelyNormal_of_uniformDigitTV`

Should be short once item 1 lands: unfold `IsAbsolutelyNormal`, fix `b ≥ 2`,
and specialise `UniformDigitTV` along the powers `b ^ r` to produce item 1's
hypothesis.  The only real step is turning "for all bases beyond `B`" into
"for all exponents beyond `K`", which needs `b ^ r ≥ B` for `r` large.

## Item 3 — `exists_schedule_digitTV_tendsto_not_isNormal` (the ONLY remaining sorry)

⚠️ A previous lap DELETED this theorem instead of proving it.  That is now blocked by
`--require-decls`, and it was never acceptable: **if a frozen statement looks unprovable, say so
in a handoff.**  Removing it is not a route.

**Route VERIFIED 2026-08-26 (Baire, not measure).**  Do not attempt the probabilistic
construction (random digits with forced zero blocks + Borel-Cantelli); it is an expedition and
it is not needed.  Every piece already exists in this repo:

| Need | Use |
|------|-----|
| non-normality in every base, for free | `NormalMeager.isMeagre_setOf_isNormal`, and the assembled `exists_absolutelyDisjunctive_forall_not_isNormal` shows the exact assembly idiom |
| a dense open set is residual | `DisjunctiveBaire.residual_of_dense_open` |
| countable intersection stays residual | `Filter.countable_iInter_mem` |
| residual ⇒ a witness exists | `nonempty_of_not_isMeagre (not_isMeagre_of_mem_residual …)` |

Steps:

1. For fixed `b`, `L`, `ε`, show `G b L ε := {x | ∃ N ≥ L * b, digitTV b x N < ε}` contains a
   **dense open** set, and is residual.
2. 🚨 **The friction point, and the only real one.**  `digitTV b · N` is locally constant *off*
   the `b`-adic rationals of level `≤ N`, so `{x | digitTV b x N < ε}` is a finite union of
   half-open intervals and is **not** open as written.  Do **not** weaken the statement over
   this.  Build an explicitly open set contained in it — exactly the move
   `orbitLiftOpen` makes in `DisjunctiveBaire`; copy that pattern rather than inventing one.
   Density is the easy half: the digits beyond any finite prefix are unconstrained.
3. Intersect over `b ≥ B` and over a sequence `ε k → 0` (both countable) with the abnormal
   residual set from `NormalMeager`.  Extract a witness `x`.
4. Build the schedule: for each `b`, choose the largest `k` with `b ≥ B k` and take that
   `∃ N` witness; `Nat.find`/`Classical.choice` over the existentials.  This gives one function
   `N : ℕ → ℕ` with `N b / b → ∞` and `digitTV b x (N b) → 0`, which is the statement.
5. `¬ IsNormal 2 x` falls straight out of the abnormal set's membership.

Sequencing note: step 2 is where laps will be spent.  Do it first and prove it as its own named
lemma; steps 3-5 are plumbing once it holds.

## Anti-goals

Do not touch other modules.  Do not add the module to `src/NormalNumbers.lean`
until it is sorry-free.  Do not repurpose this run for Route A or B6 work.
