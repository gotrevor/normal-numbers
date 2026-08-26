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

## Item 3 — `exists_schedule_digitTV_tendsto_not_isNormal` (guardrail)

Prefer the **Baire route over the probabilistic route**.  The measure-theoretic
construction (random digits with forced zero blocks, then Borel-Cantelli) is an
expedition; the category argument looks like a lap, and the repo already has the
machinery:

* `NormalMeager.exists_absolutelyDisjunctive_forall_not_isNormal` supplies a real
  that is normal to no base.
* `DisjunctiveBaire` has the pattern for open-and-dense orbit conditions
  (`isOpen_orbitLiftOpen`, `dense_orbitLiftOpen`, `residual_absolutelyDisjunctive`).

Key observation to exploit: for fixed `b`, `N`, `ε`, the condition
`digitTV b x N < ε` depends on finitely many digits, so it is open away from the
`b`-adic rationals; and `∃ N ≥ L * b, digitTV b x N < ε` is dense, because the
deep digits of a point in any interval are unconstrained.  Intersect over
`b ≥ B` (countably many) and with the residual nowhere-normal set, then apply
Baire.  The witness schedule `N` is read off from the `∃ N` witnesses.

If the openness step fights back at the `b`-adic rationals, that is the expected
friction point; handle it the way `DisjunctiveBaire` handles the analogous
endpoint issue rather than by weakening the statement.

## Anti-goals

Do not touch other modules.  Do not add the module to `src/NormalNumbers.lean`
until it is sorry-free.  Do not repurpose this run for Route A or B6 work.
