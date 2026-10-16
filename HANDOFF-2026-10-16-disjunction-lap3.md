# Disjunction Lean lap 3 (2026-10-16): kickoff complete

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Review verdict

The lap reconstructed the active route from the frozen declarations, source, report, recent commits,
status, pending work, and the lap-2 handoff.  The Part 2 reduction was faithful: the only dependency
of `not_isSimplyNormal_stoneham_sum` was the ratified digit window, and the statement of
`digitOf_stoneham_sum_eq_zero` is character-identical to its introduction in `ebbe9975`.

The proposed integer-block route reaches the statement for every `k`, including `k = 0`; no endpoint
repair was needed.  The kickoff's three Part 1 declarations and required Part 2 declaration are now
all proved.  No binding objective remains.

## Concrete advance

- Proved `NormalNumbers.digitOf_stoneham_sum_eq_zero` without changing its statement.
- Formalized the load-bearing arithmetic and analytic pieces as public lemmas:
  - `three_pow_succ_dvd_two_pow_three_pow_add_one`: LTE gives
    `3^(k+1) | 2^(3^k) + 1`.
  - `stoneham_sum_eq_tsum` and `stonehamSumTerm_scaled_eq_block`: the paired series is a sum of
    integer binary blocks after scaling.
  - `stonehamSumTerm_shift_le` and `stonehamSumTerm_scaled_lt_half`: the post-window tail is
    nonnegative and strictly below one after scaling.
  - `stoneham_sum_mem_Ico`: the sum lies in `[0,1)`, so the repository's canonical `digitOf`
    convention reads it directly.
- Consequently `NormalNumbers.not_isSimplyNormal_stoneham_sum` is axiom-clean with no further edit:
  the forced zero interval `[2*3^k, 3^(k+1))` contradicts limiting zero frequency `1/2`.
- Removed the now-obsolete `digitOf_stoneham_sum_eq_zero` waiver from `BarrierAudit`; the theorem is
  checked as proved rather than hidden as accepted proof debt.

## Exact verification

```text
lake env lean src/NormalNumbers/StonehamSums.lean
```

Succeeded.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.StonehamSums \
  --import NormalNumbers.StonehamSums \
  --axioms NormalNumbers.digitOf_stoneham_sum_eq_zero
```

Verdict: `FORMALIZE-TIER GREEN`; axioms exactly
`[Classical.choice, Quot.sound, propext]`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.StonehamSums \
  --import NormalNumbers.StonehamSums \
  --axioms NormalNumbers.not_isSimplyNormal_stoneham_sum
```

Verdict: `FORMALIZE-TIER GREEN`; axioms exactly
`[Classical.choice, Quot.sound, propext]`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --import NormalNumbers.StonehamSums \
  --axioms NormalNumbers.not_isSimplyNormal_stoneham_sum
```

Verdict: `FORMALIZE-TIER GREEN`; the full build completed successfully (10,852 jobs), the headline
axioms were exactly `[Classical.choice, Quot.sound, propext]`, and the audit reported
`34 barriers (26 proved, 6 cited, 2 frozen); 25 cruxes linked, 77 waived, 104 open sorries scanned`.

## Current blocker / next highest-value attack

None for the binding kickoff: its done condition is met.  The optional stretch order, if a later
campaign reopens it, is:

1. prove `isNormal_two_stonehamAlpha_four_three` by generalizing the existing Stoneham theorem from
   base `2` to base `4` and descending normality from base `4` to base `2`;
2. encode report rows R1--R6 and the Rauzy disjunction in `Maze.lean`, with R3/R5 linked to
   `not_isSimplyNormal_stoneham_sum` and corresponding `MazeAudit` updates;
3. attempt the conditional Bailey--Crandall consequence only if a generic BBP-to-`bcOrbit` bridge
   is first found.

Those are stretch items, not residual proof debt on this kickoff.

## Completion marker

`box done "disjunction kickoff complete: Part 1 and Stoneham sum headline are axiom-clean, full
gate green"` was invoked successfully.  The helper warned that its generic repository-wide
self-stop gate may decline the marker because unrelated source proof debt remains.  This campaign is
the bounded kickoff above: its declared done condition is fully met, so a relaunch should not reopen
this finished objective (the host should use the kickoff-scoped done condition if necessary).
