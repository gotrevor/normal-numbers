# Maze backlog lap 5 COMPLETE — L2 and final Maze rows (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order.  Parts 1--2 and Part 3/L1 were
complete at the start of this lap.  This lap proves Part 3/L2 and adds the two remaining
declaration-audited Maze rows, so every kickoff done condition is now met.

## Concrete advance

The ratified L2 theorem

```lean
not_isSimplyNormal_three_seven_triple
```

is proved in `NormalNumbers.StonehamSumsBoundary`.  The kernel-checked proof spine is:

- `seven_pow_dvd_stoneham_triple_block`: `7^n` divides
  `Φ₆(3^(7^n)) = 3^(2*7^n) - 3^(7^n) + 1`.  It lifts `729 ≡ 1`, selects the
  `27^(7^n)+1` factor modulo 7, then selects the cyclotomic factor using
  `3^(7^n) ≡ 3 (mod 7)`;
- `stonehamTripleTerm_scaled_eq_block`: the `k`-th term of
  `α₃,₇ - α₉,₇ + α₂₇,₇`, scaled at `3*7^(k+1)`, is exactly the integral block
  `Φ₆(3^(7^(k+1)))/7^(k+1)`;
- positivity, geometric-majorant, summability, and whole-tsum lemmas control the remaining
  tail below one throughout the gap;
- `digitOf_stoneham_three_seven_triple_eq_zero` proves exact 0-indexed ternary zero windows
  `[3*7^(k+1), 7^(k+2))`;
- the headline contradicts the limiting zero frequency `1/3` at the two window endpoints.

The Maze now has the required kernel rows `joint normality is pairwise` (`.refuted`) and
`same-c combinations are normal` (`.falseAsStated`), linked through
`hall_pairwise_joint_normality` and `hall_same_c_combinations_normal`.  `MazeAudit` is now
198 rows / 91 declaration-backed links / 107 legacy rows.

## Verification

```text
lake env lean src/NormalNumbers/StonehamSumsBoundary.lean
```

completed successfully.

```text
lake build NormalNumbers.MazeAudit
```

completed successfully, including the updated `#maze_audit` guard.

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --import NormalNumbers.StonehamSumsBoundary \
  --axioms NormalNumbers.not_isSimplyNormal_three_seven_triple
```

ended `FORMALIZE-TIER GREEN`; the headline axiom list was exactly
`[Classical.choice, Quot.sound, propext]`.

The final full gate

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --import NormalNumbers \
  --axioms NormalNumbers.not_isSimplyNormal_three_seven_triple
```

ended `FORMALIZE-TIER GREEN` after the full 10,858-job build, with the same axiom list.

## Current blocker and next attack

There is no blocker and no remaining item in the binding kickoff.  All three parts are complete,
all seven new Maze rows are declaration-backed, both boundary headlines are proved, and the full
build is green.  The next session should take a new operator objective rather than extend this
completed campaign speculatively.

This is a bounded campaign completion, not a claim that the entire long-running repository is
sorry-free.  `box done` was invoked for the completed kickoff; its generic repo-wide self-stop gate
reported 105 unrelated source sorries and may therefore relaunch unless the host uses a scoped done
condition.  Those obligations predate this branch and are outside `KICKOFF-2026-10-16-maze-backlog.md`.
