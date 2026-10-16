# Disjunction Lean lap 2 (2026-10-16): Part 1 complete; Stoneham corollary reduced to digit window

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Concrete advance

- Proved `NormalNumbers.QSpan.exists_pair_qSpan_not_normal` without changing its statement.
  The proof uses the already-proved category theorem `isMeagre_setOf_isNormal`: for every
  nonzero `(c₁,c₂) : ℚ × ℚ`, the continuous linear form
  `(x,y) ↦ c₁x + c₂y` is an open surjection, so the inverse image of the residual set of
  irrational non-normal reals is residual in `ℝ × ℝ`.  The countable intersection over
  `ℚ × ℚ` supplies one pair all of whose nonzero rational combinations are irrational and
  non-normal.  This is stronger and shorter than the proposed supersparse-support construction.
- Completed the kickoff's Part 1 promotion:
  - Maze row "pair-universal mechanism for a normal element of a Q-span": `.frozen` →
    `.kernel`, linked by `hall_qspan_pair_universal`.
  - `Barriers.liouville_pair_qSpan`: `.frozen` → `.proved` (the historical name remains, but
    its description now accurately says Baire-generic rather than Liouville).
  - The IndependenceRelative Maze evidence now records `ternary_line` as proved.
  - `MazeAudit` counts did not move; `BarrierAudit` moved from 25 proved / 3 frozen to 26 proved /
    2 frozen.  The Part 1 proof removes one sorry and the new Part 2 digit window adds one, so the
    authoritative full-build total remains 105 open sorries.
- Opened Part 2 in `StonehamSums.lean` with the three ratified declarations and imported it from
  `NormalNumbers.lean`.
  - `stonehamAlpha_two_three` is proved by definitional equality.
  - Proved the full frequency argument in `not_isSimplyNormal_stoneham_sum` from the digit-window
    theorem: simple normality gives zero frequency near `1/2` at both `2·3^k` and `3^(k+1)`, while
    the forced zero window adds `3^k` zeros and pushes the latter frequency near `2/3`.
  - Thus the sole Part 2 proof debt is `digitOf_stoneham_sum_eq_zero`; the corollary currently
    inherits its `sorryAx` and will become axiom-clean automatically when that window lands.

## Exact verification

```text
lake env lean src/NormalNumbers/QSpanNormal.lean
```

Succeeded; only the explicitly out-of-scope QSpan sorries remain in that module.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.QSpanNormal \
  --import NormalNumbers.QSpanNormal \
  --axioms NormalNumbers.QSpan.exists_pair_qSpan_not_normal
```

Verdict: `FORMALIZE-TIER GREEN`; axioms exactly
`[Classical.choice, Quot.sound, propext]`.

```text
lake build NormalNumbers.MazeAudit
lake build NormalNumbers.BarrierAudit NormalNumbers.StonehamSums
```

Both succeeded before the Part 2 file was added to the audit import.  The final authoritative
full-build audit is recorded below by `lean-green` (34 barriers: 26 proved, 6 cited, 2 frozen;
25 cruxes linked, 78 waived, 105 open sorries scanned).

The final full `lean-green` gate and resulting commit are recorded in the git log for this
handoff checkpoint.

## Current blocker / next highest-value attack

The only live kickoff crux is `NormalNumbers.digitOf_stoneham_sum_eq_zero` in
`src/NormalNumbers/StonehamSums.lean`.

Highest-value route: first prove the exact series regrouping

```text
α₂,₃ + α₄,₃ = Σ' k, ((2^(3^(k+1)) + 1) / 3^(k+1)) · 4^(-3^(k+1))
```

with the quotient integral via LTE (`3^(k+1) ∣ 2^(3^(k+1)) + 1`).  Then split the sum at
`k`, show all earlier blocks become integers after scaling by `2^(i+1)`, and bound the later
tail below `1`; `digitOf` is the parity of the resulting floor.  Reuse the head/tail and floor
pattern in `Stoneham.lean:stonehamState_approx` and `StonehamSixFailure.lean`.

Do not add the report's R1–R6 Maze rows or the optional `α₄,₃` normality theorem until the
digit window and axiom-clean corollary satisfy the required Part 2 gate.
