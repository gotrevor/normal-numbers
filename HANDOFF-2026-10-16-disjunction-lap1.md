# Disjunction Lean lap 1 (2026-10-16): objectives 1 and 2 proved

Binding kickoff: `KICKOFF-2026-10-16-disjunction-lean.md`.

## Concrete advance

- Proved `NormalNumbers.IndependenceRelative.ternary_line` without changing its statement.
  The proof uses `Adder.carryTG`/`carryG_column` rather than adding a new infinite-expansion
  bridge.  Once all three forbidden digits are absent, the `Y-X` borrow is in `{-1,0}`; it can
  switch from `0` to `-1` at most once.  On either constant tail, a second bounded carry for
  `Y-2X`, with three-column lookahead to exclude transient noncanonical expansions, makes its
  ternary digits eventually constant.  `Adder.not_irrational_of_periodic_digits_g` contradicts
  the irrationality hypothesis.
- Proved `NormalNumbers.IndependenceRelative.exists_counterexample_on_line` without changing its
  statement.  The witness is `Mahler.bgLiouville 3 0 1` and twice that number.  Two instances of
  `Mahler.mahler_lower_bound_bg_digit` certify that the first omits ternary digit `2` eventually
  and the double omits digit `1` eventually; irrationality comes from
  `Mahler.irrational_bgLiouville`.
- Consequently `pi_e_disjunction` is now sorry-free through `ternary_line`.

## Exact verification

```text
lake env lean src/NormalNumbers/IndependenceRelative.lean
```

Succeeded; the sole remaining sorry warning in that module is the explicitly out-of-scope
`not_isRelativeBlock_small`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction \
  --target NormalNumbers.IndependenceRelative \
  --import NormalNumbers.IndependenceRelative \
  --axioms NormalNumbers.IndependenceRelative.ternary_line \
  --axioms NormalNumbers.IndependenceRelative.exists_counterexample_on_line
```

Verdict: `FORMALIZE-TIER GREEN`.  Both declarations print exactly
`[Classical.choice, Quot.sound, propext]`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-disjunction
```

Verdict: `FORMALIZE-TIER GREEN` after the complete 10,851-job `lake build`.  The barrier audit
reports 34 barriers (25 proved, 6 cited, 3 frozen), 25 linked cruxes, 77 waivers, and 105 open
sorries scanned.  The obsolete waivers for the two theorems proved in this lap were removed.

## Current blocker / next highest-value attack

Objective 3, `QSpan.exists_pair_qSpan_not_normal`, is the remaining in-scope theorem.  The target
module's supersparse-support English proof still lacks its digit-periodicity infrastructure.
There is a second promising route already formalized downstream in `QSpanCriterion.lean`:
`ae_not_qSpanNormal_fiveDigits` proves no normal rational combination for an almost-everywhere
pair in base 10, but that file imports `QSpanNormal` and does not supply the required rational
independence or arbitrary-base statement.  The next lap should first decide whether to extract
and generalize the measure construction into a prerequisite module (adding the a.e. rational
independence lemma), or formalize the kickoff's sparse support construction directly.  Do not
perform Maze promotion until objective 3 is proved.

## Files changed

- `src/NormalNumbers/IndependenceRelative.lean`
- `src/NormalNumbers/BarrierAudit.lean`
- `HANDOFF-2026-10-16-disjunction-lap1.md`
- pointer/status files updated for this lap
