# Kickoff 2026-10-16: discharge three disjunction-shelf sorries

Branch `proof/disjunction-lean`, worktree `~/src/nn-disjunction`.  The attended session ratified
the three statements below as they stand; prove them **without changing any statement**.

## Objectives, in order

1. **`IndependenceRelative.ternary_line`** (`src/NormalNumbers/IndependenceRelative.lean`).
   The English proof is in its docstring: assume all three avoidances past some position, track
   the borrow sequence `c ∈ {−1, 0}` of `Y − X` from deep to shallow, show a `0` borrow propagates
   upward, and conclude `Y − 2X` is rational in both cases.  Mind the digit convention: `DigitIO`
   reads the canonical expansion of the fractional part, so negative `Y − X` and dyadic-style
   double expansions need a lemma relating digits of `frac (Y − X)` to the borrow arithmetic.
   When this lands, `pi_e_disjunction` becomes sorry-free for free.
2. **`IndependenceRelative.exists_counterexample_on_line`**: `X = Σ 3^{-k!}`, `Y = 2X`.
3. **`QSpan.exists_pair_qSpan_not_normal`** (`src/NormalNumbers/QSpanNormal.lean`).  The English
   construction is in its docstring (supersparse disjoint supports `(2k)!`, `(2k+1)!`; between
   support points every span element's digits are those of a rational of denominator `q`, hence
   periodic with period `≤ q`; a block outside the periodic ones has frequency → 0 along the
   support times).  Reuse the repo's existing machinery: grep for factorial-support / Liouville
   constructions (`Barriers`, `CantorLiouville`, `CantorRepetition`) and `isNormal_rat_mul_add`
   before writing new digit lemmas.

**Out of scope:** `not_isRelativeBlock_small` (65%, may be false), `qSpanNormal_sqrt_two_sqrt_three`
(open problem), `span_dimension_budget`, `exists_pair_exponentTwo_qSpan_not_normal`.  Leave them
sorried.

## If a statement is false

Do not weaken it.  Prove the negation in a new theorem next to it (a counterexample is a result),
leave the original sorried with a docstring note, and `box stuck` with the witness.

## After objective 3: Maze promotion

- `Maze.lean` row "pair-universal mechanism for a normal element of a Q-span": tier `.frozen` →
  `.kernel`, add an `alias hall_… := QSpan.exists_pair_qSpan_not_normal` in §2, and drop
  "(sorry, 90%)" from its evidence string.
- `Barriers.lean` `liouville_pair_qSpan`: `.frozen` → `.proved` if that constructor's signature
  allows it (mirror `perStage_dead_not_enough`).
- `IndependenceRelative` row (dated 2026-10-05): drop nothing, but `ternary_line` is now proved,
  so note it in the evidence string.
- Update `#guard_msgs` counts in `MazeAudit.lean` if they move.

## Done when

All three named theorems print only `[propext, Classical.choice, Quot.sound]` under
`#print axioms` (use `lean-axiom-gate` if present in the box), `lake build` is green, and the Maze
edits compile.  Then `box done`.
