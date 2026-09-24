# KICKOFF 2026-09-24 — PairDecouple, the REFUTATION direction

Worktree `~/src/nn-pd-refute`, branch `wip/pd-refute`.  Opus/low.  Target
`src/NormalNumbers/PairDecoupleRefute.lean`: `not_pairDecouple_all`.  A sibling run attacks the
positive statement.  Ren's prior: ~85% PairDecouple is TRUE.  A clean "no counterexample found,
here is why each attack fails" is a success; so is a refutation.

## The swing

1. **Probe `pairDefect` numerically** (exact ω by sieve, `N` up to `10^7`): for `b = 3, 4`,
   `m = 1`, small primes `p ≠ q` (including `p` or `q ≤ P`), `P = 2, 3, 5, 7`.  Plot the defect
   against `R`: decaying, flat, or growing?  A known-answer control is mandatory, e.g. a
   `Q`-periodic function, whose defect is exactly 0.
2. **Hunt for local obstructions**, frozen-statement edge cases first: `P` with `p ≤ P`
   (`p ∣ Q`); shifts `k` with `p ∣ 1+k` (then `p ∣ pn+1+k` for every `n`); `p, q` with
   `q·k ≡ p·k'`, so the two forms share a prime for every `n` in a class; the `R`-indexing of
   `progMean` against `fullMean` over `Q·R` terms; `n = 0` terms.  A frozen statement that is
   FALSE AS STATED (a boundary case) is a first-class finding: prove the counterexample in Lean.
3. If nothing breaks, write up WHY each obstruction fails (the CRT reason), with the probe numbers.

## Rules
- The target theorem is RATIFIED.  Never delete, rename or weaken it; an open named `sorry` is an
  acceptable end state.  Never edit existing files' statements (`SwingC1*.lean`, `CastingOut*.lean`,
  `Maze.lean`), `papers/`, `agent-mail/`, other KICKOFFs.  New helpers go in `src/NormalNumbers/PairDecouple*.lean`.
- Probes go in `probes/` (uv shebang) with a hand-computed known-answer check.
- Read first: `HANDOFF-2026-09-24-swing-c1-laps32-35.md` (defs, the refuted truncation route,
  the lap-33 variance finding), `SwingC1Decouple.lean`, `SwingC1CRT.lean`.  Also read the C3
  swing's Leaf B (`wip/swing-c3`, `git-ro show wip/swing-c3:src/NormalNumbers/SwingC3Rotation.lean`),
  the same "large primes decouple from the small-prime class" shape.
- Build `lake build NormalNumbers.<your module>` (warm tree; never run `lake exe cache get`).  Commit each
  green step.  Each HANDOFF names the crux and gives a confidence that PairDecouple is TRUE.
