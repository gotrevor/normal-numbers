# KICKOFF 2026-09-24 — swing at C1 in logarithmic density

Worktree `~/src/nn-c1log`, branch `wip/swing-c1log`.  Opus/low.  Target file `src/NormalNumbers/SwingC1Log.lean`.

## The swing

Logarithmic averaging is where the published Elliott results live: Tao 2016, the two-point
logarithmic Chowla/Elliott; Tao–Teräväinen 2019, odd-order and "structure of logarithmically
averaged correlations".
1. `castLawLog_of_castLaw` (partial summation): a warm-up, prove it.
2. `castLawLog_one` is the first real rung.  Work out EXACTLY which log-correlations of
   `z^{ω}` (z a root of unity) at consecutive integers the L = 1 statement needs, including the
   carry `c_n`, which involves ω(n+1), ω(n+2), ….  Is it a 2-point statement, or K-point with
   K → ∞?  Freeze the needed input as a named hypothesis whose statement matches a published
   theorem as closely as possible.  Cite the theorem and the precise hypotheses it needs
   (non-pretentiousness of `z^ω`: prove THAT part in Lean if it is elementary).
3. Prove `castLawLog_one_of_H`, then `conjC1Log_of_H`.  If the needed input is NOT covered by the
   published odd/two-point results, say exactly why (which parity or which K); that verdict is
   the deliverable.

## Rules (moonshot lane)

- **A lap succeeds by advancing the crux, and a refutation counts as an advance.**  Break the fat
  `sorry` into NAMED leaves (`theorem … := sorry` with a precise statement): more sorries is
  progress.  A leaf that resists stays a named sorry IN `src/`.  Never relocate it and never
  weaken a statement.
- The frozen Props in `CastingOut.lean` (`ConjC1/C2/C3`, `CastLaw`, `IsRich`, `normalCastLaw`, …)
  are RATIFIED.  Never edit `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`,
  `Maze.lean`, `papers/`, `agent-mail/`, or other KICKOFFs.  Work in `src/NormalNumbers/SwingC1Log.lean` plus new helper files
  `src/NormalNumbers/SwingC1Log*.lean`.
- **Probe before building.**  Python probes go in `probes/` (uv shebang), with a hand-computed
  known-answer check in the same file.  A probe that kills a route is a deliverable: write it up
  in the HANDOFF with the exact counterexample regime.
- Named hypotheses are fine.  A conditional theorem `conjC1Log_of_H : H → …` with `H` a precise,
  literature-checkable arithmetic statement IS the swing's main target.  Never use `axiom`.
- Math context: `CONJECTURES-2026-09-23-casting-out-and-rungs.md`.  Read the Maze
  (`src/NormalNumbers/Maze.lean`) before proposing a route: it lists ~120 closed halls.
- Build: `lake build NormalNumbers.SwingC1Log` (warm tree; never run `lake exe cache get`).  Proof tier:
  `native_decide` and boosts are fine.  Commit each green step.  Each lap's HANDOFF says what the
  crux IS now: which leaf, what it needs, and whether that is known, open, or refuted.
