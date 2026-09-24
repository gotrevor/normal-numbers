# KICKOFF 2026-09-24 — swing at C3 (G4 is rich)

Worktree `~/src/nn-c3`, branch `wip/swing-c3`.  Opus/low.  Target file `src/NormalNumbers/SwingC3.lean`.

## The swing

1. `isRichUpper_of_isRich` warm-up.
2. **Measure first.**  The disjunctivity proof (`G4SchedBAssembly.lean`, `G4Wiring*`,
   `G4Covering`) produces occurrences at designed sample positions.  Determine, from the proof,
   the COUNT of guaranteed occurrences of a word of length ℓ below X.  Is it `≫ X`, `X^{1−o(1)}`,
   or a sparse set?  Also probe numerically how often short words actually occur in `G4_4`.
3. If the proof's count is `≫ X` along a subsequence, `isRichUpper_primeLambertAtBase` may be
   within reach: extract it.  If the count is sparse by design, name the exact place where
   density is lost (a named leaf with the density statement it would need) and say whether that
   leaf is as hard as normality.  That verdict is the deliverable.
3b. Effective disjunctivity (first-occurrence bound `N(b, ℓ)`) is a welcome by-product, since
   DIRECTION.md already names it as a target.

## Rules (moonshot lane)

- **A lap succeeds by advancing the crux, and a refutation counts as an advance.**  Break the fat
  `sorry` into NAMED leaves (`theorem … := sorry` with a precise statement): more sorries is
  progress.  A leaf that resists stays a named sorry IN `src/`.  Never relocate it and never
  weaken a statement.
- The frozen Props in `CastingOut.lean` (`ConjC1/C2/C3`, `CastLaw`, `IsRich`, `normalCastLaw`, …)
  are RATIFIED.  Never edit `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`,
  `Maze.lean`, `papers/`, `agent-mail/`, or other KICKOFFs.  Work in `src/NormalNumbers/SwingC3.lean` plus new helper files
  `src/NormalNumbers/SwingC3*.lean`.
- **Probe before building.**  Python probes go in `probes/` (uv shebang), with a hand-computed
  known-answer check in the same file.  A probe that kills a route is a deliverable: write it up
  in the HANDOFF with the exact counterexample regime.
- Named hypotheses are fine.  A conditional theorem `conjC3_of_H : H → …` with `H` a precise,
  literature-checkable arithmetic statement IS the swing's main target.  Never use `axiom`.
- Math context: `CONJECTURES-2026-09-23-casting-out-and-rungs.md`.  Read the Maze
  (`src/NormalNumbers/Maze.lean`) before proposing a route: it lists ~120 closed halls.
- Build: `lake build NormalNumbers.SwingC3` (warm tree; never run `lake exe cache get`).  Proof tier:
  `native_decide` and boosts are fine.  Commit each green step.  Each lap's HANDOFF says what the
  crux IS now: which leaf, what it needs, and whether that is known, open, or refuted.

## ⚠️ ADDENDUM (Ren, 2026-09-24): never delete a ratified theorem

The swing's ratified theorems (the headline `conj…` and every `theorem` in the seeded stub) must
STAY in the file until proved.  Deleting, renaming or re-stating one to make the file sorry-free is
a failure, not completion (the c1log swing did this and was reverted).  An open headline is the
expected end state of a moonshot swing.  Put conditional versions (`…_of_H`) BESIDE it, and keep
the headline as a `sorry`.
