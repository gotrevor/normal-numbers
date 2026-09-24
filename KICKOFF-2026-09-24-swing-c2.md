# KICKOFF 2026-09-24 — swing at C2 (Erdős–Borwein disjunctive)

Worktree `~/src/nn-c2`, branch `wip/swing-c2`.  Opus/low.  Target file `src/NormalNumbers/SwingC2.lean`.

## The swing

The G4 disjunctivity proof (`isDisjunctive_base`, `G4SchedBAssembly.lean`) uses the weight `ω` in
five places (audited 2026-09-14, DIRECTION.md "campaign G5"): `PrimeLambertDefs/Tail`,
`G4Transport`, `G4Remainder`, `G4FarTail`, `G4LocalContraction` + `G4SmallPrimeVector`.  `d(n)` is
MULTIPLICATIVE, not additive: `d(pm) = d(m)·(v_p+2)/(v_p+1)`, and `d` is unbounded like `2^{ω}`.
1. **Decisive audit first, before any port.**  For each of the five places, decide whether
   it survives for `d`.  Write the verdict per place in a DESIGN note, with a probe where it's
   numeric.  The transport identity and the local contraction (C2) are the likely breaks.
2. If one place breaks, freeze the precise replacement lemma the proof would need as a named
   leaf and try it.  A precise obstruction ("additivity is load-bearing at X because Y") is a
   full success for this swing.
3. Only if all five survive, start the port bottom-up (copy the base-b template, green at each
   step).  An easier first instance is welcome: large `b`, or `b` of a special form.

## Rules (moonshot lane)

- **A lap succeeds by advancing the crux, and a refutation counts as an advance.**  Break the fat
  `sorry` into NAMED leaves (`theorem … := sorry` with a precise statement): more sorries is
  progress.  A leaf that resists stays a named sorry IN `src/`.  Never relocate it and never
  weaken a statement.
- The frozen Props in `CastingOut.lean` (`ConjC1/C2/C3`, `CastLaw`, `IsRich`, `normalCastLaw`, …)
  are RATIFIED.  Never edit `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`,
  `Maze.lean`, `papers/`, `agent-mail/`, or other KICKOFFs.  Work in `src/NormalNumbers/SwingC2.lean` plus new helper files
  `src/NormalNumbers/SwingC2*.lean`.
- **Probe before building.**  Python probes go in `probes/` (uv shebang), with a hand-computed
  known-answer check in the same file.  A probe that kills a route is a deliverable: write it up
  in the HANDOFF with the exact counterexample regime.
- Named hypotheses are fine.  A conditional theorem `conjC2_of_H : H → …` with `H` a precise,
  literature-checkable arithmetic statement IS the swing's main target.  Never use `axiom`.
- Math context: `CONJECTURES-2026-09-23-casting-out-and-rungs.md`.  Read the Maze
  (`src/NormalNumbers/Maze.lean`) before proposing a route: it lists ~120 closed halls.
- Build: `lake build NormalNumbers.SwingC2` (warm tree; never run `lake exe cache get`).  Proof tier:
  `native_decide` and boosts are fine.  Commit each green step.  Each lap's HANDOFF says what the
  crux IS now: which leaf, what it needs, and whether that is known, open, or refuted.

## ⚠️ ADDENDUM (Ren, 2026-09-24): never delete a ratified theorem

The swing's ratified theorems (the headline `conj…` and every `theorem` in the seeded stub) must
STAY in the file until proved.  Deleting, renaming or re-stating one to make the file sorry-free is
a failure, not completion (the c1log swing did this and was reverted).  An open headline is the
expected end state of a moonshot swing.  Put conditional versions (`…_of_H`) BESIDE it, and keep
the headline as a `sorry`.
