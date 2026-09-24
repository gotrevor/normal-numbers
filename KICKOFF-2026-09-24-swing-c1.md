# KICKOFF 2026-09-24 — swing at C1 (natural density)

Worktree `~/src/nn-c1`, branch `wip/swing-c1`.  Opus/low.  Target file `src/NormalNumbers/SwingC1.lean`.

## The swing

Prove `conjC1`, or, far more likely, reduce it EXACTLY.  Known mechanism:
`windowDigitSum_lambert_modEq` gives window sum ≡ Σ_{m∈(n,n+L]} ω(m) + c_{n+L} − c_n (mod b−1).
`c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋` depends on residues of `ω(N+1..N+K)` mod `b^K(b−1)` up to a
truncation error.
1. Freeze `H`: joint equidistribution of `(ω(n+1), …, ω(n+K)) mod Q`.  ⚠️ `ω ≈ log log N` is
   unbounded, so the truncation depth must grow with N: state `H` with the uniformity the proof
   ACTUALLY needs (e.g. `K = K(N) → ∞` slowly, or an explicit error term), not fixed K.
2. Prove the model lemma: iid uniform-mod-`Q` coefficients give iid uniform digits, so their casting-out law is
   `normalCastLaw` (finite, combinatorial).
3. Prove `conjC1_of_H`.  Then `conjC1` is left with exactly one leaf, `H`.
4. Record honestly whether `H` is Elliott's conjecture (open) or weaker.  Check whether the carry
   truncation also needs a size bound on ω (e.g. `ω(n) ≤ log n / log 2`, in the repo:
   `PrimeLambertDefs`).

## Rules (moonshot lane)

- **A lap succeeds by advancing the crux, and a refutation counts as an advance.**  Break the fat
  `sorry` into NAMED leaves (`theorem … := sorry` with a precise statement): more sorries is
  progress.  A leaf that resists stays a named sorry IN `src/`.  Never relocate it and never
  weaken a statement.
- The frozen Props in `CastingOut.lean` (`ConjC1/C2/C3`, `CastLaw`, `IsRich`, `normalCastLaw`, …)
  are RATIFIED.  Never edit `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`,
  `Maze.lean`, `papers/`, `agent-mail/`, or other KICKOFFs.  Work in `src/NormalNumbers/SwingC1.lean` plus new helper files
  `src/NormalNumbers/SwingC1*.lean`.
- **Probe before building.**  Python probes go in `probes/` (uv shebang), with a hand-computed
  known-answer check in the same file.  A probe that kills a route is a deliverable: write it up
  in the HANDOFF with the exact counterexample regime.
- Named hypotheses are fine.  A conditional theorem `conjC1_of_H : H → …` with `H` a precise,
  literature-checkable arithmetic statement IS the swing's main target.  Never use `axiom`.
- Math context: `CONJECTURES-2026-09-23-casting-out-and-rungs.md`.  Read the Maze
  (`src/NormalNumbers/Maze.lean`) before proposing a route: it lists ~120 closed halls.
- Build: `lake build NormalNumbers.SwingC1` (warm tree; never run `lake exe cache get`).  Proof tier:
  `native_decide` and boosts are fine.  Commit each green step.  Each lap's HANDOFF says what the
  crux IS now: which leaf, what it needs, and whether that is known, open, or refuted.
