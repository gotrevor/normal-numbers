# KICKOFF 2026-09-24 — PairDecouple, the PROOF direction

Worktree `~/src/nn-pd-prove`, branch `wip/pd-prove`.  Opus/low.  Target
`src/NormalNumbers/PairDecoupleProve.lean`: `pairDecouple_all`.  A sibling run attacks the negation.

## The swing

Ren's worry (≈70%): the contribution of prime factors of size `N^{1−o(1)}` makes PairDecouple
imply class-independence of two-form almost-prime counts (`pn+k`, `qn+k'` each with exactly one
large prime factor): Hardy–Littlewood/Chowla-type, open.  Your job is to prove it, or to show
EXACTLY which such statement it needs.
1. Split the prime range: `(P, y]` with `y = N^{o(1)}` (fundamental lemma of the sieve or
   Kubilius, CRT-exact, where class-independence should be provable), and `(y, N]` (each
   `pn+k` has `O(1)` such primes).  Freeze each range's contribution as a named leaf.
2. For the top range, look for a trick that needs only class-INDEPENDENCE, never an asymptotic:
   averaging over `n` in a class against a bijection between classes, the phase being
   `b^{-k}`-weighted (so large `k` are negligible), or `t = m/b` making only `ω` mod `b^j`
   matter.  Also check whether Kátai can be applied with `p, q` LARGE only
   (Bourgain–Sarnak–Ziegler needs just sufficiently large primes), and whether that helps.
3. If a leaf is honestly equivalent to an open problem, state the equivalence as a theorem
   (`leaf_iff_…` or `leaf_of_…` + `…_of_leaf`), name the problem, and stop.  That is a success.

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

## ADDENDUM (Ren, 2026-09-24): the refute run finished; reuse its engine

`wip/pd-refute` found no counterexample (its confidence that PairDecouple is true: 93%) and PROVED
the CRT half.  `PairDecoupleBand.lean` decomposes `pairRemainder b P = bandPairTail b P y +
pairRemainder b y`, and every bounded band `(P, y]` decouples EXACTLY (`classDeviation ≤ 4(R mod
M)/R`, `0` when `M ∣ R`).  So the whole crux is the primes `r ≍ N`.  Cherry-pick or copy
`PairDecoupleBand.lean`, `PairDecoupleLower.lean`, `PairDecoupleAttacks.lean`
(`git-ro show wip/pd-refute:<path>`) instead of re-deriving.  Handoff:
`git-ro show wip/pd-refute:HANDOFF-2026-09-24-pd-refute-lap1.md`.  Probes there are stdlib-only
(no uv/PyPI egress in the box).
