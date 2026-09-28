# KICKOFF 2026-09-24 — C3 via MRT / log-Elliott (moonshot)

Worktree `~/src/nn-c3mrt`, branch `wip/c3-mrt` (forked from `wip/elliott-port`, so the `lean-proofs-latest` dependency,
the MRT + unit-circle log-Elliott development of `plby/lean-proofs`, is present and built).  Opus/low.
Ratified target: `weylLambertTwist_holds` in `src/NormalNumbers/SwingC3Leaf.lean` (existing, open).
A success is any of: a proof; a proof of the LOG-averaged variant plus a precise statement of what
the natural-density upgrade needs; or an equivalence theorem naming the open problem it is.

## The leaf
`CastingOut.WeylLambertTwist b` (`SwingC3Lambert2.lean`): for every `P, Q, j, h` with `0 < j < Q`,
`(1/N) Σ_{n<N} e(jn/Q) · e(h · b^n · L_P) → 0`, where `L_P = Σ_{p>P} 1/(b^p − 1)`.  The complete-period
version is proved; the L¹-truncation family is refuted (see the swing handoffs on `wip/swing-c3`
and the "Status after the 2026-09-24 swings" section of `CONJECTURES-2026-09-23-casting-out-and-rungs.md`).

## Ren's honest read (≈ 70% that MRT alone does not close it)
`e(h·b^n·L_P)` is, up to boundary carries, `Π_k ζ_k^{ω_{>P}(n+k)}` (compare `phase_digitTrunc` in
`PairDecoupleDigits.lean`): a MULTI-point correlation of the multiplicative functions
`ζ_k^{ω_{>P}}`, twisted by the periodic phase `e(jn/Q)`.  MRT controls one-point sums in short
intervals and, via entropy decrement, TWO-point log correlations (`Erdos67b.unitCircleLogElliott`).
So:
1. **Decide the shape first.**  Write the truncation-depth-`K` version of the leaf as a `2K`- or
   `K`-point correlation (reuse `PairDecoupleDigits`), and determine whether the twist `e(jn/Q)`
   with `j ≠ 0` gives cancellation by periodicity ALONE (a CRT / residue-class argument, as in
   `PairDecoupleBand.lean`, where bounded prime bands decouple exactly), leaving only large primes.
2. **K = 1 in log density**: `(log-avg) e(jn/Q) ζ^{ω_{>P}(n+1)} → 0`.  A one-point twisted sum of a
   multiplicative function against a periodic phase: expand `e(jn/Q)` in Dirichlet characters mod
   `Q'`; each piece is `Σ χ(n) ζ^{ω(n)}`, a Delange/Halász-type mean (the repo proves Delange:
   `DelangeSlot*`, `TwoPointDelange*` on `wip/twopoint-avg`).  This may be provable NOW in natural
   density without MRT; if so it is the first rung.
3. **K ≥ 2**: needs Elliott for `K` points; state the precise log-averaged multi-point statement
   needed and whether Tao–Teräväinen (odd-order log-Elliott) covers it.  Name it as a `Prop`.
4. Probes: stdlib-only Python in `probes/`, known-answer checked.

## Rules
- Ratified: never delete, rename or weaken `weylLambertTwist_holds` or `conjC3`.  Never copy dependency files into the repo; never edit
  `Maze.lean`, other files' statements, `papers/`, other KICKOFFs.  New code in
  `src/NormalNumbers/C3Mrt*.lean`; files importing `lean-proofs-latest` modules must not be imported by the
  `NormalNumbers` root (PNT+ name collisions with `src/PNTPort`).
- Build `lake build NormalNumbers.<module>` (warm tree; never `lake exe cache get`).  Commit each green step.
- HANDOFF `HANDOFF-c3mrt-<date>-lapN.md`: the crux, this lap's advance, confidence the leaf is TRUE
  and PROVABLE with known techniques.
