# HANDOFF — pointer

This is a thin pointer, not an overview.  Read, in order:

1. **`DIRECTION.md` → CURRENT DIRECTIVE** — binding, altitude-owned, outranks every baton.
2. **`STATUS.md`** — the living overview (refreshed on review laps).
3. **The newest dated baton**: `HANDOFF-2026-10-02-erdos257b2-lap3.md` (Erdős #257 base 2).
   Find it with `ls HANDOFF-*.md | sort -t p -k2 -n | tail -1` (numeric — plain `ls | tail`
   breaks once lap numbers pass 99).
4. **`PENDING_WORK.md`** — the queue and the corrected attack path.
5. `src/NormalNumbers/Maze.lean` — every refuted route, as Lean data.  Read before proposing one.

Earlier batons: `HANDOFF-2026-09-29-2330.md`, `HANDOFF-2026-09-29-2100.md`,
`HANDOFF-2026-09-29-0307.md`, and `archive/handoff/`.

## BLOCKER (2026-10-02, erdos257-base2 run) — operator-gated
Scoped target `sorry-free:src/NormalNumbers/Erdos257Base2.lean` cannot be honestly met:
its only hypothesis `CastingOut.TTEquidistributedCorrelation` is PROVABLY TRUE
(`ttEquidistributedCorrelation_trivially_true`, LiteratureTTEquidistributedDefect.lean; Maze row
"TT 3.1(i) with a Lebesgue-measured exceptional set"), so the frozen headlines are unconditional
base-2 disjunctivity (open). Verify: `#print axioms` on that theorem = trust base.
Ask: operator re-freezes the headline on `CastingOut.TTEquidistributedDyadic`. Details:
HANDOFF-2026-10-02-erdos257b2-lap1.md.
Re-confirmed 2026-10-02 (lap 2): stuck-bail confirmed, treadmill halted for operator.

## OPERATOR RESOLUTION (2026-10-02)
Accepted.  `Erdos257Base2.lean` headlines are re-frozen on `CastingOut.TTEquidistributedDyadic`
(the derivation from TT Thm 3.1(i), with `c/4`, is now in its docstring, 85%).
`TTEquidistributedCorrelation` stays as the recorded vacuous transcription (Maze row).  The stuck
flag is cleared: continue with N3-N8 against the dyadic Prop (N6 now consumes it).

## STUCK-BAIL (2026-10-02, erdos257b2 run, strike 1)
- **What:** this run's operator scope — Erdős #257 base 2 headline axiom-clean — is MET (2d2e70e1).
  Verify: `#print axioms` of `NormalNumbers.Erdos257.{isDisjunctive_subsetLambert_two,
  erdos257_primeSubset, erdos257_residueClass}` = `[propext, Classical.choice, Quot.sound]`.
- **Why stuck:** the repo-wide self-stop gate counts 23 sorries in other lanes (outside the operator's
  scope for this run), so `box done` is declined; no lap in this scope can clear them.
- **Need from operator:** relaunch/stop with `--done-when` scoped to `src/NormalNumbers/Erdos257Base2.lean`
  (or accept done).  Details: `HANDOFF-2026-10-02-erdos257b2-lap5.md`.
Re-confirmed 2026-10-02 (fresh lap): build green, axioms trust-base only; stuck strike 2 recorded.
