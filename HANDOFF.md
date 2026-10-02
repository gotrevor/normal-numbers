# HANDOFF — pointer

This is a thin pointer, not an overview.  Read, in order:

1. **`DIRECTION.md` → CURRENT DIRECTIVE** — binding, altitude-owned, outranks every baton.
2. **`STATUS.md`** — the living overview (refreshed on review laps).
3. **The newest dated baton**: `HANDOFF-2026-10-02-master-lap1.md` (master conjectures).
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
