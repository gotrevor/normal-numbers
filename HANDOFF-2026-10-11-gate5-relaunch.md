# HANDOFF 2026-10-11 — operator gate-5 relaunch (one decisive measurement): KILL

Branch `proof/uniformbad-threshold`.  Build green (10851 jobs).

The relaunch's single measurement is done; the kill criterion fired and the box self-stopped.
- Controls held: crude 5.419, drop-5–7 0.695 (closes), zero tail passes, kill-all 1.584 (fails).
- Certified gaps: (i) 4.190, (iii) 4.385, (ii) 2.231, (i)+(ii) 1.725, (i)+(ii)+(iii) **1.391 > 1**.
- Lean: `src/NormalNumbers/UniformBadTailCounting.lean`; Maze row "Refined counting screen for the gate-5 tail"
  (cited in MazeAudit).  Scripts: `scripts/cstar_models/tail5_{runsum,layercake,refined}.py`; outputs
  `tail5_out/{runsum_k20,layercake_k15,refined_screen}.txt`.
- Waiting on the operator: fallback (a) (`ON-LINE-REQUEST.md`, `ROUTE-ESCALATION-2026-10-11.md`).
- Remaining gap is a factor 1.39, all in bases 5–7 long-window edges at lags 2–3.  If the operator prefers not
  to take (a): candidate levers are a lag-dependent K (survivors of a parent that was hit at the previous lag)
  and charging edges to parent MASS rather than count.  Neither is tested.
