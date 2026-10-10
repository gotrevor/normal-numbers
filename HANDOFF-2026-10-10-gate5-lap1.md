# HANDOFF 2026-10-10 — operator gate 5, lap 1: wiring PROVED; kill test FIRED (scheme level)

Branch `proof/uniformbad-threshold`, HEAD f6297030 (green).

- (0) prework done: exact3.c `A<<F` -> `A*ONE`; UBSan xfail removed (verified with trap-mode UBSan;
  the box has no ubsan runtime; host should run `exact3-review test` once).
- (3) wiring PROVED: `Tail.tailBudgetSuffices449` (UniformBadTailWiring: coreDeletionRecurrence449,
  mass_pos_of_budget, exists_limit, weak_avoid; `Coherent.wq_grow`).  `cStar_le_449` rests only on
  `tailChargeBudget449` (sorry).
- Split: `UniformBadTailSplit` (lossIn, loss_le_split, SplitChargeBudget449 -> crux).
- (1)/(2) measurement + kill test: see `UniformBadTailObstruction.lean` docstring and Maze row
  "Per-ancestor sup charging ...".  Totals pass (0.230, 0.210); every per-ancestor sup scheme
  fails at gamma=(17/10)^6 (655 / 226.5 / 174.4 / 81.7).  Mechanism `childConcentration_18`
  (sorry, waived: exact finite fact).  Reopen: `TailTotalsBound449` (-> crux, proved).
- ON-LINE-REQUEST.md: operator decision on structural fix (fold 5..7 into core vs averaging).

## Next
Awaiting operator.  Off-decision leaf: prove `childConcentration_18` by evaluation.

## BLOCKER (box stuck, strike 1) — for the fresh lap to verify fast
- WHAT: `Tail.tailChargeBudget449` (the only sorry under `cStar_le_449`).
- WHY operator-gated: DIRECTION.md gate 5 step (2) says: if bases 5-7 exhaust the budget, state the
  obstruction in Lean, add a Maze row, write ON-LINE-REQUEST.md and STOP; the structural fix (fold
  bases into the core) is the operator's call.  Done: `UniformBadTailObstruction.lean`, Maze row,
  ON-LINE-REQUEST 2026-10-10 entry.  Verify: `grep -A6 "bases 5..7, n <= 7" scripts/cstar_models/
  tail5_out/peranc_b7_n7_*.txt` (all FAIL vs 9.874655).  Retuning gate-4 weights is forbidden.
- NEED from operator: choose (a) a gate-4-style core certificate including base-5..7 phases, or
  (b) an averaging route to `TailTotalsBound449`; or relabel the kill-test threshold.
