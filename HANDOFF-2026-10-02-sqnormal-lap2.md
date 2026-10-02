# HANDOFF — explicit-square lane (row 3), lap 2 — 2026-10-02


Branch `proof/sqnormal`, HEAD `01fd13fc` (green, full lake build). Run stopped via `box done --green`.
Next steps (outside this lane): row 5 sorries in ExplicitSquareNonNormal.lean (no known mechanism).
Row 3 target `NormalNumbers.ExplicitSquare.exists_computable_normal_sq_not_normal` is PROVED,
axioms = [propext, Classical.choice, Quot.sound] (takes `BakerBanajiQuarterCantor` as hypothesis).
Frozen statements untouched (diff of the frozen file: one import + the proof body).

New: `ComputableNormal.lean` assembly lemmas, `SqrtFloor.lean`; `Bridge.floor_realOfDigits_mul_pow`
unprivated.  Details in PENDING_WORK.md "Row 3 CLOSED".

Open in lane: nothing for row 3.  Row 5 sorries are out of scope per operator.
Build gotcha: parallel full build hits fd exhaustion on whole-Mathlib importers after a Bridge
change; build failing modules individually, then `lake build`.
