# HANDOFF 2026-10-07 — c⋆ lap 4 (exact {2,3} core probe)

Branch `proof/uniformbad-threshold`.
## Done
* `UniformBadJoint.lean`: `winBad`, `SubEigen`, `exists_good_of_subEigen` (proved, axiom-clean),
  crux node `jointCoreSubEigen_four` (sorry 80%, BarrierAudit-linked).
* `scripts/cstar_models/abs23.js`: worst-case box abstraction of the joint {2,3} system:
  `node abs23.js N M1 M2 IT [delta] [c]` → min ratio 1.669 at (81,8,8,150).
## Findings / next: see PENDING_WORK top (lap 4).  Crux moved to bases 5,6,7: counting them
fails at c=4 by a wide margin; need exact treatment or a regular-measure engine.
