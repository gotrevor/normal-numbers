# HANDOFF 2026-10-07 — c⋆ lap 2

Branch `proof/uniformbad-threshold`, HEAD after this commit, tree clean.

## Done
* `UniformBadRoute.lean` (proved): `goodBase_pow`, `exists_nonPerfPow_root`,
  `admissible_iff_nonPerfectPow` (perfect-power bases free), `cStar_le_of_treeCore` (wiring).
* Crux nodes (def Props, no sorry): `SmallBaseTreeCore` (15%), `TreeEngineSuffices` (50%).
* `cStar_le_four` docstring points at the route. Models in `scripts/cstar_models/`.

## Findings (see PENDING_WORK.md top section)
Base-charging engines stall below c≈7; base 2 must be exact; at c=4 base 3 is the blocker.
Natural survivor measure with base 3 has cell-relative Frostman C≈9; worst-case avoidance keeps 21%.

## Next
Model the h-normalised potential (Ψ = Φ/h, h = μ(Q)/|Q|^s) on the depth-20 survivor tree
(node scripts, `fr.js` as base); if it closes at c=4 restate the nodes around it.
