# HANDOFF 2026-10-07 — c⋆ lap 3 (review + bank)

Branch `proof/uniformbad-threshold`, tree clean after this commit.

## Done
* `UniformBadCount.lean` (axiom-clean): counting engine `Count.growth` (Rosenfeld-style: kills at
  level k+1 charged to alive ancestors; `cnt (k+1) + #kills = 2 cnt k`), limit point
  `Count.exists_mem_cells`, and the exponent-6 application: `Count.exists_good_six`
  (`‖bⁿξ‖ ≥ b^{−6}` all b, n), `admissible_of_six_lt`, **`cStar_le_six`**.
* DIRECTION.md branch directive revised (review lap); STATUS.md section for this branch.

## Findings (PENDING_WORK top)
Per-level counting: c=6 closes, c=5 fails; level-averaged: only c≈4.6; c=4 needs base 3 exact
jointly with base 2.  Joint simulation: growth 1.808 ({2,3}), 1.80 (all bases) at c=4.

## Next (binding: DIRECTION.md)
1. Crux probe: finite-state abstraction of the joint {2,3} skew product (binary run state, ternary
   run state, position u in ternary units, phase), compute a sub-eigenvector; how many states for
   Λ ≥ 1.75?  Record as a Lean node with confidence.
2. Averaged counting engine (level-dependent g k in `Count.growth` is already general) → c ≤ ~4.75.
