# HANDOFF 2026-10-07 — c⋆ lap 8

Branch `proof/uniformbad-threshold`, HEAD 5bd5c6f2 (green, 10804 jobs).

## Done
* Directive item (1), decisive `c = 4` counting probe: NEGATIVE. True joint {2,3} tree is regular-looking
  (per-cell lookahead growth [1.751,1.842]) but weight-aware b≥5 charges (base 5: 0.055 = 1.5x regular) make the
  engine recursion die at c = 4 (lives at 4.25; at c = 4 lives only with base 5 also exact). Maze row
  "counted medium bases" updated; probes scripts/cstar_models/joint23_{spread,rho,rec}.js. PENDING lap 8.
* Also analysed (no Lean yet): two-base merge closures have no interior valleys (a local minimum between two
  same-base windows contradicts same-base thickness when τ_C < (τ_b−1)/2), so a {2,3} thick core is local;
  but every b≥5 engine on top of it (counting or root potential) fails at c = 4 by the same constants.

## Blocker
Scope gate is `sorry-free:UniformBadThreshold.lean` = `cStar_le_four`, a research wall (all known mechanisms
closed in Maze). DIRECTION item (2) mandates `cStar_le_five` in UniformBadFive.lean, which the hook marks
designated-open/out of scope. Operator needs to reconcile scope vs directive (or rescope to c⋆ ≤ 5).
