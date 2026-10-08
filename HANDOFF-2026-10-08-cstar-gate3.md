# HANDOFF c⋆ gate 3 (2026-10-08)

Branch proof/uniformbad-threshold; run gate `sorry-free:src/NormalNumbers/UniformBadTower.lean`.

Done (all in UniformBadTower.lean, axiom-clean modulo native_decide):
- `le_cStar_729_290` via `not_admissible_729_290` (95-window cert, `scripts/cstar_models/cert_exact.py`).
- `goodBelow_241_1365`; `admissible_of_towerFamily` (Baire on closure F); checker `goodBelow_of_check`.
- `rationalTower_four` proved from ONE leaf: `selfGoodPerfect_four` (sorry, 35%).
- `not_rationalTower_of_jointRationalsFinite` (refutation direction), nodes `JointRationalsFinite`,
  `CarmichaelChainCollapse`, `SmallOrderModuli`; Maze row "Carmichael towers for rationalTower_four".

Crux state: census (joint_rationals.js) shows self-good rationals at c = 4 abundant below 1e5, but their
denominators are divisors of 2^36−1-type numbers (small multiplicative orders), i.e. the Carmichael regime whose
asymptotics are predicted to collapse (count Q·e^{-κL}, log Q = L^{o(1)}).  Decisive next probe: census over
divisors of 2^L−1 / lcm-type moduli for L up to ~10^3 (sampled numerators), tracking count of self-good per level.
Either a structured family appears (attack SelfGoodPerfect) or collapse evidence → push ¬RationalTower 4
(conditional on a coset-equidistribution hypothesis + CZ as cited Props).
