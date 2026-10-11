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

## STUCK (strike 1, 2026-10-08)
Blocked: the run gate `sorry-free:UniformBadTower.lean` now hinges on `selfGoodPerfect_four` alone, and the lap's
probes predict it FALSE.  Any rational tower at c needs infinitely many rationals good for bases 2 and 3
(`not_rationalTower_of_jointRationalsFinite`, proved).  Under the square-root coset model, which fits the measured
densities, a modulus with ord(2) = a and ord(3) = b carries at most gcd(2^a−1, 3^b−1)·e^{−κ₂a−κ₃b} such numerators.
The best log-margin is 26.5, and it is negative past scale 4096 (`gcd_budget.py`).  Corvaja–Zannier makes the total
finite.  Verify quickly: `python3 scripts/cstar_models/gcd_budget.py 4 1024`, and the Maze row
"Carmichael towers for rationalTower_four".
Ask: the operator decides between (a) rescoping the gate to a conditional refutation `¬ RationalTower 4` (coset
equidistribution plus CZ as cited hypothesis Props) and (b) a non-rational tower mechanism.  DIRECTION forbids
local engines, so proving the believed-false leaf is the only in-scope work left.
