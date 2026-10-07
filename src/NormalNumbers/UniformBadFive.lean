/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadCount
import NormalNumbers.UniformBadRoute

/-!
# `c⋆ ≤ 5` by level-dependent counting

The counting engine of `UniformBadCount` (`Count.growth`, which already allows a growth rate `g k`
that depends on the level) at exponent `5`, with three changes against `cStar_le_six`:

* **base `2` exact.**  A cell at level `k + 1 ≥ 6` whose last five binary digits agree has a
  unique charge: its ancestor at level `k − 4` (the other run digit would already have been killed
  one level earlier).  Multiplicity `1`, so the base-2 balance is the run-free recurrence itself.
* **per-window resolution.**  The window of order `n` of base `b` has length `r` cells at its
  resolution level `lv = ⌈log₂ b^{n+5}⌉`, with `r = 2^{lv+1}/b^{n+5} ∈ [2, 4)`.  It is killed at `lv`
  when `r < 3` (at most `4` cells) and one level earlier when `r ≥ 3` (at most `3` cells), and
  charged at lag `⌊log₂(¾ (b⁵ − 2))⌋`.  Perfect powers are dropped (`admissible_iff_nonPerfectPow`).
* **two growth rates.**  `g k = 329/200` when level `k + 1` carries a base-3 kill and `181/100`
  otherwise.  For base `3` the kill levels satisfy `L(n+2) ≥ L(n) + 3` (no two consecutive gaps of
  one), so any `ℓ` consecutive levels hold at most `⌊(2ℓ + 2)/3⌋` of them, and every product of
  growth rates over a charging window is bounded below.

Probe (`scripts/cstar_models/lvl5c.js`, `pess.js`, 2026-10-07): the worst per-level slack of this
scheme is `0.038` along the true kill pattern (`0.028` with every base `b ≥ 5` killing at every
level), and `0.019` with every charging window given its worst count of base-3 kill levels.  With
a single growth rate the scheme fails (best slack `−0.023`), as does charging `5` cells per window
(`−0.011`).  Control: the same pessimistic check at `c = 6` has slack `0.21`, consistent with
`cStar_le_six`.
-/

namespace NormalNumbers.UniformBadThreshold

/-- **`c⋆ ≤ 5`** (frozen 2026-10-07, believed 90%).  Banked bound between the proved `c⋆ ≤ 6` and
the headline `cStar_le_four`.

English proof.  Run `Count.growth` with the pruning described in the module doc.  At a level whose
successor carries no base-3 kill, the kills are at most `cnt (k−4) + Σ_{b ≥ 5} 4 cnt (k+1−lag b)`;
bounding each `cnt j` by `cnt k` over the product of the growth rates on `[j, k)`, and each product
from below by the worst count of base-3 kill levels in the window, the kills are at most
`(0.124 + 0.037) cnt k ≤ (2 − 181/100) cnt k`.  At a base-3 kill level the extra term
`4 cnt (k − 6)` adds `0.167 cnt k`, and `0.328 ≤ 2 − 329/200`.  So every level has an alive cell,
the limit point avoids every base-2 run and every window of a base that is not a perfect power,
and `‖bⁿξ‖ ≥ b^{−5}` for all `b ≥ 2` follows from `goodBase_pow`. -/
theorem cStar_le_five : cStar ≤ 5 := by
  sorry

end NormalNumbers.UniformBadThreshold
