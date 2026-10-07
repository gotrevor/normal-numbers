/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadThreshold

/-!
# A sharper lower bound for `c⋆`, and where the finite systems stall

`five_halves_le_cStar` used a 29-window cover found by a greedy search with `n ≤ 14`.  With the
stages allowed to go deeper (windows of radius down to `10⁻¹³`), the same exact-rational greedy
(`scripts/cstar_models/cover2.py 93 37 30 1000000 1e-13`) covers `[0, 1]` at `c = 93/37 ≈ 2.5135`
with 59 windows from the bases `2, 3, 5, 10, 17` (`n ≤ 18`).

**Where the finite systems stall (c⋆ lap 13 probe, `scripts/cstar_models/surv.py`, `cover2.py`).**
With every base `b ≤ 3000` (perfect powers dropped) and every window of radius `≥ 10⁻¹³`, the
survivor set of `‖bⁿξ‖ > b^{−c}` is empty at `c = 93/37` and nonempty at `c = 2.514`.  The
survivors sit just above `2^{−c}`, near binary-periodic rationals: at `c = 2.52`–`2.55` near
`0.1746089874… ≈ 11443/65535` (`65535 = 2¹⁶ − 1`), at `c = 2.6` near `0.1691158…`, at `c = 2.514`
near `0.30155…`.  The rational families die once `b` reaches their denominator (control: the
family near `241/1365` survives `b ≤ 1000` at `c = 2.514` and is gone at `b ≤ 3000`), but new
families with longer binary periods take their place, and at `c = 2.55` the survivor count grows
with the resolution (606, 1066, 1762 intervals at radii `10⁻¹¹, 10⁻¹², 10⁻¹³`).  So the finite
systems point at `c⋆` only slightly above `5/2` (`CStarLeThirteenFifths`), far below the proved
upper bound `124/25`.
-/

namespace NormalNumbers.UniformBadThreshold

/-- 59-window certificate at `c = 93/37` (`scripts/cstar_models/cover2.py`, greedy, exact
rationals; bases `2, 3, 5, 10, 17`, `n ≤ 18`). -/
def cert9337 : List Win :=
  [(2, 0, 0, 21891/125000), (2, 8, 45, 21891/125000), (17, 1, 3, 807/1000000),
   (2, 12, 723, 21891/125000), (2, 4, 3, 21891/125000), (5, 1, 1, 17503/1000000),
   (2, 6, 13, 21891/125000), (3, 5, 50, 15801/250000), (2, 10, 211, 21891/125000),
   (2, 2, 1, 21891/125000), (2, 10, 301, 21891/125000), (3, 3, 8, 15801/250000),
   (2, 6, 19, 21891/125000), (2, 14, 4909, 21891/125000), (3, 10, 17693, 15801/250000),
   (2, 18, 78547, 21891/125000), (2, 10, 307, 21891/125000), (10, 1, 3, 613/200000),
   (2, 8, 77, 21891/125000), (2, 16, 19757, 21891/125000), (3, 8, 1978, 15801/250000),
   (2, 12, 1235, 21891/125000), (2, 4, 5, 21891/125000), (3, 1, 1, 15801/250000),
   (2, 3, 3, 21891/125000), (5, 1, 2, 17503/1000000), (2, 5, 13, 21891/125000),
   (17, 1, 7, 807/1000000), (2, 9, 211, 21891/125000), (2, 1, 1, 21891/125000),
   (2, 9, 301, 21891/125000), (3, 5, 143, 15801/250000), (2, 5, 19, 21891/125000),
   (5, 1, 3, 17503/1000000), (2, 3, 5, 21891/125000), (3, 1, 2, 15801/250000),
   (2, 4, 11, 21891/125000), (2, 12, 2861, 21891/125000), (3, 8, 4583, 15801/250000),
   (2, 16, 45779, 21891/125000), (2, 8, 179, 21891/125000), (10, 1, 7, 613/200000),
   (2, 10, 717, 21891/125000), (2, 18, 183597, 21891/125000), (3, 10, 41356, 15801/250000),
   (2, 14, 11475, 21891/125000), (2, 6, 45, 21891/125000), (3, 3, 19, 15801/250000),
   (2, 10, 723, 21891/125000), (2, 2, 3, 21891/125000), (2, 10, 813, 21891/125000),
   (3, 5, 193, 15801/250000), (2, 6, 51, 21891/125000), (5, 1, 4, 17503/1000000),
   (2, 4, 13, 21891/125000), (2, 12, 3373, 21891/125000), (17, 1, 14, 807/1000000),
   (2, 8, 211, 21891/125000), (2, 0, 1, 21891/125000)]

theorem not_admissible_93_37 : ¬ Admissible (93 / 37) := by
  have := not_admissible_of_cert 93 37 (by norm_num) cert9337 (by decide +kernel)
    (by decide +kernel)
  norm_num at this ⊢; exact this

/-- **Sharper lower bound** (c⋆ lap 13): `c⋆ ≥ 93/37 ≈ 2.5135`.  A greedy cover with all bases
`b ≤ 3000` and windows down to radius `10⁻¹³` fails already at `c = 2.514` (survivors near
`0.30155`), so finite covers of this shape cannot go much higher. -/
@[blueprint (title := "Bugeaud 10.36 optimal exponent: c⋆ ≥ 93/37 by a 59-window cover")]
theorem ninety_three_thirty_sevenths_le_cStar : (93 : ℝ) / 37 ≤ cStar :=
  le_cStar_of_not_admissible not_admissible_93_37

/-- **Open conjecture (believed 60%): `c⋆ ≤ 13/5`.**  The optimal exponent sits only slightly
above `5/2`.

Evidence (c⋆ lap 13, `scripts/cstar_models/surv.py`, `cover2.py`): with all bases `b ≤ 3000`
(`b ≤ 8000` at `c = 13/5`) and every window of radius `≥ 10⁻¹³`, the survivor set at `c = 13/5`
is nonempty (first survivor near `0.1691158212`), and at `c = 2.55` the number of surviving
intervals grows as the resolution refines (606, 1066, 1762 at radii `10⁻¹¹, 10⁻¹², 10⁻¹³`), the
profile of a Cantor set of dimension about `0.2`.  Control: the same search empties at `c = 93/37`
(certificate `cert9337`), and survivors near a rational `p/q` disappear once `b` reaches `q` (the
family near `241/1365` at `c = 2.514`).  Caveat: every survivor family seen so far lies near a
binary-periodic rational `p/(2^m − 1)` with `m ≤ 16`, which the base `2^m − 1` kills; the
conjecture needs the limit of such families to avoid every base.

Would imply `CStarLeThree` and put `c⋆` in `[93/37, 13/5]`.  The upper-bound engines are far from
it: the best proved bound is `124/25` (`cStar_le_124_25`), and the local engines stall near
`c ≈ 4.55` (`UniformBadNineHalves`, Maze row "local per-window engines at c = 9/2"). -/
def CStarLeThirteenFifths : Prop := cStar ≤ 13 / 5

end NormalNumbers.UniformBadThreshold
