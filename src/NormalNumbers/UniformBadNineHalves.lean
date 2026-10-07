/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadFive

/-!
# Below exponent `5`: the next gate for `c⋆`

Proved so far: `5/2 ≤ c⋆ ≤ 5` (`five_halves_le_cStar`, `cStar_le_five`).  `cStar_le_four` is a
recorded wall (it needs an exact joint `{2, 3, 5}` core; Maze rows "counted medium bases over an
exact {2,3} core at c = 4" and "adaptive split cores for the Newhouse thick core").

The `cStar_le_five` engine has slack only `0.013` at its base-`3` kill levels, so lowering the
exponent needs a new ingredient, not retuned constants.  The candidates, in the order the lap-8 and
lap-10 probes suggest:
* base `3` handled exactly alongside base `2` (the joint recursion `joint23_rec.js` dies at level 91
  at `c = 4` but lives at `c = 4.25`), with the bases `b ≥ 5` still counted;
* finer kill-level bookkeeping (non-integer exponents change the windows' cell spans).

Frozen 2026-10-07 by the operator (Ren) after `cStar_le_five` landed.
-/

namespace NormalNumbers.UniformBadThreshold

/-- **Headline (frozen 2026-10-07): `c⋆ ≤ 9/2`.**  Believed 40%.

English proof sketch.  Run the two-rate counting engine of `cStar_le_five` at exponent `9/2` with
base `3` made exact as well as base `2`: the joint `{2, 3}` survivor tree grows at a rate that the
lap-8 probe keeps alive down to `c ≈ 4.25`, and the bases `b ≥ 5` (perfect powers free) are charged
to alive ancestors at their kill levels, whose total weight `Σ_{b ≥ 5} b^{−9/2}`-type series is small.
The risk is the exact joint `{2, 3}` core: a counting lower bound for its growth that is uniform over
all levels (the `jointCoreSubEigen` question of `UniformBadJoint`, at `9/2` instead of `4`). -/
theorem cStar_le_nine_halves : cStar ≤ 9 / 2 := by
  sorry

end NormalNumbers.UniformBadThreshold
