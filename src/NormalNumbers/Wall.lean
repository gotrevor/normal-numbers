/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# Wall's theorem

D. D. Wall (1949): a real number is normal in base `b` iff its
multiply-by-`b` orbit `n ↦ b^n·x mod 1` is equidistributed mod 1.

This is the dictionary between digit combinatorics and dynamics: it is the
statement that lets equidistribution results (e.g. the conditional
Bailey–Crandall orbits in `LnTwo.lean`) speak about digits at all.
-/

namespace NormalNumbers

/-- **Wall's theorem** (1949). -/
theorem isNormal_iff_equidistributed_orbit (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    IsNormal b x ↔ Equidistributed (orbit b x) := by
  sorry

end NormalNumbers
