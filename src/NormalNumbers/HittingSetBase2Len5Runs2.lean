/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 2 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c4 : runsCover h25P 16480222607723875 h25runsC4 20703859396119900 = true := by decide +kernel



theorem h25_runs_c5 : runsCover h25P 20703859396119900 h25runsC5 24644271345704010 = true := by decide +kernel


end NormalNumbers.Adder
