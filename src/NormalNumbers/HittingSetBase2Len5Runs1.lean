/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 1 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c2 : runsCover h25P 8286816388175325 h25runsC2 12274924425063300 = true := by decide +kernel



theorem h25_runs_c3 : runsCover h25P 12274924425063300 h25runsC3 16480222607723875 = true := by decide +kernel


end NormalNumbers.Adder
