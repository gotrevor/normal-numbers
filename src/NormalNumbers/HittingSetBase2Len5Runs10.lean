/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 10 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c20 : runsCover h25P 82355014513842525 h25runsC20 86321736353177325 = true := by decide +kernel



theorem h25_runs_c21 : runsCover h25P 86321736353177325 h25runsC21 90495901554007950 = true := by decide +kernel


end NormalNumbers.Adder
