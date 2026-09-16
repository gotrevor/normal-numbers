/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 4 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c8 : runsCover h25P 32859028460938680 h25runsC8 37046943853019100 = true := by decide +kernel



theorem h25_runs_c9 : runsCover h25P 37046943853019100 h25runsC9 41258802628318275 = true := by decide +kernel


end NormalNumbers.Adder
