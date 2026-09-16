/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 8 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c16 : runsCover h25P 65777584147350075 h25runsC16 69944489930440125 = true := by decide +kernel



theorem h25_runs_c17 : runsCover h25P 69944489930440125 h25runsC17 73976979397946625 = true := by decide +kernel


end NormalNumbers.Adder
