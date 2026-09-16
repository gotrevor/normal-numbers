/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 0 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers


theorem h25_runs_c0 : runsCover h25P 0 h25runsC0 4070375147188350 = true := by decide +kernel



theorem h25_runs_c1 : runsCover h25P 4070375147188350 h25runsC1 8286816388175325 = true := by decide +kernel


end NormalNumbers.Adder
