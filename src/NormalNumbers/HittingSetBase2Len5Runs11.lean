/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 11 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c22 : runsCover h25P 90495901554007950 h25runsC22 94534903310240250 = true := by decide +kernel



theorem h25_runs_c23 : runsCover h25P 94534903310240250 h25runsC23 98709581465319825 = true := by decide +kernel


end NormalNumbers.Adder
