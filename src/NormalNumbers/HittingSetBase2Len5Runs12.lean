/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 12 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c24 : runsCover h25P 98709581465319825 h25runsC24 102905290744606350 = true := by decide +kernel



theorem h25_runs_c25 : runsCover h25P 102905290744606350 h25runsC25 106880173219719900 = true := by decide +kernel


end NormalNumbers.Adder
