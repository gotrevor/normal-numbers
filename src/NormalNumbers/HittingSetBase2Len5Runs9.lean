/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 9 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c18 : runsCover h25P 73976979397946625 h25runsC18 78140372559549300 = true := by decide +kernel



theorem h25_runs_c19 : runsCover h25P 78140372559549300 h25runsC19 82355014513842525 = true := by decide +kernel


end NormalNumbers.Adder
