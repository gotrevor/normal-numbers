/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 3 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c6 : runsCover h25P 24644271345704010 h25runsC6 28834627247919675 = true := by decide +kernel



theorem h25_runs_c7 : runsCover h25P 28834627247919675 h25runsC7 32859028460938680 = true := by decide +kernel


end NormalNumbers.Adder
