/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Base

/-! Run-sweep chunks 6 of the `h25` family: one `lean` process per group, so no single kernel probe run holds them all. -/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

theorem h25_runs_c12 : runsCover h25P 49399552922694975 h25runsC12 53429314570632000 = true := by decide +kernel



theorem h25_runs_c13 : runsCover h25P 53429314570632000 h25runsC13 57597722302220100 = true := by decide +kernel


end NormalNumbers.Adder
