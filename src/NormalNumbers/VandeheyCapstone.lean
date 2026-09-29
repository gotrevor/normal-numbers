/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyCFBridge

/-!
# Vandehey 2017, Theorem 1.1 — the capstone

`LiteratureVandehey` states `VandeheyUniformFreq` and `vandehey_matrix_action` and proves the
endgame reduction between them; it cannot prove the crux, because every module of the Raney
transducer chain imports it.  This module closes the loop.

The route, in one line:

  `vandehey_matrix_action`
    ← `vandehey_matrix_action_of_uniformFreq`      (the either-or endgame, `LiteratureVandehey`)
    ← `vandeheyUniformFreq_of_scaleUniformFreq`    (Serret + Smith: reduce to `x ↦ D·x`, `D` prime)
    ← `scaleUniformFreq_holds`                     (`VandeheyCFBridge`)
    ← `mobiusUniformFreq_of_runClock`              (`VandeheyRunClock`)
        · `zero_lt_runRate'`, `runClock_mono'`, `tendsto_runClock_div`   (the clock)
        · `exists_tendsto_cfCount_runClock`                              (`hcount`)
-/

namespace NormalNumbers.Literature

/-- **The crux, proved.**  Vandehey §2–§6 for the concrete Raney `L/R` transducer, on the run
clock (`VandeheyRunClock`) rather than on the letter clock, which does not exist. -/
theorem vandeheyUniformFreq_holds : VandeheyUniformFreq :=
  vandeheyUniformFreq_of_scaleUniformFreq VandeheyLR.scaleUniformFreq_holds

/-- **Vandehey 2017, Theorem 1.1**: integer Möbius maps with nonzero determinant
preserve CF-normality. -/
theorem vandehey_matrix_action_holds : vandehey_matrix_action :=
  vandehey_matrix_action_of_uniformFreq vandeheyUniformFreq_holds

end NormalNumbers.Literature

section
open NormalNumbers.Literature
#print axioms vandeheyUniformFreq_holds
#print axioms vandehey_matrix_action_holds
end
