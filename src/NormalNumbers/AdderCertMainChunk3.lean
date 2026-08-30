/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCertMainKData

/-! Chunk 3 of the kernel-tier main certificate sweep: states
`[27648, 36864)`. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem main_chunk3 :
    checkEdgesOn mainFamily mainLiveK mainRhoK mainOmegaK mainForcedK 27648 9216 = true := by
  decide +kernel

end NormalNumbers.Adder
