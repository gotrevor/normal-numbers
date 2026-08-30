/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCertMainKData

/-! Chunk 4 of the kernel-tier main certificate sweep: states
`[36864, 46080)`. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem main_chunk4 :
    checkEdgesOn mainFamily mainLiveK mainRhoK mainOmegaK mainForcedK 36864 9216 = true := by
  decide +kernel

end NormalNumbers.Adder
