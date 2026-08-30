/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCertMainKData

/-! Chunk 1 of the kernel-tier main certificate sweep: states
`[9216, 18432)`. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem main_chunk1 :
    checkEdgesOn mainFamily mainLiveK mainRhoK mainOmegaK mainForcedK 9216 9216 = true := by
  decide +kernel

end NormalNumbers.Adder
