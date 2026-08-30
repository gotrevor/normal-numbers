/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCertMainKData

/-! Chunk 2 of the kernel-tier main certificate sweep: states
`[18432, 27648)`. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem main_chunk2 :
    checkEdgesOn mainFamily mainLiveK mainRhoK mainOmegaK mainForcedK 18432 9216 = true := by
  decide +kernel

end NormalNumbers.Adder
