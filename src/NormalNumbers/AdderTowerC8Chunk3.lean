/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC8KData

/-! Chunk 3 of the C8 kernel sweep: states `[27648, 36864)`. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem c8_chunk3 :
    checkEdgesOnP (zfamPred c8Family) c8LiveK c8RhoK c8OmegaK c8ForcedK
      27648 9216 = true := by
  decide +kernel

end NormalNumbers.Adder
