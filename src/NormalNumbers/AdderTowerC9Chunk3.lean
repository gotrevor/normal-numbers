/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC9KData

/-! Chunk 3 of the C9 kernel sweep: states `[18432, 24576)`. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem c9_chunk3 :
    checkEdgesOnP (zfamPred c9Family) c9LiveK c9RhoK c9OmegaK c9ForcedK
      18432 24576 = true := by
  decide +kernel

end NormalNumbers.Adder
