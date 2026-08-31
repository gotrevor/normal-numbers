/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC9KData

/-! Chunk 4b of the C9 kernel sweep: states `[27648, 30720)`.

Second half of the split original chunk 4 (see `AdderTowerC9Chunk4a`). -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem c9_chunk4b :
    checkEdgesOnP (zfamPred c9Family) c9LiveK c9RhoK c9OmegaK c9ForcedK
      27648 30720 = true := by
  decide +kernel

end NormalNumbers.Adder
