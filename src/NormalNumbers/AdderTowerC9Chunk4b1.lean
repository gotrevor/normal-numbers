/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC9KData

/-! Chunk 4b1 of the C9 kernel sweep: states `[27648, 29184)`.

First half of the split chunk 4b `[27648, 30720)`: that range's
`decide +kernel` OOM'd at its tail (exit 137) even at 3072 states, so it was
halved again to 1536-state sub-chunks (see `AdderTowerC9Chunk4b2`). -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem c9_chunk4b1 :
    checkEdgesOnP (zfamPred c9Family) c9LiveK c9RhoK c9OmegaK c9ForcedK
      27648 29184 = true := by
  decide +kernel

end NormalNumbers.Adder
