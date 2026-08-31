/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC9KData

/-! Chunk 4b2 of the C9 kernel sweep: states `[29184, 30720)`.

Second half of the split chunk 4b `[27648, 30720)`: this range carries the
heaviest (~700-digit) packed omega numerals, so it holds the tail proof-term
spike that OOM'd the 3072-state chunk 4b (see `AdderTowerC9Chunk4b1`). -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem c9_chunk4b2 :
    checkEdgesOnP (zfamPred c9Family) c9LiveK c9RhoK c9OmegaK c9ForcedK
      29184 30720 = true := by
  decide +kernel

end NormalNumbers.Adder
