/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC9KData

/-! Chunk 4a of the C9 kernel sweep: states `[24576, 27648)`.

Split from the original single chunk 4 `[24576, 30720)`: that range's
`decide +kernel` peaked past the box memory ceiling (the highest-numbered
states carry ~700-digit packed omega numerals, so the proof term spiked to
OOM at the tail).  Halving the range halves the peak. -/

namespace NormalNumbers.Adder

set_option maxHeartbeats 8000000 in
theorem c9_chunk4a :
    checkEdgesOnP (zfamPred c9Family) c9LiveK c9RhoK c9OmegaK c9ForcedK
      24576 27648 = true := by
  decide +kernel

end NormalNumbers.Adder
