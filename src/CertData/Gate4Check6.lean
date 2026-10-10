/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CertData.Gate4

/-! Gate 4 certificate check, bins `[57600, 67200)` (native code: `CertData` is precompiled). -/

namespace NormalNumbers.UniformBadThreshold.Coherent.Data

theorem checkRange_6 : checkRange 57600 67200 = true := by native_decide

end NormalNumbers.UniformBadThreshold.Coherent.Data
