/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LogTwoSqKicked

/-!
# Lane-2 discharge of the frozen node `LogTwoSqSeries`

Batch-2 target 1 (2026-08-29 operator brief v2).  The one obligation of
this file is `logTwoSqSeries_proved : LogTwoSqSeries`, i.e.

  `log² 2 = Σ_{m≥0} (2·H_m/(m+1)) · 2^{−(m+1)}`

(in the machine's shifted indexing).  Route: `log 2 = Σ_{k≥1} 2^{−k}/k`
(`−log(1−x)` Taylor series at `x = 1/2`), square it; the Cauchy product
of the series with itself has `m`-th coefficient
`Σ_{i+j=m, i,j≥1} 1/(i·j)`, and the partial-fraction identity
`1/(i·j) = (1/(i+j))·(1/i + 1/j)` collapses it to `2·H_{m−1}/m`.
Absolute convergence on the disk makes the Cauchy product legal —
mathlib: `Complex.hasSum_taylorSeries_neg_log` (or the real
`Real.hasSum_log_sub_one`-family; check what exists), plus the
summable-norm Cauchy product API (`HasSum.mul_eq` /
`summable_norm_mul_of_summable_norm` family).  Probe already green:
`experiments/logtwosq_series.py` (identity verified to 70 digits).
-/

namespace NormalNumbers

/-- **Lane-2 discharge of the frozen node `LogTwoSqSeries`**: the
harmonic-weighted series sums to `log² 2`. -/
theorem logTwoSqSeries_proved : LogTwoSqSeries := by
  sorry

end NormalNumbers
