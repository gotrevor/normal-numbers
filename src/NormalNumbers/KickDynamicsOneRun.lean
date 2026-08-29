/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickDynamics

/-!
# The twin edge: `SliverEscape` caps one-runs

Lane-2 target 2 (2026-08-29 operator brief; alien review move 2 — "completes
D7 symmetry").  Mirror of `zeroRun_le_of_sliverEscape` for runs of ones,
via `lnTwoOrbit_top_sliver_of_oneRun`.

⚠️ DRAFT STATEMENT — the constants below are a first guess, and there is a
known width mismatch to resolve honestly: the one-run dichotomy lands the
surrogate only in the WIDE sliver `1 − 2/(n+j+1)`, while the frozen node
`SliverEscape` hypothesizes the narrow sliver `1 − 1/(n+j+1)`.  The lap
may restate the theorem below (adjust constants, thresholds, or hypotheses)
to the honest provable twin — keeping the name, keeping it an edge from a
sliver-escape-style hypothesis to a one-run cap, and NEVER editing the
frozen `SliverEscape` itself.  If the honest twin needs a wide-sliver
variant of the node, freeze that variant here with a provenance docstring
recording the width-mismatch reason, and record the decision in
PENDING_WORK.md.
-/

namespace NormalNumbers

open Filter Set

/-- **Twin edge (DRAFT)**: `SliverEscape` caps one-runs of binary `ln 2`,
mirroring `zeroRun_le_of_sliverEscape`. -/
theorem oneRun_le_of_sliverEscape {C : ℝ} {N₀ : ℕ} (hC : 0 ≤ C)
    (hesc : SliverEscape C N₀) {n k : ℕ} (hn : N₀ ≤ n) (hn1 : 1 ≤ n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    (k : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2)
      + Real.logb 2 ((n : ℝ) + k + 1) + 3 := by
  sorry

end NormalNumbers
