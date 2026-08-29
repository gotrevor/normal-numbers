/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickedOrbit

/-!
# π² through a signed-kick machine (batch-2 target 2)

Lane-2 batch-2 target 2 (operator brief v2).  π² is BBP in base 16 —
Bailey, *A Compendium of BBP-Type Formulas for Mathematical Constants*
(2023-04-08), **Formula 29**:

  `π² = Σ_{k≥0} 16⁻ᵏ (16/(8k+1)² − 16/(8k+2)² − 8/(8k+3)² − 16/(8k+4)²
        − 4/(8k+5)² − 4/(8k+6)² + 2/(8k+7)²)`.

Probe: `experiments/pi_sq_bbp.py` (2026-08-29) — identity verified to 88
digits AND the block-sign fact confirmed: the per-digit block is positive
at `k = 0` and NEGATIVE for every `1 ≤ k < 30` (coefficient sum `−30`,
asymptotically `−30/(64k²)`).  So the nonneg-kick machine
(`top_sliver_of_zeroRun_kicked`) does NOT apply; the honest move is a
SIGNED variant:

* abstract layer (new section here or a new module, KickedOrbit-style):
  for `x = Σ r(k)/bᵏ` with two-sided cap `|r m| ≤ A` for `m > n`, the
  tail bracket is two-sided, `|bⁿ·(x − sₙ)| ≤ A/(b−1)`, and the run
  theorem is BOUNDARY-shaped, not top-sliver-shaped: a long run of zeros
  (or of top digits) pins the surrogate `fract (bⁿ·sₙ)` within
  `b⁻ᵏ + A/(b−1)` of the wrap point from EITHER side (i.e. the min of
  `fract` and `1 − fract` is small) — for π² the cap past `n` decays
  like `C/n²`, so the window is quadratically thin;
* elementary signed kick bounds for `piSqKick` (`|piSqKick j| ≤ C/(8j+1)²`
  for `j ≥ 1`-type, plus the `j = 0` block handled separately or the
  machine applied from `n ≥ 1`);
* the headline below, conditional on the frozen node `PiSqBBP`.

⚠️ DRAFT STATEMENT — the headline's shape and constants are a first
guess; restate to what the signed machine honestly yields (keep the
name, keep it conditional on `PiSqBBP`, ADDITIVE ONLY elsewhere; the
node statement itself is FROZEN — probe-verified — do not restate it).
-/

namespace NormalNumbers

/-- The signed per-digit block of Formula 29. -/
noncomputable def piSqKick (j : ℕ) : ℝ :=
  16 / (8 * (j : ℝ) + 1) ^ 2 - 16 / (8 * (j : ℝ) + 2) ^ 2
    - 8 / (8 * (j : ℝ) + 3) ^ 2 - 16 / (8 * (j : ℝ) + 4) ^ 2
    - 4 / (8 * (j : ℝ) + 5) ^ 2 - 4 / (8 * (j : ℝ) + 6) ^ 2
    + 2 / (8 * (j : ℝ) + 7) ^ 2

/-- The π² BBP summand: `16⁻ʲ · piSqKick j`. -/
noncomputable def piSqTerm (j : ℕ) : ℝ := (1 / 16 ^ j) * piSqKick j

/-- **Node (frozen, CITED-class): the π² BBP formula** — Bailey's
compendium (2023-04-08) Formula 29, presented in the original 1997 BBP
paper.  Probe-verified to 88 digits (`experiments/pi_sq_bbp.py`).
Lane-2 discharge owed, like `PiBBP` was. -/
def PiSqBBP : Prop := HasSum piSqTerm (Real.pi ^ 2)

/-- **Headline (DRAFT)**: conditional on the node, a long zero-run of
hexadecimal π² at position `n ≥ 1` pins the BBP surrogate near the wrap
point from either side (boundary forcing, two-sided). -/
theorem piSq_boundary_of_zeroRun (hπ : PiSqBBP) {n k : ℕ} (hn : 1 ≤ n)
    (h : OccursAt 16 (Real.pi ^ 2) (List.replicate k 0) n) :
    min (Int.fract ((16 : ℝ) ^ n * kickedPartial 16 piSqKick n))
        (1 - Int.fract ((16 : ℝ) ^ n * kickedPartial 16 piSqKick n))
      ≤ 1 / 16 ^ k + 1 / (8 * (n : ℝ) + 1) := by
  sorry

end NormalNumbers
