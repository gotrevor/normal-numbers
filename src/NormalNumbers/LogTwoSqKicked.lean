/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickedOrbit

/-!
# log² 2 through the summed-kick machine (target 5, optional dessert)

Lane-2 target 5 (2026-08-29 operator brief): instantiate the summed-kick
machine (`KickedOrbit.lean`) for a second constant.  `log² 2` is chosen
over `π²` because its series is elementary: the classical generating-
function identity (integrate `Σ Hₙ xⁿ = −log(1−x)/(1−x)`) gives at
`x = 1/2`

  `log² 2 = Σ_{m≥1} (2·H_{m−1}/m) · 2^{−m}`   (`H₀ = 0`, so the `m = 1`
  kick vanishes),

i.e. base `b = 2` with kick numerators `r m = 2·H_{m−1}/m`.

## Obligations (mirror `PiBBP.lean`)

1. ⚠️ PROBE FIRST: an `experiments/` script verifying the identity
   numerically to high precision (the node discipline — every frozen
   node carries a refutation probe).  If the probe FAILS, stop and
   record the failure: the identity as stated is wrong, do not freeze it.
2. The node `LogTwoSqSeries` below (CITED-class, hypothesis-not-axiom;
   the in-house Cauchy-product derivation is a later lane-2 discharge,
   like `PiBBP` was).
3. Elementary kick bounds: `r` is eventually `< 1` (base 2 makes the
   constant cap `A = 1` VACUOUS — the sliver `1 − A/(b−1)` empties — so
   the cap must be position-dependent: for `m > n` use an explicit
   decreasing bound like `A n = 2·(1 + Real.log (n+1))/(n+1)`, from
   `H_{m−1} ≤ 1 + log (m−1)`; the floor uses `H` monotone:
   `r (n+1) ≥ 2·H_n/(n+1) > 0` for `n ≥ 1`).
4. The sliver headline below via `top_sliver_of_zeroRun_kicked`; a
   `_maxRun` twin via `top_sliver_of_maxRun_kicked` once `A n ≤ 1/2`.

⚠️ DRAFT STATEMENT — the headline's thresholds and the explicit cap are
first guesses; restate to what the machine honestly yields (keep the
name, keep the conditional-on-node shape, ADDITIVE ONLY elsewhere).
-/

namespace NormalNumbers

/-- Harmonic number `H_m = Σ_{k=1}^{m} 1/k` (real-valued). -/
noncomputable def harmonicR (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1)

/-- The kick numerators of `log² 2`: `r m = 2·H_{m−1}/m` (`r 0 = r 1 = 0`). -/
noncomputable def logTwoSqKick (m : ℕ) : ℝ :=
  2 * harmonicR (m - 1) / m

/-- **Node (frozen, CITED-class): the `log² 2` series** —
`log² 2 = Σ_{m≥1} (2·H_{m−1}/m)·2^{−m}`, classical (integrated harmonic
generating function at `x = 1/2`), stated in the summed-kick machine's
indexing.  Lane-2 discharge owed, like `PiBBP` was. -/
def LogTwoSqSeries : Prop :=
  HasSum (fun m : ℕ => logTwoSqKick (m + 1) / (2 : ℝ) ^ (m + 1))
    (Real.log 2 ^ 2)

/-- **Headline (DRAFT)**: conditional on the series node, a long zero-run
of binary `log² 2` at position `n` forces the truncated-series surrogate
into the explicit top sliver, via `top_sliver_of_zeroRun_kicked`. -/
theorem logTwoSq_top_sliver_of_zeroRun (hs : LogTwoSqSeries) {n k : ℕ}
    (hn : 6 ≤ n) (hk : (1 : ℝ) / 2 ^ k < harmonicR n / ((n : ℝ) + 1))
    (h : OccursAt 2 (Real.log 2 ^ 2) (List.replicate k 0) n) :
    1 - 2 * (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1)
      ≤ Int.fract ((2 : ℝ) ^ n * kickedPartial 2 logTwoSqKick n) := by
  sorry

end NormalNumbers
