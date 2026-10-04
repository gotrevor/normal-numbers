/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LogCastingOut

/-!
# The logarithmic rung (E2): frozen targets beside the audit

Two statements the audit (`docs/LOG-AVERAGE-AUDIT-2026-10-04.md`) believes and does not prove.
Both are `sorry` by design: statement now, proof later.

* `omegaModDigit_logTwoWord_of_zetaExponent` — the one honest **consumer** of the Elliott ledger
  on the digit side.  It is about the CARRY-FREE sibling `Σ_{m≥1} (ω(m) mod b)·b^{-m}`, not about
  `G4_b`; low novelty (a direct corollary of Tao 2016 plus Delange), high odds.
* `simplyNormalLog_of_growingDepth` — the wiring from the reopen condition
  `GrowingDepthLogElliott` to log-simple-normality of `G4_b`.  It does not prove the hard part;
  it certifies that the reopen condition is the right one.
-/

open Finset Filter Topology

namespace NormalNumbers.LogCastingOut

noncomputable section

/-- Digit `n` (position `n + 1` after the point) of the carry-free constant
`Σ_{m≥1} (ω(m) mod b)·b^{-m}`: every term is already a base-`b` digit, so no carries. -/
def omegaModDigit (b n : ℕ) : ℕ := CastingOut.omegaNat (n + 1) % b

/-- Logarithmic frequency of the two-letter word `(i, j)` at positions `n, n + 1`. -/
def logPairFreq (s : ℕ → ℕ) (i j N : ℕ) : ℝ :=
  (∑ n ∈ (range N).filter (fun n => s n = i ∧ s (n + 1) = j), (1 : ℝ) / (n + 1)) /
    ∑ n ∈ range N, (1 : ℝ) / (n + 1)

/-- **Carry-free consumer of the ledger** (frozen; true-confidence 97%, Lean-provable-from-repo
confidence 80%).  Under the ledger's single input, every two-letter word has logarithmic
frequency `b^{-2}` in the digits `ω(n+1) mod b`.

*English proof.*  Expand `1[d_n = i, d_{n+1} = j] = b^{-2} Σ_{a₁,a₂ mod b} e(a₁(ω(n+1) − i)/b)
e(a₂(ω(n+2) − j)/b)`.  The character `(0,0)` gives the main term.  For `a₁ ≢ 0` take
`g₁ = zetaOmegaInt (a₁/b)` on the form `n+1` and `g₂ = zetaOmegaInt (a₂/b)` on `n+2`
(determinant `1·2 − 1·1 ≠ 0`); for `a₁ ≡ 0`, `a₂ ≢ 0` take `g₁ = zetaOmegaInt (a₂/b)` on `n+2`
and `g₂ ≡ 1` on `n+1`.  `ElliottGeneral.nonasymptoticLogElliottMult` (Tao 2016, proved in this
repo) needs only `g₁` uniformly non-pretentious, which the ledger chain supplies from
`ZetaLogDerivExponent θ`, `θ < 1` (the same discharges as
`ElliottLedger.twoPointElliottLog_of_zetaExponent`, via
`ElliottSmallShift.uniformlyNonPretentious_zetaOmega_of_almostRealProp`).  Weights `1/n` on
`2 ≤ n ≤ X` versus `1/(n+1)` on `n < N` differ by a summable amount.

Prior art: for `b = 2` this is the `ω`-analogue of Tao 2016's two-point log Chowla; the
`λ`-version is in `TaoTeravainen2019LiouvilleThree` (length 3). -/
theorem omegaModDigit_logTwoWord_of_zetaExponent {b : ℕ} (hb : 2 ≤ b) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (h : ElliottZetaTheta.ZetaLogDerivExponent θ)
    {i j : ℕ} (hi : i < b) (hj : j < b) :
    Tendsto (logPairFreq (omegaModDigit b) i j) atTop (𝓝 (1 / (b : ℝ) ^ 2)) := by
  sorry

/-- **The reopen condition is the right one** (frozen; confidence 70%).  Growing-depth log Elliott
for the digit-truncation phases gives logarithmic simple normality of `G4_b`.

*English proof.*  `{bⁿ G4_b} ≡ T_n := Σ_{k≥0} ω(n+1+k) b^{-(k+1)}`, and
`|e(h T_n) − digitTruncPhase b h K n| ≤ 2π|h| b^{-K} T_{n+K}`.  The log mean of `T_{n+K}` is
`≪ log log X`, so with `b^{K(X)} ≥ (log log X)²` the truncation costs `o(1)` in log mean; hence
the log Weyl sums of `(bⁿ G4_b)` vanish for every `h` with `b ∤ h`, and for `b ∣ h` by the index
shift `n ↦ n + 1` (log means are shift-invariant).  A log-averaged Weyl criterion then gives log
equidistribution of `{bⁿ G4_b}`, and the digit `⌊b{bⁿx}⌋` reads an interval of length `1/b`
(endpoints have measure zero).  Choose `K(X) = ⌈2 log_b log log X⌉ + 1`, which also satisfies
`b^K ≤ log X` for large `X`. -/
theorem simplyNormalLog_of_growingDepth {b : ℕ} (hb : 3 ≤ b) (h : GrowingDepthLogElliott b) :
    CastingOut.SimplyNormalLog b (PrimeLambert.primeLambertAtBase b) := by
  sorry

end

end NormalNumbers.LogCastingOut
