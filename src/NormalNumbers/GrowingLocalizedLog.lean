/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureVandeheyDifferencing
import NormalNumbers.RealDefs

/-!
# The growing-prime localized logarithm `ζ_Y` (campaign launched 2026-10-02)

`ζ_Y = Σ_{m ≥ 1, P⁺(m) ≤ Y(m)} 1/(m·2ᵐ)`: the binary logarithm series restricted to the indices
that are `Y(m)`-smooth.  For a constant `Y` this is a finite-prime localized logarithm, known to
be normal (CaptainSude/xi-normality, paper level; Lean there only for `{2,3}`).  Here `Y` may grow,
as long as `π(Y(n)) ≤ (1−ε) log₂ log n`.  That gives an explicit normal constant with unbounded
prime support: every prime eventually divides a retained index.

Paper derivation and audit: KB note `normal-numbers-localized-log-growing-primes-2026-09-16`,
repaired by `docs/GROWING-PRIME-LOCALIZED-LOG-AUDIT-2026-10-02.md` (sound with two repairs, 75%:
segment cutoff `L₀ = N·exp(−(log log N)³)`, and the differencing depth `k` chosen per segment via
Vandehey's Lemma 6.3).  Route: the audit's §6.3 lemmas N1-N10; N8 (`korobov_uniform_saving`) is
the crux.

## Frozen statements (do not edit; prove them)

* `zetaY_isNormal`, conditional on `Literature.VandeheyDiff.VandeheyThm51` only.
* `exists_unbounded_zetaY`.

## Guard rule

**Content locator.**  Constant `Y` is the known finite-prime theorem, so the new content is
entirely the uniformity in the growing prime set (Vandehey's explicit constants, and the
interval count `(1 + log₂ x)^{π(Y)}`).

**Degenerate cases.**  `Y(m) = m` (every index retained) is `log 2`, excluded because `π(Y(n))`
then exceeds `log₂ log n`.  `ε ≥ 1` makes the hypothesis false for large `n`, since `3 ≤ Y` gives
`π(Y n) ≥ 2`; the statement is then vacuous, as it should be.  `Y ≥ 3` is load-bearing: it keeps
`3^k` and `2·3^k` retained, which is the 3-adic denominator survival.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Filter

/-- `m` is retained iff `m ≥ 1` and every prime factor of `m` is at most `Y m`. -/
def Retained (Y : ℕ → ℕ) (m : ℕ) : Prop := 1 ≤ m ∧ ∀ p, p.Prime → p ∣ m → p ≤ Y m

open Classical in
/-- `ζ_Y = Σ_{m retained} 1/(m·2ᵐ)`. -/
noncomputable def zetaY (Y : ℕ → ℕ) : ℝ :=
  ∑' m : ℕ, if Retained Y m then 1 / ((m : ℝ) * 2 ^ m) else 0

/-- **The growing-prime localized logarithm is normal in base 2.**  Paper level 75% (audit). -/
theorem zetaY_isNormal (hV : Literature.VandeheyDiff.VandeheyThm51)
    (Y : ℕ → ℕ) (hmono : Monotone Y) (h3 : ∀ m, 3 ≤ Y m) (ε : ℝ) (hε : 0 < ε)
    (hY : ∀ᶠ n : ℕ in atTop,
      ((Y n).primeCounting : ℝ) ≤ (1 - ε) * Real.logb 2 (Real.log n)) :
    IsNormal 2 (zetaY Y) := by
  sorry

/-- The theorem has content: an admissible `Y` with `Y → ∞`, hence unbounded prime support. -/
theorem exists_unbounded_zetaY : ∃ Y : ℕ → ℕ, Monotone Y ∧ (∀ m, 3 ≤ Y m) ∧
    Tendsto Y atTop atTop ∧
    ∀ᶠ n : ℕ in atTop, ((Y n).primeCounting : ℝ) ≤ (1 / 2) * Real.logb 2 (Real.log n) := by
  sorry

end NormalNumbers.GrowingLocalizedLog
