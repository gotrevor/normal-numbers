/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureVandeheyDifferencing
import NormalNumbers.RealDefs
import NormalNumbers.GrowingLocalizedLogWitness
import NormalNumbers.GrowingLocalizedLogNormal

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
  have hS3 : ∀ K, Retained Y (3 ^ K) ∧ Retained Y (2 * 3 ^ K) := by
    intro K
    have h3p : ∀ p, p.Prime → p ∣ 3 ^ K → p = 3 := fun p hp hd =>
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd)
    refine ⟨⟨Nat.one_le_pow _ _ (by norm_num), fun p hp hd => ?_⟩,
      ⟨by have := Nat.one_le_pow K 3 (by norm_num); omega, fun p hp hd => ?_⟩⟩
    · rw [h3p p hp hd]; exact h3 _
    · rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · have := Nat.le_of_dvd two_pos h; linarith [h3 (2 * 3 ^ K)]
      · rw [h3p p hp h]; exact h3 _
  exact isNormal_xS hV hmono h3 hS3 (fun m hm => hm.1) (fun m p hm _ hp hd => hm.2 p hp hd)
    hε hY

/-- The theorem has content: an admissible `Y` with `Y → ∞`, hence unbounded prime support. -/
theorem exists_unbounded_zetaY : ∃ Y : ℕ → ℕ, Monotone Y ∧ (∀ m, 3 ≤ Y m) ∧
    Tendsto Y atTop atTop ∧
    ∀ᶠ n : ℕ in atTop, ((Y n).primeCounting : ℝ) ≤ (1 / 2) * Real.logb 2 (Real.log n) :=
  ⟨witnessY, witnessY_mono, three_le_witnessY, witnessY_tendsto, witnessY_admissible⟩

end NormalNumbers.GrowingLocalizedLog
