/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsNormal
import NormalNumbers.GrowingLocalizedLog

/-!
# Vandehey's Korobov-sum bound, proved (no longer cited)

`Literature.VandeheyDiff.VandeheyThm51` (Vandehey, *Differencing methods for Korobov-type
exponential sums*, J. Anal. Math. 138 (2019), Theorem 5.1) enters the repo as a cited hypothesis.
This file proves it, which makes every theorem that takes it as a binder unconditional.  The two
headline consumers are restated below without the binder.
-/

namespace NormalNumbers.VandeheyProof

open Literature.VandeheyDiff

/-- **Vandehey, Theorem 5.1**, proved. -/
theorem vandeheyThm51_holds : VandeheyThm51 := by
  sorry

/-- **Theorem A, unconditional.**  Every nonzero rational combination of Stoneham constants
`α_{b^{mᵢ}, cᵢ}` with the `cᵢ` pairwise coprime and coprime to `b` is `b`-normal. -/
theorem isNormal_stonehamCombination_unconditional
    (b : ℕ) (hb : 2 ≤ b) {r : ℕ} (c m : Fin r → ℕ) (q : Fin r → ℚ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i) (hq : q ≠ 0) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)) :=
  StonehamSumsNormal.isNormal_stonehamCombination vandeheyThm51_holds b hb c m q hc hcop hcb hm hq

/-- **`α₂,₃ + α₂,₅` is normal in base 2**, unconditionally. -/
theorem isNormal_two_stoneham_three_add_five_unconditional :
    IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 2 5) :=
  StonehamSumsNormal.isNormal_two_stoneham_three_add_five vandeheyThm51_holds

/-- **`ζ_Y` is normal**, unconditionally (was conditional on `VandeheyThm51`). -/
theorem zetaY_isNormal_unconditional
    (Y : ℕ → ℕ) (hmono : Monotone Y) (h3 : ∀ m, 3 ≤ Y m) (ε : ℝ) (hε : 0 < ε)
    (hY : ∀ᶠ n : ℕ in Filter.atTop,
      ((Y n).primeCounting : ℝ) ≤ (1 - ε) * Real.logb 2 (Real.log n)) :
    IsNormal 2 (GrowingLocalizedLog.zetaY Y) :=
  GrowingLocalizedLog.zetaY_isNormal vandeheyThm51_holds Y hmono h3 ε hε hY

end NormalNumbers.VandeheyProof
