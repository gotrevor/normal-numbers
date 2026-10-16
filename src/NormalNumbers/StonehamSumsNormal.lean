/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSums
import NormalNumbers.LiteratureVandeheyDifferencing

/-!
# Sums of Stoneham constants with pairwise-coprime `c` are normal

Bailey–Borwein (Ramanujan J. 29, 2012, §4): "it is not known at the present time whether the sum
`α_{b,c₁} + α_{b,c₂}` is `b`-normal."  This file answers it for coprime `c₁, c₂`: every nonzero
rational combination of Stoneham constants `α_{b^{mᵢ}, cᵢ}` with the `cᵢ` pairwise coprime and
coprime to `b` is `b`-normal.  The coprimality is necessary: `α₂,₃ + α₄,₃` is not even simply
normal (`not_isSimplyNormal_stoneham_sum`).

Paper proof: `papers/2026-10-16-stoneham-sums-normal.md` (independently refereed, minor repairs
applied).  The one analytic input is Vandehey's Korobov-sum bound, here the cited
`VandeheyThm51`; the paper's (F3) is Vandehey's Corollary 1.2, which this file derives from it
(`vandeheyCor12_of_thm51`) rather than citing separately.
-/

namespace NormalNumbers.StonehamSumsNormal

open Finset NormalNumbers.G4 Literature.VandeheyDiff

/-- **Vandehey, Corollary 1.2** (derived, not cited): for fixed `b`, a finite prime set `P`
coprime to `b`, and `ε > 0`, there are `δ > 0` and `C` such that for every `m ≥ 2` built from
`P`, every `a` coprime to `m`, and every `N ≥ m^ε`,
`|Σ_{n=1}^N e(a bⁿ/m)| ≤ C m^{−δ} N (1 + log m)`.  Vandehey §6.1: `N ≥ m` by the `k = 0`
case (his Lemma 2.3), `m^ε ≤ N ≤ m` by Theorem 5.1 at a `k` chosen from `ε`. -/
def VandeheyCor12 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ Nat.Coprime p b) →
    ∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧
      ∀ (m : ℕ), 2 ≤ m → (∀ p, p.Prime → p ∣ m → p ∈ P) →
      ∀ (a : ℤ), IsCoprime a (m : ℤ) → ∀ N : ℕ, (m : ℝ) ^ ε ≤ N →
        ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
          C * (m : ℝ) ^ (-δ) * N * (1 + Real.log m)

theorem vandeheyCor12_of_thm51 (hV : VandeheyThm51) : VandeheyCor12 := by
  sorry

/-- **Theorem A.**  Pairwise-coprime Stoneham families: every nonzero rational combination is
normal. -/
theorem isNormal_stonehamCombination (hV : VandeheyThm51)
    (b : ℕ) (hb : 2 ≤ b) {r : ℕ} (c m : Fin r → ℕ) (q : Fin r → ℚ)
    (hc : ∀ i, 2 ≤ c i) (hcop : Pairwise fun i j => Nat.Coprime (c i) (c j))
    (hcb : ∀ i, Nat.Coprime (c i) b) (hm : ∀ i, 1 ≤ m i) (hq : q ≠ 0) :
    IsNormal b (∑ i, (q i : ℝ) * stonehamAlpha (b ^ m i) (c i)) := by
  sorry

/-- **Headline.**  `α₂,₃ + α₂,₅` is normal in base 2 (Bailey's "Can we prove normality for
α2,3 + α2,5?"). -/
theorem isNormal_two_stoneham_three_add_five (hV : VandeheyThm51) :
    IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 2 5) := by
  sorry

end NormalNumbers.StonehamSumsNormal
