/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsNormal
import NormalNumbers.StonehamSumsBoundary
import NormalNumbers.StonehamPairsAnalytic
import NormalNumbers.StonehamPairsArithmetic
import NormalNumbers.StonehamPairsResultant
import NormalNumbers.StonehamPairsClasses
import NormalNumbers.StonehamPairsDistinct
import NormalNumbers.StonehamPairsSameClass

/-!
# Bailey–Borwein's question, literally: `α_{b,c₁} ± α_{b,c₂}` is always `b`-normal

Bailey–Borwein (Ramanujan J. 29, 2012, §4): "it is not known at the present time whether the sum
`α_{b,c₁} + α_{b,c₂}` is `b`-normal."  `StonehamSumsNormal` answers it for coprime `c₁, c₂`.  This
file answers it for **every** pair `c₁, c₂ ≥ 2` coprime to `b`, including pairs that share primes
(`α₂,₃ + α₂,₉`, `α₅,₂ + α₅,₆`), and for differences with `c₁ ≠ c₂`.

The boundary is sharp and already in Lean: rational coefficients can break it
(`not_isSimplyNormal_stoneham_sub_succ_mul`: `α_{b,p} − (p+1)α_{b,p²}` is not simply normal).

Paper: `papers/2026-10-16-bailey-borwein-full-answer.md` (refereed 2026-10-16, headline ACCEPT
~92%; read its "Referee repairs" section first).  Analytic input: the same `VandeheyThm51`
binder as Theorem A.
-/

namespace NormalNumbers.StonehamPairsNormal

open Literature.VandeheyDiff

/-- **The literal Bailey–Borwein sum** is `b`-normal for every pair `c₁, c₂` coprime to `b`. -/
theorem isNormal_stonehamAlpha_add (hV : VandeheyThm51) (b c₁ c₂ : ℕ) (hb : 2 ≤ b)
    (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂) (hb₁ : Nat.Coprime c₁ b) (hb₂ : Nat.Coprime c₂ b) :
    IsNormal b (stonehamAlpha b c₁ + stonehamAlpha b c₂) := by
  by_cases heq : c₁ = c₂
  · subst c₂
    exact NormalNumbers.StonehamSumsNormal.isNormal_stonehamAlpha_add_self
      hV b c₁ hb hc₁ hb₁
  by_cases hdep : StonehamPairMulDep c₁ c₂
  · obtain ⟨g, s₁, s₂, hg, hs₁, hs₂, hc₁g, hc₂g⟩ :=
      exists_common_power_base_of_stonehamPairMulDep c₁ c₂ hc₁ hc₂ hdep
    subst c₁
    subst c₂
    have hsne : s₁ ≠ s₂ := by
      intro hseq
      apply heq
      rw [hseq]
    exact isNormal_stonehamAlpha_add_of_common_power
      hV b g s₁ s₂ hb hg hs₁ hs₂ hb₁ hb₂ hsne
  · exact isNormal_stonehamAlpha_add_of_not_mulDep
      hV b c₁ c₂ hb hc₁ hc₂ hb₁ hb₂ hdep

/-- **The difference** `α_{b,c₁} − α_{b,c₂}` is `b`-normal whenever `c₁ ≠ c₂`. -/
theorem isNormal_stonehamAlpha_sub (hV : VandeheyThm51) (b c₁ c₂ : ℕ) (hb : 2 ≤ b)
    (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂) (hb₁ : Nat.Coprime c₁ b) (hb₂ : Nat.Coprime c₂ b)
    (hne : c₁ ≠ c₂) :
    IsNormal b (stonehamAlpha b c₁ - stonehamAlpha b c₂) := by
  by_cases hdep : StonehamPairMulDep c₁ c₂
  · obtain ⟨g, s₁, s₂, hg, hs₁, hs₂, hc₁g, hc₂g⟩ :=
      exists_common_power_base_of_stonehamPairMulDep c₁ c₂ hc₁ hc₂ hdep
    subst c₁
    subst c₂
    have hsne : s₁ ≠ s₂ := by
      intro heq
      apply hne
      rw [heq]
    exact isNormal_stonehamAlpha_sub_of_common_power
      hV b g s₁ s₂ hb hg hs₁ hs₂ hb₁ hb₂ hsne
  · exact isNormal_stonehamAlpha_sub_of_not_mulDep
      hV b c₁ c₂ hb hc₁ hc₂ hb₁ hb₂ hdep

/-- A same-class instance the coprime theorem cannot reach: `α₂,₃ + α₂,₉` is 2-normal. -/
theorem isNormal_two_stoneham_three_add_nine (hV : VandeheyThm51) :
    IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 2 9) :=
  isNormal_stonehamAlpha_add hV 2 3 9 le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end NormalNumbers.StonehamPairsNormal
