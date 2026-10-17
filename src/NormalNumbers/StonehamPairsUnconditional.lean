/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPairsNormal
import NormalNumbers.VandeheyProof

/-!
# Bailey–Borwein's question, answered unconditionally

`StonehamPairsNormal` proves the literal Bailey–Borwein statements from the `VandeheyThm51`
binder; `VandeheyProof.vandeheyThm51_holds` discharges it.  So, with no cited input:
`α_{b,c₁} + α_{b,c₂}` is `b`-normal for every `c₁, c₂ ≥ 2` coprime to `b`, and so is
`α_{b,c₁} − α_{b,c₂}` for `c₁ ≠ c₂`.
-/

namespace NormalNumbers.StonehamPairsUnconditional

/-- **Bailey–Borwein (2012, §4), answered:** every literal sum is normal. -/
theorem isNormal_stonehamAlpha_add (b c₁ c₂ : ℕ) (hb : 2 ≤ b)
    (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂) (hb₁ : Nat.Coprime c₁ b) (hb₂ : Nat.Coprime c₂ b) :
    IsNormal b (stonehamAlpha b c₁ + stonehamAlpha b c₂) :=
  StonehamPairsNormal.isNormal_stonehamAlpha_add VandeheyProof.vandeheyThm51_holds
    b c₁ c₂ hb hc₁ hc₂ hb₁ hb₂

/-- Every literal difference with `c₁ ≠ c₂` is normal. -/
theorem isNormal_stonehamAlpha_sub (b c₁ c₂ : ℕ) (hb : 2 ≤ b)
    (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂) (hb₁ : Nat.Coprime c₁ b) (hb₂ : Nat.Coprime c₂ b)
    (hne : c₁ ≠ c₂) :
    IsNormal b (stonehamAlpha b c₁ - stonehamAlpha b c₂) :=
  StonehamPairsNormal.isNormal_stonehamAlpha_sub VandeheyProof.vandeheyThm51_holds
    b c₁ c₂ hb hc₁ hc₂ hb₁ hb₂ hne

/-- `α₂,₃ + α₂,₉` is 2-normal (a same-class pair). -/
theorem isNormal_two_stoneham_three_add_nine :
    IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 2 9) :=
  StonehamPairsNormal.isNormal_two_stoneham_three_add_nine VandeheyProof.vandeheyThm51_holds

end NormalNumbers.StonehamPairsUnconditional
