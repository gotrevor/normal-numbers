/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsBoundary
import NormalNumbers.StonehamPairsUnconditional
import NormalNumbers.VandeheyProof

/-!
# Joint normality of one prime class of Stoneham constants (Theorem T-B′)

Fix a prime `p ∤ b` and let `d = ord_p b`.  The family `α_{b^{mᵢ}, p^{sᵢ}}` is rationally jointly
`b`-normal (every nonzero `ℚ`-combination is `b`-normal) exactly when the powers `ζ^{mᵢ}` of a
primitive `d`-th root of unity are `ℚ`-linearly independent.  The exponents `sᵢ` play no role.
Since `ℚ(ζ)` has degree `φ(d)`, a jointly normal family has at most `φ(d)` members; for
`p ∈ {2, 3}` that is one.

`ζ` stands in for the Teichmüller lift `ω_p(b) ∈ ℤ_p`: both generate a copy of the `d`-th
cyclotomic field, and `ℚ`-linear independence of the `ζ^{mᵢ}` does not depend on the embedding.
For `p = 2`, `d = 1` and `ζ = 1`, matching the convention `ω₂ := 1`.

Source: `papers/2026-10-16-bailey-borwein-full-answer.md`, Theorem T-B′ and referee repair 1.
-/

namespace NormalNumbers.StonehamPrimeClass

/-- The prime-class Stoneham family `i ↦ α_{b^{mᵢ}, p^{sᵢ}}`. -/
noncomputable def primeClassFamily (b p : ℕ) {r : ℕ} (m s : Fin r → ℕ) : Fin r → ℝ :=
  fun i => stonehamAlpha (b ^ m i) (p ^ s i)

/-- **T-B′, non-normal half.**  If the `ζ^{mᵢ}` are `ℚ`-linearly dependent, some nonzero rational
combination of the family is not `b`-normal. -/
theorem not_isRationallyJointNormal_of_not_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (m s : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hdep : ¬ LinearIndependent ℚ (fun i => ζ ^ m i)) :
    ¬ IsRationallyJointNormal b (primeClassFamily b p m s) := by
  sorry

/-- **T-B′, normal half.**  If the `ζ^{mᵢ}` are `ℚ`-linearly independent, every nonzero rational
combination of the family is `b`-normal. -/
theorem isRationallyJointNormal_of_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (m s : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hind : LinearIndependent ℚ (fun i => ζ ^ m i)) :
    IsRationallyJointNormal b (primeClassFamily b p m s) := by
  sorry

/-- **Theorem T-B′.**  A prime-class Stoneham family is rationally jointly normal exactly when the
`ζ^{mᵢ}` are `ℚ`-linearly independent. -/
theorem isRationallyJointNormal_iff_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (m s : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p))) :
    IsRationallyJointNormal b (primeClassFamily b p m s) ↔
      LinearIndependent ℚ (fun i => ζ ^ m i) :=
  ⟨fun h => by
    by_contra hdep
    exact not_isRationallyJointNormal_of_not_linearIndependent b p hp hb hpb m s hm hs ζ hζ
      hdep h,
   isRationallyJointNormal_of_linearIndependent b p hp hb hpb m s hm hs ζ hζ⟩

/-- **Pairs.**  `α_{b^{m₁}, p^{s₁}}` and `α_{b^{m₂}, p^{s₂}}` are rationally jointly `b`-normal
exactly when `ord_p b ∤ 2(m₂ − m₁)`. -/
theorem isRationallyJointNormal_pair_iff
    (b p m₁ m₂ s₁ s₂ : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) :
    IsRationallyJointNormal b
        ![stonehamAlpha (b ^ m₁) (p ^ s₁), stonehamAlpha (b ^ m₂) (p ^ s₂)] ↔
      ¬ ((orderOf (b : ZMod p) : ℤ) ∣ 2 * ((m₂ : ℤ) - m₁)) := by
  sorry

/-- **The L2 premise holds**: each pair in `α_{3,7}, α_{9,7}, α_{27,7}` is rationally jointly
`3`-normal (`ord_7 3 = 6` divides none of `2, 4`). -/
theorem stonehamThreeSevenPairwiseNormal_holds : StonehamThreeSevenPairwiseNormal := by
  sorry

/-- **Joint normality is not pairwise**, unconditionally: the ternary triple is pairwise but not
jointly rationally `3`-normal. -/
theorem stonehamThreeSeven_pairwise_not_joint_unconditional :
    IsPairwiseRationallyJointNormal 3 stonehamThreeSevenFamily ∧
      ¬ IsRationallyJointNormal 3 stonehamThreeSevenFamily :=
  stonehamThreeSeven_pairwise_not_joint stonehamThreeSevenPairwiseNormal_holds

end NormalNumbers.StonehamPrimeClass
