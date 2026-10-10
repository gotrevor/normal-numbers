/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTower

/-!
# Review of the rational-tower quantifiers

The status note at commit `191666b6` gives only a conditional refutation of
`RationalTower`.  Its definition is unconditionally impossible: approximation
at every accuracy around a fixed rational cannot avoid that rational's killing
base.  This is a defect in the proposed sufficient condition, and gives no
evidence for `JointRationalsFinite` or `CosetSurvival`.

The original note is retained as the reviewed artifact.  This review does not
change either located bound for `cStar`.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear dnear_le_abs_sub)

/-- Every rational has a neighbourhood forbidden by its killing base.  Thus
no rational can belong to a tower family, at any real exponent. -/
theorem towerFamily_excludes_rat {c : ℝ} {F : Set ℝ} (h : TowerFamily c F)
    (x : ℚ) : (x : ℝ) ∉ F := by
  intro hx
  let b : ℕ := 2 * x.den
  have hb : 2 ≤ b := by dsimp [b]; have := x.den_pos; omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hp : (0 : ℝ) < (b : ℝ) ^ (-c) := Real.rpow_pos_of_pos hb0 _
  obtain ⟨y, -, hy, hg⟩ := h.2 (x : ℝ) hx
    ((b : ℝ) ^ (-c) / b) (div_pos hp hb0) (b + 1)
  have hgood := hg b hb (by omega) 1
  have hnear := dnear_le_abs_sub ((b : ℝ) * y) (2 * x.num)
  have hxint : (b : ℝ) * (x : ℝ) = ((2 * x.num : ℤ) : ℝ) := by
    have he : (x : ℝ) = (x.num : ℝ) / x.den := by
      exact_mod_cast (Rat.num_div_den x).symm
    dsimp [b]
    rw [he]
    push_cast
    field_simp
  rw [← hxint, ← mul_sub, abs_mul, abs_of_pos hb0] at hnear
  have hsmall : (b : ℝ) * |y - (x : ℝ)| < (b : ℝ) ^ (-c) := by
    have := (lt_div_iff₀ hb0).1 hy
    nlinarith
  simp only [pow_one] at hgood
  linarith

/-- The rational-tower route is false for every exponent, independently of any
coset heuristic or literature hypothesis. -/
@[blueprint (title := "RationalTower is impossible at every exponent by continuity")]
theorem not_rationalTower (c : ℝ) : ¬ RationalTower c := by
  rintro ⟨F, hrat, hF⟩
  obtain ⟨x, hx⟩ := hF.1
  obtain ⟨q, rfl⟩ := hrat hx
  exact towerFamily_excludes_rat hF q hx

/-- The perfect-self-good-rationals premise is also false at every exponent.
The integer zero is self-good vacuously (its denominator is one), and the
existing implication would turn this premise into an impossible tower. -/
theorem not_selfGoodPerfect (c : ℝ) : ¬ SelfGoodPerfect c := by
  intro h
  apply not_rationalTower c
  apply rationalTower_of_selfGoodPerfect h 0
  intro b hb hbB
  norm_num at hbB
  omega

/-- Positive control: `TowerFamily` itself is consistent whenever `Admissible`
holds.  The obstruction is requiring its members to be rational. -/
theorem towerFamily_singleton_of_admissible {c : ℝ} (hc : Admissible c) :
    ∃ x : ℝ, TowerFamily c {x} := by
  obtain ⟨x, hx⟩ := hc
  refine ⟨x, ⟨x, rfl⟩, ?_⟩
  intro y hy ε hε B
  have hyx : y = x := hy
  subst y
  refine ⟨x, rfl, ?_, ?_⟩
  · simpa using hε
  · exact fun b hb _ n => hx b hb n

/-- Reopen condition for a different rational-approximation route: a single
convergent sequence eventually good below every base bound.  Unlike
`TowerFamily`, this asks for approximation only to its limit, not arbitrarily
close approximation to every earlier rational.  It does not by itself assert
strict goodness of the limit at exponent `c`. -/
def ConvergentGoodRationalSequence (c : ℝ) : Prop :=
  ∃ (r : ℕ → ℚ) (x : ℝ),
    Filter.Tendsto (fun k => (r k : ℝ)) Filter.atTop (nhds x) ∧
    ∀ B : ℕ, ∀ᶠ k in Filter.atTop, GoodBelow c B (r k : ℝ)

/-- Literature input, specialized from Peres--Schlag, arXiv:0706.0223v1,
Theorem 3.1: take M = 4 and c₀ = 1/240.  The increasing enumeration of
{2^n, 3^n : n ≥ 0} satisfies the four-step doubling hypothesis (at most
three distinct elements lie in [t, 2t]).  Thus the theorem implies this
two-base bound.  This is a cited Prop, not a formalized proof, and asserts
neither irrationality nor simultaneous avoidance for other bases.
Source: https://arxiv.org/pdf/0706.0223 -/
def PeresSchlagTwoThreeBound : Prop :=
  ∃ x : ℝ, ∀ b : ℕ, b = 2 ∨ b = 3 → ∀ n : ℕ,
    (1 : ℝ) / 1920 ≤ dnear ((b : ℝ) ^ n * x)

#print axioms not_rationalTower
#print axioms not_selfGoodPerfect
#print axioms towerFamily_singleton_of_admissible

end NormalNumbers.UniformBadThreshold
