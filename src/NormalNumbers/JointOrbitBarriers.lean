/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSums
import NormalNumbers.QSpanNormal
import NormalNumbers.QSpanCriterion
import Architect

/-!
# Barriers to joint-orbit disjunctions

Precise Lean nodes for the closed joint-orbit routes in
`docs/joint-bc-orbits-2026-10-16.md`.  The first node is the universal disagreement
statement T-D: subtracting the normal Stoneham constant `alpha_{2,3}` forces many binary
digit disagreements for every input, so applying it to `ln 2` alone carries no information
specific to `ln 2`.
-/

namespace NormalNumbers.JointOrbitBarriers

open CantorExactExponent

/-- The number of the first `N` base-`b` digit positions where `x` and `y` disagree. -/
noncomputable def digitDisagreementCount (b : ℕ) (x y : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n =>
    digitOf b (Int.fract x) n != digitOf b (Int.fract y) n).card

/-- **T-D (frozen, 97%).**  Every binary expansion disagrees with its translate by
`alpha_{2,3}` on lower density at least `1/4`.

The report gives the borrow-analysis proof: a long agreement interval would force too many
binary digits of the normal Stoneham translate.  This exact universal-in-`x` form is the
witness that Stoneham sub-series pointing at `ln 2` is vacuous: it holds with `x` replaced by
an arbitrary real. -/
def StonehamUniversalDisagreement : Prop :=
  ∀ x : ℝ,
    (1 : ℝ) / 4 ≤ Filter.liminf (fun N : ℕ =>
      (digitDisagreementCount 2 x (x - stonehamAlpha 2 3) N : ℝ) / N) Filter.atTop

/-- A real whose standard base-ten expansion uses only the digits `0` and `1`. -/
def IsZeroOneCantorTen (x : ℝ) : Prop :=
  ∀ n : ℕ, digitOf 10 (Int.fract x) n = 0 ∨ digitOf 10 (Int.fract x) n = 1

/-- **R4 (frozen, 85%).**  A base-ten `{0,1}` Cantor pair has Roth-optimal
Diophantine behaviour in every nontrivial rational channel, while no such channel is
disjunctive.

The reported mechanism for the last clause is dynamical: every tail of
`a * x + c * y` lies in one of finitely many rational affine images of `aC + cC`, whose
upper box dimension is at most `log 4 / log 10 < 1`; hence its base-ten orbit is not dense.
The exponent-two leg is the Bénard--He--Zhang input already frozen in
`QSpan.exists_pair_exponentTwo_qSpan_not_normal`. -/
def CantorPairNoDisjunctiveChannel : Prop :=
  ∃ x y : ℝ,
    IsZeroOneCantorTen x ∧ IsZeroOneCantorTen y ∧
      ∀ a c : ℚ, (a ≠ 0 ∨ c ≠ 0) →
        HasIrrExponent ((a : ℝ) * x + (c : ℝ) * y) 2 ∧
          ¬ IsDisjunctive 10 ((a : ℝ) * x + (c : ℝ) * y)

/-- Reopen condition for a joint-normal orbit route containing `ln 2`: normality of `ln 2`
in at least one base. -/
def LnTwoNormalSeed : Prop :=
  ∃ b : ℕ, 2 ≤ b ∧ IsNormal b (Real.log 2)

/-- Joint normality of a digit pair forces normality of each coordinate.  This is the
coordinate-projection obstruction behind R6: putting `ln 2` into a jointly normal family
cannot bypass the normality problem for `ln 2` itself. -/
@[blueprint (title := "Joint normality forces coordinate normality")]
theorem isNormal_coordinates_of_jointNormal (b : ℕ) (hb : 2 ≤ b) (x y : ℝ)
    (hJ : IsNormalSequence (b * b) (fun i =>
      (QSpanCriterion.digitPair b (by omega) x y i : ℕ))) :
    IsNormal b x ∧ IsNormal b y := by
  constructor
  · simpa using QSpanCriterion.isNormal_span_of_jointNormal b hb x y hJ 1 0
      (Or.inl one_ne_zero)
  · simpa using QSpanCriterion.isNormal_span_of_jointNormal b hb x y hJ 0 1
      (Or.inr one_ne_zero)

end NormalNumbers.JointOrbitBarriers
