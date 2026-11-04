/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.ExponentLift
import NormalNumbers.SqrtTwoRoutes.ExponentOrder

/-!
# Exponent-selector discovery lap

Read `../../../MAZE.md` and `docs/sqrt-two-routes/exponent-selection.md`.
The index lift fits the real coefficient box, but its divisibility identity
holds for every numerator.  This module records the remaining word-dependent
input and an exact failure of arbitrary numerator-residue steering at a fixed
lifted state.  It does not exclude selecting a different exponent for the word.
-/

namespace NormalNumbers.SqrtTwoRoutes

/-- Open input for the index-lifting selector.  The lift hypotheses are
spelled out rather than assuming that index divisibility has been proved to
give denominator divisibility here.  No construction establishing this
word-dependent supply is known from the present lap. -/
@[blueprint (title := "Open word-dependent supply at lifted Pell indices")]
def PellLiftedWordSupply : Prop :=
  ∀ L A : ℕ, A < 2 ^ L → ∃ m n : ℕ, ∃ u v : ℤ,
    L ≤ m ∧ 2 ^ L ≤ n ∧ (2 : ℤ) ^ L ∣ pellQ n ∧
      PellWordCertificate L A m n u v

theorem pellLiftedWordSupply_implies_disjunctive (h : PellLiftedWordSupply) :
    IsDisjunctive 2 (Real.sqrt 2) := by
  apply pellWordCertificateSupply_implies_disjunctive
  intro L A hA
  obtain ⟨m, n, u, v, _, _, _, hcert⟩ := h L A hA
  exact ⟨m, n, u, v, hcert⟩

/-- The lifted n=4,m=8 state does not permit an arbitrary low numerator
residue while retaining real accuracy.  Every integer within one unit of
256*sqrt(2) is 362 or 363, so none is divisible by four. -/
@[blueprint (title := "Lift congruences cannot freely prescribe a nearby numerator residue")]
theorem lifted_zero_residue_not_near :
    ¬ ∃ P : ℤ, (4 : ℤ) ∣ P ∧ |(P : ℝ) - 256 * Real.sqrt 2| ≤ 1 := by
  rintro ⟨P, ⟨k, hk⟩, hnear⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hlo : (362 : ℝ) < 256 * Real.sqrt 2 := by nlinarith
  have hhi : 256 * Real.sqrt 2 < (363 : ℝ) := by nlinarith
  obtain ⟨hleft, hright⟩ := abs_le.mp hnear
  have hPlo : (361 : ℝ) < (P : ℝ) := by linarith
  have hPhi : (P : ℝ) < (364 : ℝ) := by linarith
  have hPloZ : (361 : ℤ) < P := by exact_mod_cast hPlo
  have hPhiZ : P < (364 : ℤ) := by exact_mod_cast hPhi
  omega

/-- The excluded residue at this state is not an accuracy failure for
every numerator: the actual lower integer is within one unit, as required. -/
theorem lifted_near_positive_control :
    |(362 : ℝ) - 256 * Real.sqrt 2| ≤ 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hlo : (362 : ℝ) < 256 * Real.sqrt 2 := by nlinarith
  have hhi : 256 * Real.sqrt 2 < (363 : ℝ) := by nlinarith
  rw [abs_le]
  constructor <;> linarith

end NormalNumbers.SqrtTwoRoutes
