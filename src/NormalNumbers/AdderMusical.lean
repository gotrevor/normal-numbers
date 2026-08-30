/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderMusicalKData
import NormalNumbers.LnTwoIrrational

/-!
# The musical disjunction (first data-swap instance of the signed engine)

Brief: `BRIEF-adder-signed-engine.md` §Objective 3.

The musical family — channels `(1,0)/00 · (0,1)/11 · (−1,1)/100 ·
(2,−1)/11 · (−3,2)/00 · (1,1)/010`, instance constants
`ln 2, ln 3, ln(3/2), ln(4/3), ln(9/8), ln 6` — admits a valid
certificate (15360 ambient states, 15 live, kernel-checked here), so by
the engine meta-theorem `signed_engine`, for ALL `X Y` not both rational
one of the six words occurs infinitely often.  All four words
(`00`, `11`, `100`, `010`) lie beyond the Adamczewski–Rampersad boundary
(occurrence of every single digit is known for irrational algebraics;
two-to-three-digit patterns in these transcendental constants are open),
so each disjunct is individually unprovable by current methods.

Kernel tier: `decide +kernel`, trust triple exactly.
-/

namespace NormalNumbers.Adder

open NormalNumbers

set_option maxHeartbeats 8000000 in
/-- The musical certificate passes the edge sweep (kernel). -/
theorem musical_edges_ok :
    checkEdgesP (zfamPred musicalFamily) 15360 musicalLiveK musicalRhoK
      musicalOmegaK musicalForcedK = true := by decide +kernel

set_option maxHeartbeats 8000000 in
/-- The musical certificate passes the forced sweep (kernel). -/
theorem musical_forced_ok :
    checkForcedP (zfamPred musicalFamily) 15360 musicalLiveK musicalForcedK
      = true := by decide +kernel

/-- The musical certificate, kernel tier. -/
theorem musical_cert_ok :
    checkCertP (zfamPred musicalFamily) 15360 musicalLiveK musicalRhoK
      musicalOmegaK musicalForcedK = true :=
  checkCertP_of_parts musical_edges_ok musical_forced_ok

/-- **The musical disjunction, universal form**: for any reals `X, Y` not
both rational, `00` occurs infinitely often in `X`, or `11` in `Y`, or
`100` in `Y − X`, or `11` in `2X − Y`, or `00` in `2Y − 3X`, or `010` in
`X + Y`. -/
theorem adder_musical_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 X [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 Y [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Y - X) [1, 0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (2 * X - Y) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (2 * Y - 3 * X) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + Y) [0, 1, 0] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  have hS : (15360 : ℕ) = zfamSize musicalFamily := by decide
  obtain ⟨ch, hch, hocc⟩ := signed_engine musicalFamily hS musical_cert_ok X Y hirr
    (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = X from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1, 1] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((-1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1, 0, 0] n := hocc
    rwa [show ((-1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y - X from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((2:ℤ):ℝ) * X + ((-1:ℤ):ℝ) * Y) [1, 1] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((-1:ℤ):ℝ) * Y = 2 * X - Y from by
      push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((-3:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((-3:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y = 2 * Y - 3 * X from by
      push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 1, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = X + Y from by push_cast; ring] at h

/-- **The musical disjunction** (ln-instance): `00` occurs infinitely often
in the binary expansion of ln 2, or `11` in ln 3, or `100` in ln(3/2), or
`11` in ln(4/3), or `00` in ln(9/8), or `010` in ln 6. -/
theorem adder_musical_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 2) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 3) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log (3 / 2)) [1, 0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log (4 / 3)) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log (9 / 8)) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 6) [0, 1, 0] n) := by
  have h2 : (2:ℝ) ≠ 0 := by norm_num
  have h3 : (3:ℝ) ≠ 0 := by norm_num
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div h3 h2
  have h43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) h3,
      show (4:ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    push_cast; ring
  have h98 : Real.log (9 / 8) = 2 * Real.log 3 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (9:ℝ) = 3 ^ 2 from by norm_num, show (8:ℝ) = 2 ^ 3 from by norm_num,
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 from by norm_num, Real.log_mul h2 h3]
  rw [h32, h43, h98, h6]
  exact adder_musical_disjunction_universal (Real.log 2) (Real.log 3)
    (Or.inl fun ⟨p, hp⟩ => irrational_log_two ⟨p, hp⟩)

end NormalNumbers.Adder
