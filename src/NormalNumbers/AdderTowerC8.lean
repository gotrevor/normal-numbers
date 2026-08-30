/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC8Chunk0
import NormalNumbers.AdderTowerC8Chunk1
import NormalNumbers.AdderTowerC8Chunk2
import NormalNumbers.AdderTowerC8Chunk3
import NormalNumbers.AdderTowerC8Chunk4
import NormalNumbers.AdderTowerC8Chunk5
import NormalNumbers.AdderTowerC8Chunk6
import NormalNumbers.AdderTowerC8Chunk7
import NormalNumbers.LnTwoIrrational

/-!
# C8: the complemented flagship (BRIEF-adder-tower phase A)

Words are the bitwise complements of the frozen flagship's
(`11, 110, 00, 110, 101, 111` vs `00, 001, 11, 001, 010, 000`), same six
constants.  Certified directly for independence (dossier recommendation)
rather than derived via the complement involution.  Data-swap instance
of `signed_engine`; kernel tier, trust triple.
-/

namespace NormalNumbers.Adder

open NormalNumbers

set_option maxHeartbeats 8000000 in
theorem c8_forced_ok :
    checkForcedP (zfamPred c8Family) 73728 c8LiveK c8ForcedK = true := by
  decide +kernel

theorem c8_edges_ok :
    checkEdgesP (zfamPred c8Family) 73728 c8LiveK c8RhoK c8OmegaK c8ForcedK
      = true := by
  apply checkEdgesP_of_edgeOkP
  intro s' hs'
  have c0 := checkEdgesOnP_spec c8_chunk0
  have c1 := checkEdgesOnP_spec c8_chunk1
  have c2 := checkEdgesOnP_spec c8_chunk2
  have c3 := checkEdgesOnP_spec c8_chunk3
  have c4 := checkEdgesOnP_spec c8_chunk4
  have c5 := checkEdgesOnP_spec c8_chunk5
  have c6 := checkEdgesOnP_spec c8_chunk6
  have c7 := checkEdgesOnP_spec c8_chunk7
  rcases (by omega : s' < 9216 ∨ (9216 ≤ s' ∧ s' < 18432) ∨ (18432 ≤ s' ∧ s' < 27648)
      ∨ (27648 ≤ s' ∧ s' < 36864) ∨ (36864 ≤ s' ∧ s' < 46080)
      ∨ (46080 ≤ s' ∧ s' < 55296) ∨ (55296 ≤ s' ∧ s' < 64512)
      ∨ (64512 ≤ s' ∧ s' < 73728)) with
    h | h | h | h | h | h | h | h
  · have := c0 s' h
    rwa [Nat.zero_add] at this
  · have := c1 (s' - 9216) (by omega)
    rwa [show 9216 + (s' - 9216) = s' from by omega] at this
  · have := c2 (s' - 18432) (by omega)
    rwa [show 18432 + (s' - 18432) = s' from by omega] at this
  · have := c3 (s' - 27648) (by omega)
    rwa [show 27648 + (s' - 27648) = s' from by omega] at this
  · have := c4 (s' - 36864) (by omega)
    rwa [show 36864 + (s' - 36864) = s' from by omega] at this
  · have := c5 (s' - 46080) (by omega)
    rwa [show 46080 + (s' - 46080) = s' from by omega] at this
  · have := c6 (s' - 55296) (by omega)
    rwa [show 55296 + (s' - 55296) = s' from by omega] at this
  · have := c7 (s' - 64512) (by omega)
    rwa [show 64512 + (s' - 64512) = s' from by omega] at this

/-- The C8 certificate, kernel tier. -/
theorem c8_cert_ok :
    checkCertP (zfamPred c8Family) 73728 c8LiveK c8RhoK c8OmegaK c8ForcedK
      = true :=
  checkCertP_of_parts c8_edges_ok c8_forced_ok

/-- **C8, universal form**: for any reals `X, Y` not both rational, `11`
occurs infinitely often in `X`, or `110` in `Y`, or `00` in `X + Y`, or
`110` in `X + 2Y`, or `101` in `2X + Y`, or `111` in `X + 3Y`. -/
theorem adder_c8_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 X [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 Y [1, 1, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + Y) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + 2 * Y) [1, 1, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (2 * X + Y) [1, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + 3 * Y) [1, 1, 1] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  have hS : (73728 : ℕ) = zfamSize c8Family := by decide
  obtain ⟨ch, hch, hocc⟩ := signed_engine c8Family hS c8_cert_ok X Y hirr
    (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [1, 1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = X from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1, 1, 0] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y) [1, 1, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y = X + 2 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((2:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1, 0, 1] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = 2 * X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y) [1, 1, 1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((3:ℤ):ℝ) * Y = X + 3 * Y from by push_cast; ring] at h

/-- **C8, ln-instance**: `11` occurs infinitely often in the binary
expansion of ln 2, or `110` in ln 3, or `00` in ln 6, or `110` in ln 18,
or `101` in ln 12, or `111` in ln 54. -/
theorem adder_c8_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 2) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 3) [1, 1, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 6) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 18) [1, 1, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 12) [1, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 54) [1, 1, 1] n) := by
  have hlog2 : (2:ℝ) ≠ 0 := by norm_num
  have hlog3 : (3:ℝ) ≠ 0 := by norm_num
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 from by norm_num, Real.log_mul hlog2 hlog3]
  have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18:ℝ) = 2 * 3 ^ 2 from by norm_num, Real.log_mul hlog2 (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2 ^ 2 * 3 from by norm_num, Real.log_mul (by norm_num) hlog3,
      Real.log_pow]
    push_cast; ring
  have h54 : Real.log 54 = Real.log 2 + 3 * Real.log 3 := by
    rw [show (54:ℝ) = 2 * 3 ^ 3 from by norm_num, Real.log_mul hlog2 (by norm_num),
      Real.log_pow]
    push_cast; ring
  rw [h6, h18, h12, h54]
  exact adder_c8_disjunction_universal (Real.log 2) (Real.log 3)
    (Or.inl fun ⟨p, hp⟩ => irrational_log_two ⟨p, hp⟩)

end NormalNumbers.Adder
