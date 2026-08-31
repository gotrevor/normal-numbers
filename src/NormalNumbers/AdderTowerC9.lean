/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderTowerC9Chunk0
import NormalNumbers.AdderTowerC9Chunk1
import NormalNumbers.AdderTowerC9Chunk2
import NormalNumbers.AdderTowerC9Chunk3
import NormalNumbers.AdderTowerC9Chunk4a
import NormalNumbers.AdderTowerC9Chunk4b
import NormalNumbers.LnTwoIrrational

/-!
# C9: the second channel set (adder-family census)

A genuinely different two-track base-2 disjunction — NOT the complement
(C8) nor a single-word swap of the frozen flagship, but a distinct channel
assignment (`docs/adder-family-2026-08-29.md`, "second channel set"): the
constants ln2, ln3, ln6, ln12, ln24, ln72 with words `00, 001, 11, 00, 00,
010`.  The cheapest certified family in the tower (ambient 30720, 28 live —
4× smaller than the base flagship).  Data-swap instance of `signed_engine`;
kernel tier, trust triple.
-/

namespace NormalNumbers.Adder

open NormalNumbers

set_option maxHeartbeats 8000000 in
theorem c9_forced_ok :
    checkForcedP (zfamPred c9Family) 30720 c9LiveK c9ForcedK = true := by
  decide +kernel

theorem c9_edges_ok :
    checkEdgesP (zfamPred c9Family) 30720 c9LiveK c9RhoK c9OmegaK c9ForcedK
      = true := by
  apply checkEdgesP_of_edgeOkP
  intro s' hs'
  have c0 := checkEdgesOnP_spec c9_chunk0
  have c1 := checkEdgesOnP_spec c9_chunk1
  have c2 := checkEdgesOnP_spec c9_chunk2
  have c3 := checkEdgesOnP_spec c9_chunk3
  have c4a := checkEdgesOnP_spec c9_chunk4a
  have c4b := checkEdgesOnP_spec c9_chunk4b
  rcases (by omega : s' < 6144 ∨ (6144 ≤ s' ∧ s' < 12288)
      ∨ (12288 ≤ s' ∧ s' < 18432) ∨ (18432 ≤ s' ∧ s' < 24576)
      ∨ (24576 ≤ s' ∧ s' < 27648) ∨ (27648 ≤ s' ∧ s' < 30720)) with
    h | h | h | h | h | h
  · have := c0 s' h
    rwa [Nat.zero_add] at this
  · have := c1 (s' - 6144) (by omega)
    rwa [show 6144 + (s' - 6144) = s' from by omega] at this
  · have := c2 (s' - 12288) (by omega)
    rwa [show 12288 + (s' - 12288) = s' from by omega] at this
  · have := c3 (s' - 18432) (by omega)
    rwa [show 18432 + (s' - 18432) = s' from by omega] at this
  · have := c4a (s' - 24576) (by omega)
    rwa [show 24576 + (s' - 24576) = s' from by omega] at this
  · have := c4b (s' - 27648) (by omega)
    rwa [show 27648 + (s' - 27648) = s' from by omega] at this

/-- The C9 certificate, kernel tier. -/
theorem c9_cert_ok :
    checkCertP (zfamPred c9Family) 30720 c9LiveK c9RhoK c9OmegaK c9ForcedK
      = true :=
  checkCertP_of_parts c9_edges_ok c9_forced_ok

/-- **C9, universal form**: for any reals `X, Y` not both rational, `00`
occurs infinitely often in `X`, or `001` in `Y`, or `11` in `X + Y`, or
`00` in `2X + Y`, or `00` in `3X + Y`, or `010` in `3X + 2Y`. -/
theorem adder_c9_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 X [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 Y [0, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (X + Y) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (2 * X + Y) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (3 * X + Y) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (3 * X + 2 * Y) [0, 1, 0] n) := by
  have hirr : Irrational X ∨ Irrational Y := by
    rcases hXY with hX | hY
    · exact Or.inl fun ⟨p, hp⟩ => hX ⟨p, hp⟩
    · exact Or.inr fun ⟨q, hq⟩ => hY ⟨q, hq⟩
  have hS : (30720 : ℕ) = zfamSize c9Family := by decide
  obtain ⟨ch, hch, hocc⟩ := signed_engine c9Family hS c9_cert_ok X Y hirr
    (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((0:ℤ):ℝ) * Y = X from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 0, 1] n := hocc
    rwa [show ((0:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [1, 1] n := hocc
    rwa [show ((1:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((2:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((2:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = 2 * X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((3:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y) [0, 0] n := hocc
    rwa [show ((3:ℤ):ℝ) * X + ((1:ℤ):ℝ) * Y = 3 * X + Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have h : ∀ N, ∃ n, N ≤ n ∧
        OccursAt 2 (((3:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y) [0, 1, 0] n := hocc
    rwa [show ((3:ℤ):ℝ) * X + ((2:ℤ):ℝ) * Y = 3 * X + 2 * Y from by
      push_cast; ring] at h

/-- **C9, ln-instance**: `00` occurs infinitely often in the binary
expansion of ln 2, or `001` in ln 3, or `11` in ln 6, or `00` in ln 12,
or `00` in ln 24, or `010` in ln 72. -/
theorem adder_c9_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 2) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 3) [0, 0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 6) [1, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 12) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 24) [0, 0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 72) [0, 1, 0] n) := by
  have hlog2 : (2:ℝ) ≠ 0 := by norm_num
  have hlog3 : (3:ℝ) ≠ 0 := by norm_num
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 from by norm_num, Real.log_mul hlog2 hlog3]
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2 ^ 2 * 3 from by norm_num, Real.log_mul (by norm_num) hlog3,
      Real.log_pow]
    push_cast; ring
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24:ℝ) = 2 ^ 3 * 3 from by norm_num, Real.log_mul (by norm_num) hlog3,
      Real.log_pow]
    push_cast; ring
  have h72 : Real.log 72 = 3 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (72:ℝ) = 2 ^ 3 * 3 ^ 2 from by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [h6, h12, h24, h72]
  exact adder_c9_disjunction_universal (Real.log 2) (Real.log 3)
    (Or.inl fun ⟨p, hp⟩ => irrational_log_two ⟨p, hp⟩)

end NormalNumbers.Adder
