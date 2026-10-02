/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterKicked
import NormalNumbers.PiSqBBPProof
import NormalNumbers.PiBBPProof

/-!
# Hypothesis A ⇒ `π²` normal (bases 16 and 2), and `π` in base 2 without the BBP hypothesis

Instances of the machine `hypA_isNormal_of_kicked` on the in-repo proved BBP formulas.
The `π²` edge carries `Irrational (π²)` as a hypothesis argument (Legendre 1794; mathlib proves
only `irrational_pi`, whose Cartwright integrals are private).
-/
namespace NormalNumbers.MasterConjectures
open Polynomial Filter NormalNumbers

/-! ### π² (Bailey–Borwein–Plouffe base-16 formula for π², `PiSqBBP`) -/

/-- The linear factor `8n + k − 8` (at `n = m + 1` it is `8m + k`). -/
noncomputable def piSqLin (k : ℤ) : ℤ[X] := C 8 * X + C (k - 8)

/-- Denominator: `∏_{k=1}^7 (8n + k − 8)²`. -/
noncomputable def piSqQ : ℤ[X] :=
  piSqLin 1 ^ 2 * piSqLin 2 ^ 2 * piSqLin 3 ^ 2 * piSqLin 4 ^ 2 * piSqLin 5 ^ 2 * piSqLin 6 ^ 2 * piSqLin 7 ^ 2

/-- Numerator: `16·Σ_k c_k ∏_{j≠k} (8n + j − 8)²`, so `piSqP/piSqQ = 16·piSqKick (n−1)`. -/
noncomputable def piSqP : ℤ[X] :=
  C 16 * (C (16 : ℤ) * (piSqLin 2 ^ 2 * piSqLin 3 ^ 2 * piSqLin 4 ^ 2 * piSqLin 5 ^ 2 * piSqLin 6 ^ 2 * piSqLin 7 ^ 2)
    + C (-16 : ℤ) * (piSqLin 1 ^ 2 * piSqLin 3 ^ 2 * piSqLin 4 ^ 2 * piSqLin 5 ^ 2 * piSqLin 6 ^ 2 * piSqLin 7 ^ 2)
    + C (-8 : ℤ) * (piSqLin 1 ^ 2 * piSqLin 2 ^ 2 * piSqLin 4 ^ 2 * piSqLin 5 ^ 2 * piSqLin 6 ^ 2 * piSqLin 7 ^ 2)
    + C (-16 : ℤ) * (piSqLin 1 ^ 2 * piSqLin 2 ^ 2 * piSqLin 3 ^ 2 * piSqLin 5 ^ 2 * piSqLin 6 ^ 2 * piSqLin 7 ^ 2)
    + C (-4 : ℤ) * (piSqLin 1 ^ 2 * piSqLin 2 ^ 2 * piSqLin 3 ^ 2 * piSqLin 4 ^ 2 * piSqLin 6 ^ 2 * piSqLin 7 ^ 2)
    + C (-4 : ℤ) * (piSqLin 1 ^ 2 * piSqLin 2 ^ 2 * piSqLin 3 ^ 2 * piSqLin 4 ^ 2 * piSqLin 5 ^ 2 * piSqLin 7 ^ 2)
    + C (2 : ℤ) * (piSqLin 1 ^ 2 * piSqLin 2 ^ 2 * piSqLin 3 ^ 2 * piSqLin 4 ^ 2 * piSqLin 5 ^ 2 * piSqLin 6 ^ 2))

theorem piSqQ_eval (m : ℕ) : ((piSqQ.eval ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ)
    = (8 * (m : ℝ) + 1) ^ 2 * (8 * m + 2) ^ 2 * (8 * m + 3) ^ 2 * (8 * m + 4) ^ 2
      * (8 * m + 5) ^ 2 * (8 * m + 6) ^ 2 * (8 * m + 7) ^ 2 := by
  simp [piSqQ, piSqLin]; ring

theorem piSq_kick_eq (m : ℕ) :
    ((piSqP.eval ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ) / ((piSqQ.eval ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ)
      = piSqShiftKick (m + 1) := by
  rw [piSqQ_eval, piSqShiftKick, Nat.add_sub_cancel, piSqKick]
  have h1 : (8 * (m : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (8 * (m : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (8 * (m : ℝ) + 3) ≠ 0 := by positivity
  have h4 : (8 * (m : ℝ) + 4) ≠ 0 := by positivity
  have h5 : (8 * (m : ℝ) + 5) ≠ 0 := by positivity
  have h6 : (8 * (m : ℝ) + 6) ≠ 0 := by positivity
  have h7 : (8 * (m : ℝ) + 7) ≠ 0 := by positivity
  simp [piSqP, piSqLin]
  field_simp
  ring

theorem piSqQ_natDegree : piSqQ.natDegree = 14 := by unfold piSqQ piSqLin; compute_degree!
theorem piSqP_natDegree_le : piSqP.natDegree ≤ 12 := by unfold piSqP piSqLin; compute_degree

theorem piSq_hr (n : ℕ) (hn : 1 ≤ n) :
    ((piSqP.eval (n : ℤ) : ℤ) : ℝ) / ((piSqQ.eval (n : ℤ) : ℤ) : ℝ) = piSqShiftKick n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact piSq_kick_eq m

theorem piSqQ_ne (n : ℕ) (hn : 1 ≤ n) : piSqQ.eval (n : ℤ) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  have := piSqQ_eval m
  rw [h] at this
  have : (0 : ℝ) < (8 * (m : ℝ) + 1) ^ 2 * (8 * m + 2) ^ 2 * (8 * m + 3) ^ 2 * (8 * m + 4) ^ 2
      * (8 * m + 5) ^ 2 * (8 * m + 6) ^ 2 * (8 * m + 7) ^ 2 := by positivity
  push_cast at *; linarith

theorem piSqP_ne : piSqP ≠ 0 := by
  intro h
  have := piSq_kick_eq 0
  rw [h] at this
  simp [piSqShiftKick, piSqKick] at this
  norm_num at this

theorem tendsto_piSq_tail (hπ : PiSqBBP) :
    Tendsto (fun n : ℕ => ((16 : ℕ) : ℝ) ^ n * (Real.pi ^ 2 - kickedPartial 16 piSqShiftKick n))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => 52 * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (52 : ℝ)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  refine (kicked_tail_abs_le (b := 16) (by norm_num) n (hasSum_piSqShiftKick hπ)
    (fun m hm => abs_piSqShiftKick_le hn hm)).trans ?_
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by positivity)]
  push_cast
  field_simp
  nlinarith

/-- **Hypothesis A ⇒ `π²` normal in base 16**, given the irrationality of `π²` (Legendre 1794;
not in mathlib).  The BBP-type π² formula (`piSqBBP_proved`) enters unconditionally; its kicks
change sign, which the two-sided tail lemma absorbs. -/
theorem hypA_piSq_base16 (hA : BaileyCrandallHypA) (hirr : Irrational (Real.pi ^ 2)) :
    IsNormal 16 (Real.pi ^ 2) :=
  hypA_isNormal_of_kicked hA piSqP piSqQ 16 (by norm_num) piSqP_ne
    (by rw [piSqQ_natDegree]; linarith [piSqP_natDegree_le]) piSqQ_ne piSqShiftKick piSq_hr
    _ hirr (tendsto_piSq_tail piSqBBP_proved)

/-- … and in base 2 (`16 = 2⁴`). -/
theorem hypA_piSq_base2 (hA : BaileyCrandallHypA) (hirr : Irrational (Real.pi ^ 2)) :
    IsNormal 2 (Real.pi ^ 2) :=
  isNormal_of_isNormal_pow (b := 2) (K := 4) le_rfl (by norm_num) (hypA_piSq_base16 hA hirr)

/-- Hypothesis A alone (BBP formula now proved in-repo) gives `π` normal in base 2. -/
theorem hypA_pi_base2_uncond (hA : BaileyCrandallHypA) : IsNormal 2 Real.pi :=
  isNormal_of_isNormal_pow (b := 2) (K := 4) le_rfl (by norm_num)
    (hypA_pi_base16 hA piBBP_proved)

end NormalNumbers.MasterConjectures
