import Mathlib

namespace NormalNumbers

noncomputable def distToInteger (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

noncomputable def dyadicEnergyTerm (C : ℤ) (j : ℕ) : ℝ :=
  distToInteger ((C : ℝ) / (2 : ℝ) ^ j) ^ 2

lemma fract_odd_half (k : ℤ) :
    Int.fract (((2 * k + 1 : ℤ) : ℝ) / 2) = (1 / 2 : ℝ) := by
  have h :
      (((2 * k + 1 : ℤ) : ℝ) / 2) = (k : ℝ) + (1 / 2 : ℝ) := by
    push_cast
    ring
  rw [h, Int.fract_intCast_add]
  norm_num [Int.fract]

/-- The first level after the 2-adic valuation contributes exactly 1/4. -/
theorem dyadicEnergyTerm_oddPart (v : ℕ) (k : ℤ)
    (C : ℤ) (hC : C = (2 : ℤ) ^ v * (2 * k + 1)) :
    dyadicEnergyTerm C (v + 1) = (1 / 4 : ℝ) := by
  have hquot :
      (C : ℝ) / (2 : ℝ) ^ (v + 1) =
        (((2 * k + 1 : ℤ) : ℝ) / 2) := by
    rw [hC]
    push_cast
    rw [pow_succ]
    field_simp
  rw [dyadicEnergyTerm, hquot, distToInteger, fract_odd_half]
  norm_num

/-- A finite partial energy already has the universal lower bound 1/4. -/
theorem quarter_le_partial_dyadicEnergy (v : ℕ) (k : ℤ)
    (C : ℤ) (hC : C = (2 : ℤ) ^ v * (2 * k + 1)) :
    (1 / 4 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 (v + 1), dyadicEnergyTerm C j := by
  have hmem : v + 1 ∈ Finset.Icc 1 (v + 1) := by simp
  calc
    (1 / 4 : ℝ) = dyadicEnergyTerm C (v + 1) :=
      (dyadicEnergyTerm_oddPart v k C hC).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 (v + 1), dyadicEnergyTerm C j := by
      apply Finset.single_le_sum (fun j _ => sq_nonneg (distToInteger
        ((C : ℝ) / (2 : ℝ) ^ j))) hmem

/-- Every nonzero integer is a power of two times an odd integer. -/
lemma exists_two_pow_mul_odd_int (C : ℤ) (hC : C ≠ 0) :
    ∃ v : ℕ, ∃ k : ℤ, C = (2 : ℤ) ^ v * (2 * k + 1) := by
  have hn : C.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hC
  obtain ⟨v, m, hm, habs⟩ := Nat.exists_eq_two_pow_mul_odd hn
  obtain ⟨t, ht⟩ := (odd_iff_exists_bit1.mp hm)
  have hcast : (C.natAbs : ℤ) = (2 : ℤ) ^ v * (m : ℤ) := by
    exact_mod_cast habs
  rcases le_total 0 C with hpos | hneg
  · refine ⟨v, t, ?_⟩
    calc
      C = (C.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_nonneg hpos]
      _ = (2 : ℤ) ^ v * (m : ℤ) := hcast
      _ = (2 : ℤ) ^ v * (2 * (t : ℤ) + 1) := by
        rw [ht]
        push_cast
        rfl
  · refine ⟨v, -t - 1, ?_⟩
    calc
      C = -(C.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_nonpos hneg, neg_neg]
      _ = -((2 : ℤ) ^ v * (m : ℤ)) := by rw [hcast]
      _ = (2 : ℤ) ^ v * (2 * (-t - 1) + 1) := by
        rw [ht]
        push_cast
        ring

/-- Every nonzero integer has a finite dyadic energy partial sum at least 1/4. -/
theorem quarter_le_some_partial_dyadicEnergy (C : ℤ) (hC : C ≠ 0) :
    ∃ v : ℕ,
      (1 / 4 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 (v + 1), dyadicEnergyTerm C j := by
  obtain ⟨v, k, hfactor⟩ := exists_two_pow_mul_odd_int C hC
  exact ⟨v, quarter_le_partial_dyadicEnergy v k C hfactor⟩

end NormalNumbers
