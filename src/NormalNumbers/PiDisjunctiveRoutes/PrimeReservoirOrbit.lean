/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.PrimeReservoirStep

/-!
# Route 2: the reservoir is a ×16 orbit of a partial BBP-type sum

Combining `bbpPrimeReservoir_succ` with `bbpReservoirExit_mod_one`, the reservoir is,
modulo 1, exactly `16ⁿ · ρₙ` where `ρₙ` is a partial sum of a prime-indexed series with
`O(1/k)` numerators.  So the reservoir carries no arithmetic beyond the digits of the
limit constant `ρ`.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

/-- Kick of the reservoir at step `k`, after the exit collapse. -/
noncomputable def reservoirKick (k : ℕ) : ℝ :=
  -(if Nat.Prime (4 * k + 1) then 64 / (4 * (k : ℝ) + 1) else 0) + bbpReservoirEntry k

/-- Partial sums of the reservoir constant `ρ = Σ kick_k / 16^{k+1}`. -/
noncomputable def reservoirConstPartial (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, reservoirKick k / 16 ^ (k + 1)

/-- Exact: `Rₙ ≡ 16ⁿ ρₙ (mod 1)`. -/
theorem bbpPrimeReservoir_eq_orbit (n : ℕ) :
    ∃ z : ℤ, bbpPrimeReservoir n = z + 16 ^ n * reservoirConstPartial n := by
  induction n with
  | zero => exact ⟨0, by simp [bbpPrimeReservoir, reservoirConstPartial]⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := bbpReservoirExit_mod_one n
    refine ⟨16 * z - w, ?_⟩
    rw [bbpPrimeReservoir_succ, hz, hw, reservoirConstPartial, reservoirConstPartial,
      Finset.sum_range_succ, reservoirKick]
    have h : (16 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma div_bounds {c x : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : (k : ℝ) + 1 ≤ x) :
    0 ≤ c / x ∧ c / x ≤ c / ((k : ℝ) + 1) :=
  ⟨div_nonneg hc (by linarith), div_le_div_of_nonneg_left hc (by positivity) hx⟩

theorem abs_reservoirKick_le (k : ℕ) : |reservoirKick k| ≤ 144 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨a1, a2⟩ := div_bounds (c := 64) (x := 4 * (k : ℝ) + 1) k (by norm_num) (by linarith)
  obtain ⟨b1, b2⟩ := div_bounds (c := 4) (x := 8 * (k : ℝ) + 1) k (by norm_num) (by linarith)
  obtain ⟨c1, c2⟩ := div_bounds (c := 1) (x := 8 * (k : ℝ) + 5) k (by norm_num) (by linarith)
  have e64 : (64 : ℝ) / ((k : ℝ) + 1) = 64 * (1 / ((k : ℝ) + 1)) := by ring
  have e4 : (4 : ℝ) / ((k : ℝ) + 1) = 4 * (1 / ((k : ℝ) + 1)) := by ring
  have e144 : (144 : ℝ) / ((k : ℝ) + 1) = 144 * (1 / ((k : ℝ) + 1)) := by ring
  rw [reservoirKick, bbpReservoirEntry, reservoirTerm, pow_one, abs_le]
  constructor <;> split_ifs <;> nlinarith

theorem summable_reservoirKick :
    Summable fun k : ℕ => reservoirKick k / 16 ^ (k + 1) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => 144 * (1 / 16 : ℝ) ^ (k + 1)) ?_ ?_
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _ |>.comp_injective
      (add_left_injective 1)
  · intro k
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 ^ (k + 1)),
      one_div_pow, ← div_eq_mul_one_div]
    gcongr
    calc |reservoirKick k| ≤ 144 / ((k : ℝ) + 1) := abs_reservoirKick_le k
    _ ≤ 144 := div_le_self (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

/-- The reservoir constant `ρ = Σ_k kick_k / 16^{k+1}`, a prime-indexed BBP-type series. -/
noncomputable def reservoirConst : ℝ := ∑' k, reservoirKick k / 16 ^ (k + 1)

/-- The reservoir is the ×16 orbit of the constant `ρ`, up to an integer and `10/(n+1)`. -/
theorem bbpPrimeReservoir_near_orbit (n : ℕ) :
    ∃ z : ℤ, |bbpPrimeReservoir n - z - 16 ^ n * reservoirConst| ≤ 10 / ((n : ℝ) + 1) := by
  obtain ⟨z, hz⟩ := bbpPrimeReservoir_eq_orbit n
  refine ⟨z, ?_⟩
  have hs := summable_reservoirKick
  have key := hs.sum_add_tsum_nat_add n
  have htail : 16 ^ n * reservoirConst - 16 ^ n * reservoirConstPartial n =
      ∑' i, reservoirKick (i + n) / 16 ^ (i + 1) := by
    rw [reservoirConst, ← key, reservoirConstPartial, mul_add, add_sub_cancel_left,
      ← tsum_mul_left]
    congr 1; ext i
    rw [show i + n + 1 = (i + 1) + n by ring, pow_add]
    field_simp
  rw [hz, show (z : ℝ) + 16 ^ n * reservoirConstPartial n - z - 16 ^ n * reservoirConst =
    -(16 ^ n * reservoirConst - 16 ^ n * reservoirConstPartial n) by ring, abs_neg, htail]
  have hs' : Summable fun i : ℕ => (144 / ((n : ℝ) + 1)) * (1 / 16 : ℝ) ^ (i + 1) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)).mul_left _
  have hb : ∀ i : ℕ, ‖reservoirKick (i + n) / 16 ^ (i + 1)‖ ≤
      (144 / ((n : ℝ) + 1)) * (1 / 16 : ℝ) ^ (i + 1) := by
    intro i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 ^ (i + 1)),
      one_div_pow, ← div_eq_mul_one_div]
    gcongr
    calc |reservoirKick (i + n)| ≤ 144 / (((i + n : ℕ) : ℝ) + 1) := abs_reservoirKick_le _
    _ ≤ 144 / ((n : ℝ) + 1) := by gcongr; push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  calc |∑' i, reservoirKick (i + n) / 16 ^ (i + 1)|
      ≤ ∑' i, (144 / ((n : ℝ) + 1)) * (1 / 16 : ℝ) ^ (i + 1) := by
        rw [← Real.norm_eq_abs]; exact tsum_of_norm_bounded hs'.hasSum hb
    _ = (144 / ((n : ℝ) + 1)) * (1 / 15) := by
        rw [tsum_mul_left]; congr 1
        simp_rw [pow_succ]
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
    _ ≤ 10 / ((n : ℝ) + 1) := by
        rw [div_mul_eq_mul_div]; gcongr; norm_num

end NormalNumbers.PiDisjunctiveRoutes
