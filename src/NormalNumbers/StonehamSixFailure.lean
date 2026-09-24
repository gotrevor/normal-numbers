import NormalNumbers.Stoneham
import NormalNumbers.AbelianNormal

/-!
# Failures of 2026-09-23, formalized

1. **α₂,₃ is not even simply normal in base 6** (so no abelian-normal "natural separation").
   In base 6 the term `1/(3ᵐ 2^{3ᵐ}) = 3^{3ᵐ−m}/6^{3ᵐ}` occupies positions `≈ [0.387·3ᵐ, 3ᵐ]`, and
   the next term starts near `1.161·3ᵐ`.  So the digits at positions `(3ᵐ, 1.1·3ᵐ]` are all `0`:
   below position `p`, the head `Σ_{k≤m}` times `6ᵖ` is an integer, and
   `6ᵖ · Σ_{k>m} < 1` because `1.1·log₂6 ≈ 2.84 < 3`.  Hence at `N ≈ 1.1·3ᵐ` the zero frequency
   is `≥ (1/6 + 0.1·5/6)/1.1 − o(1) ≈ 0.227`, not `1/6`.  Bailey–Borwein (2012) first proved
   base-6 non-normality; this is that mechanism, not a new result.  Probe:
   `probes/abelian_stoneham_and_times3.py`, which measures freq(0) = .3217 at N = 2·10⁵.
2. **×3 abelian lifting**, frozen but PARKED.  The hexSwap example (`AbelianBinaryExample.lean`)
   does not refute it: 3ξ is far from abelian-normal in the probe.  A dimension count suggests a
   single multiplier is too weak; the all-odd-multiplier version is plausible and may be classical.
-/

open Finset Filter Topology

namespace NormalNumbers.Failures

/-- `6^10 < 2^26`, the numeric margin that makes `6^{1.1·3^m}` fit under `2^{3^{m+1}}`. -/
theorem two_mul_six_pow_lt_two_pow {m p : ℕ} (hm : 2 ≤ m) (hp1 : 1 ≤ p)
    (hp : 10 * p ≤ 11 * 3 ^ m) : 2 * 6 ^ p < 2 ^ 3 ^ (m + 1) := by
  have h9 : 9 ≤ 3 ^ m := by
    calc (9:ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hexp : 10 + 26 * p ≤ 30 * 3 ^ m := by omega
  have hbase : (6:ℕ) ^ 10 < 2 ^ 26 := by norm_num
  by_contra hcon
  push_neg at hcon
  have hle : (2 ^ 3 ^ (m + 1)) ^ 10 ≤ (2 * 6 ^ p) ^ 10 := Nat.pow_le_pow_left hcon 10
  have hlt : (2 * 6 ^ p) ^ 10 < (2 ^ 3 ^ (m + 1)) ^ 10 := by
    have h1 : ((6:ℕ) ^ 10) ^ p < (2 ^ 26) ^ p := Nat.pow_lt_pow_left hbase (by omega)
    have h2 : (2 * 6 ^ p) ^ 10 = 2 ^ 10 * ((6:ℕ) ^ 10) ^ p := by
      rw [Nat.mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm p 10]
    have h3 : ((2:ℕ) ^ 26) ^ p = 2 ^ (26 * p) := by rw [← pow_mul]
    have h4 : ((2:ℕ) ^ 3 ^ (m + 1)) ^ 10 = 2 ^ (30 * 3 ^ m) := by
      rw [← pow_mul, pow_succ]; ring_nf
    calc (2 * 6 ^ p) ^ 10 = 2 ^ 10 * ((6:ℕ) ^ 10) ^ p := h2
      _ < 2 ^ 10 * (2 ^ 26) ^ p := by
          exact mul_lt_mul_of_pos_left h1 (by positivity)
      _ = 2 ^ (10 + 26 * p) := by rw [h3, pow_add]
      _ ≤ 2 ^ (30 * 3 ^ m) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ 3 ^ (m + 1)) ^ 10 := h4.symm
  omega

/-- **Forced zeros.**  For all large `m`, the base-6 digits of `α₂,₃` with index in
`[3ᵐ, 11·3ᵐ/10)` are `0` (index `i` is position `i + 1`). -/
theorem stoneham23_digit_six_eq_zero :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : ℕ, 3 ^ m ≤ i → i < 11 * 3 ^ m / 10 →
      digitOf 6 (Int.fract stoneham23) i = 0 := by
  refine ⟨2, fun m hm i hi hi' => ?_⟩
  have hx : Int.fract stoneham23 = stoneham23 :=
    Int.fract_eq_self.mpr ⟨stoneham23_mem_Ico.1, stoneham23_mem_Ico.2⟩
  set p : ℕ := i + 1 with hpdef
  have h9 : 9 ≤ 3 ^ m := by
    calc (9:ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp10 : 10 * p ≤ 11 * 3 ^ m := by
    have := Nat.lt_succ_iff.mp (Nat.lt_succ_of_lt hi')
    have hdiv : 10 * (11 * 3 ^ m / 10) ≤ 11 * 3 ^ m := Nat.mul_div_le _ _ |>.trans_eq rfl
    have hdiv' : 10 * (11 * 3 ^ m / 10) ≤ 11 * 3 ^ m := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (11 * 3 ^ m) 10
    omega
  have hp3m : 3 ^ m < p := by omega
  -- the scaled series
  set g : ℕ → ℝ := fun j => (6 : ℝ) ^ p * sterm j with hg
  have hg_sum : Summable g := summable_sterm.mul_left _
  have hg_pos : ∀ j, 0 < g j := fun j => by
    have := sterm_pos j; simp only [hg]; positivity
  have hmul : stoneham23 * (6 : ℝ) ^ p = ∑' j, g j := by
    rw [tsum_mul_left, mul_comm]; rfl
  have hshift_sum : Summable fun j => g (j + m) := (summable_nat_add_iff m).2 hg_sum
  have hsplit : ∑' j, g j = (∑ j ∈ Finset.range m, g j) + ∑' j, g (j + m) :=
    (hg_sum.sum_add_tsum_nat_add m).symm
  set T : ℝ := ∑' j, g (j + m) with hT
  set A : ℕ := ∑ j ∈ Finset.range m, 2 ^ (p - 3 ^ (j + 1)) * 3 ^ (p - (j + 1)) with hA
  -- head is the integer `A`
  have hHead : (∑ j ∈ Finset.range m, g j) = (A : ℝ) := by
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := Finset.mem_range.mp hj
    have h3j : 3 ^ (j + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hjm
    have hja : 3 ^ (j + 1) < p := lt_of_le_of_lt h3j hp3m
    have hjb : j + 1 < p := by
      have : j + 1 ≤ 3 ^ (j + 1) := Nat.lt_pow_self (by norm_num) |>.le
      omega
    have h2 : (2 : ℝ) ^ (p - 3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1)) = 2 ^ p := by
      rw [← pow_add]; congr 1; omega
    have h3 : (3 : ℝ) ^ (p - (j + 1)) * 3 ^ (j + 1) = 3 ^ p := by
      rw [← pow_add]; congr 1; omega
    have h6 : (6 : ℝ) ^ p = 2 ^ p * 3 ^ p := by rw [← mul_pow]; norm_num
    simp only [hg, sterm]
    rw [mul_one_div, div_eq_iff (by positivity), h6, ← h2, ← h3]
    ring
  have hA6 : 6 ∣ A := by
    rw [hA]
    refine Finset.dvd_sum fun j hj => ?_
    have hjm : j < m := Finset.mem_range.mp hj
    have h3j : 3 ^ (j + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hjm
    have hja : 3 ^ (j + 1) < p := lt_of_le_of_lt h3j hp3m
    have hjb : j + 1 < p := by
      have : j + 1 ≤ 3 ^ (j + 1) := Nat.lt_pow_self (by norm_num) |>.le
      omega
    obtain ⟨a, ha⟩ : ∃ a, p - 3 ^ (j + 1) = a + 1 := ⟨p - 3 ^ (j + 1) - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, p - (j + 1) = b + 1 := ⟨p - (j + 1) - 1, by omega⟩
    rw [ha, hb, pow_succ, pow_succ]
    exact ⟨2 ^ a * 3 ^ b, by ring⟩
  -- tail is positive and below one
  have hT_pos : 0 < T := by
    rw [hT]; exact Summable.tsum_pos hshift_sum (fun j => (hg_pos _).le) 0 (hg_pos _)
  have hT_lt : T < 1 := by
    have hterm : ∀ j, g (j + m) ≤ ((6:ℝ) ^ p * sterm m) * (1 / 2) ^ j := by
      intro j
      have hexp : 3 ^ (m + 1) + j ≤ 3 ^ (j + m + 1) := by
        have hj3 : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
        have hP : 1 ≤ 3 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
        calc 3 ^ (m + 1) + j ≤ 3 ^ (m + 1) * (j + 1) := by nlinarith
          _ ≤ 3 ^ (m + 1) * 3 ^ j := Nat.mul_le_mul_left _ hj3
          _ = 3 ^ (j + m + 1) := by rw [← pow_add]; congr 1; omega
      have hkey : (3 : ℝ) ^ (m + 1) * 2 ^ (3 ^ (m + 1)) * 2 ^ j
          ≤ 3 ^ (j + m + 1) * 2 ^ (3 ^ (j + m + 1)) := by
        have h3 : (3 : ℝ) ^ (m + 1) ≤ 3 ^ (j + m + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) ^ (3 ^ (m + 1)) * 2 ^ j ≤ 2 ^ (3 ^ (j + m + 1)) := by
          rw [← pow_add]; exact pow_le_pow_right₀ one_le_two hexp
        calc (3 : ℝ) ^ (m + 1) * 2 ^ (3 ^ (m + 1)) * 2 ^ j
            = 3 ^ (m + 1) * (2 ^ (3 ^ (m + 1)) * 2 ^ j) := by ring
          _ ≤ 3 ^ (j + m + 1) * 2 ^ (3 ^ (j + m + 1)) :=
              mul_le_mul h3 h2 (by positivity) (by positivity)
      have hs : sterm (j + m) ≤ sterm m * (1 / 2) ^ j := by
        simp only [sterm, div_pow, one_pow, div_mul_div_comm, one_mul]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey
      simp only [hg]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hgeom : Summable fun j : ℕ => ((6:ℝ) ^ p * sterm m) * (1 / 2) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift_sum.tsum_le_tsum hterm hgeom
    rw [hT]
    refine lt_of_le_of_lt hle ?_
    rw [tsum_mul_left, tsum_geometric_two]
    have hnat : (2 : ℕ) * 6 ^ p < 2 ^ 3 ^ (m + 1) :=
      two_mul_six_pow_lt_two_pow hm (by omega) hp10
    have hnatR : (2 : ℝ) * 6 ^ p < 2 ^ 3 ^ (m + 1) := by exact_mod_cast hnat
    have h31 : (1 : ℝ) ≤ 3 ^ (m + 1) := one_le_pow₀ (by norm_num)
    have hpos : (0:ℝ) < 2 ^ 3 ^ (m + 1) := by positivity
    simp only [sterm]
    rw [mul_one_div, div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith [pow_pos (show (0:ℝ) < 6 by norm_num) p, hpos]
  -- read off the digit
  have hval : stoneham23 * (6 : ℝ) ^ p = (A : ℝ) + T := by rw [hmul, hsplit, hHead]
  have hfl : ⌊stoneham23 * (6 : ℝ) ^ p⌋ = (A : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  unfold digitOf
  rw [hx]
  have hcast : ((6:ℕ) : ℝ) = (6:ℝ) := by norm_num
  rw [hcast, ← hpdef, hfl, Int.toNat_natCast]
  omega

/-- **α₂,₃ is not simply normal in base 6**: the frequency of the digit `0` does not tend to
`1/6`. -/
theorem not_simplyNormal_six_stoneham23 :
    ¬ Tendsto (fun n : ℕ =>
        (countOccurrences [0] ((List.range n).map (digitOf 6 (Int.fract stoneham23))) : ℝ) / n)
      atTop (𝓝 (1 / 6)) := by
  sorry

/-- Hence not normal in base 6 (Bailey–Borwein 2012). -/
theorem not_isNormal_six_stoneham23 : ¬ IsNormal 6 stoneham23 := by
  sorry

/-- **×3 abelian lifting (PARKED, ~20%).** -/
def TimesThreeLifting : Prop :=
  ∀ x : ℝ, Abelian.IsAbelianNormalTwo (digitOf 2 (Int.fract x)) →
    Abelian.IsAbelianNormalTwo (digitOf 2 (Int.fract (3 * x))) → IsNormal 2 x

/-- **Odd-multiplier abelian lifting (open, ~70%, literature check pending).** -/
def OddMultiplierLifting : Prop :=
  ∀ x : ℝ, (∀ q : ℕ, Odd q → Abelian.IsAbelianNormalTwo (digitOf 2 (Int.fract ((q : ℝ) * x)))) →
    IsNormal 2 x

theorem oddMultiplierLifting_of_timesThree (h : TimesThreeLifting) : OddMultiplierLifting := by
  sorry

end NormalNumbers.Failures
