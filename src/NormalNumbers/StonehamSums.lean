/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Stoneham
import NormalNumbers.ReciprocalNormal
import NormalNumbers.StonehamSixFailure

/-!
# Sums of Stoneham constants

The pair `α₂,₃`, `α₄,₃` is arithmetically coupled: after putting the two series
over powers of four, the `k`-th coefficient is an integer because
`3^(k+1) ∣ 2^(3^k) + 1`.  Consequently the binary expansion of their sum has zero windows of
asymptotic relative length `1/3`, obstructing even simple normality.
-/

namespace NormalNumbers

open ReciprocalNormal
open Filter Topology

/-- The Stoneham constant `α_{B,c} = Σ_{m≥1} 1/(c^m · B^(c^m))`. -/
noncomputable def stonehamAlpha (B c : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((c : ℝ) ^ (n + 1) * (B : ℝ) ^ (c ^ (n + 1)))

theorem stonehamAlpha_two_three : stonehamAlpha 2 3 = stoneham23 := by
  rfl

/-- The combined summand of `α₂,₃ + α₄,₃`. -/
noncomputable def stonehamSumTerm (j : ℕ) : ℝ :=
  1 / ((3 : ℝ) ^ (j + 1) * 2 ^ (3 ^ (j + 1))) +
    1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1)))

/-- The LTE divisibility which makes every regrouped Stoneham summand an integer block. -/
theorem three_pow_succ_dvd_two_pow_three_pow_add_one (k : ℕ) :
    3 ^ (k + 1) ∣ 2 ^ (3 ^ k) + 1 := by
  have hv := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide) (by norm_num) (by norm_num) (Odd.pow (by decide) : Odd (3 ^ k))
  norm_num [padicValNat.prime_pow] at hv
  exact (padicValNat_dvd_iff_le (by positivity)).2 (by omega)

theorem summable_stonehamAlpha_four_three_term : Summable fun j : ℕ =>
    1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1))) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) summable_sterm
  unfold sterm
  apply div_le_div_of_nonneg_left one_pos.le (by positivity)
  gcongr
  norm_num

theorem summable_stonehamSumTerm : Summable stonehamSumTerm := by
  exact summable_sterm.add summable_stonehamAlpha_four_three_term

/-- The two Stoneham series combine termwise into `stonehamSumTerm`. -/
theorem stoneham_sum_eq_tsum :
    stonehamAlpha 2 3 + stonehamAlpha 4 3 = ∑' j, stonehamSumTerm j := by
  rw [stonehamAlpha_two_three]
  unfold stoneham23 stonehamAlpha stonehamSumTerm
  exact (summable_sterm.tsum_add summable_stonehamAlpha_four_three_term).symm

/-- Once scaled past its right endpoint, a combined summand is an integer binary block. -/
theorem stonehamSumTerm_scaled_eq_block (j p : ℕ) (hp : 2 * 3 ^ (j + 1) ≤ p) :
    (2 : ℝ) ^ p * stonehamSumTerm j =
      (2 ^ (p - 2 * 3 ^ (j + 1)) *
        ((2 ^ (3 ^ (j + 1)) + 1) / 3 ^ (j + 1)) : ℕ) := by
  have hdvd : 3 ^ (j + 1) ∣ 2 ^ (3 ^ (j + 1)) + 1 :=
    (pow_dvd_pow 3 (by omega : j + 1 ≤ j + 2)).trans
      (three_pow_succ_dvd_two_pow_three_pow_add_one (j + 1))
  set q : ℕ := (2 ^ (3 ^ (j + 1)) + 1) / 3 ^ (j + 1) with hq
  have hqN : 3 ^ (j + 1) * q = 2 ^ (3 ^ (j + 1)) + 1 := by
    rw [hq]
    exact Nat.mul_div_cancel' hdvd
  have hqR : (3 : ℝ) ^ (j + 1) * q = 2 ^ (3 ^ (j + 1)) + 1 := by
    exact_mod_cast hqN
  have hpow : (2 : ℝ) ^ (p - 2 * 3 ^ (j + 1)) * 2 ^ (2 * 3 ^ (j + 1)) = 2 ^ p := by
    rw [← pow_add]
    congr 1
    omega
  change (2 : ℝ) ^ p *
      (1 / (3 ^ (j + 1) * 2 ^ (3 ^ (j + 1))) +
        1 / (3 ^ (j + 1) * 4 ^ (3 ^ (j + 1)))) = _
  rw [show (4 : ℝ) ^ (3 ^ (j + 1)) = 2 ^ (2 * 3 ^ (j + 1)) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]
  rw [show ((2 ^ (p - 2 * 3 ^ (j + 1)) * q : ℕ) : ℝ) =
      (2 : ℝ) ^ (p - 2 * 3 ^ (j + 1)) * q by push_cast; rfl]
  field_simp
  rw [← hpow]
  rw [show (2 : ℝ) ^ (2 * 3 ^ (j + 1)) =
      2 ^ (3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1)) by
    rw [← pow_add]; congr 1; omega]
  have hscaled := congrArg (fun z : ℝ =>
    2 ^ (p - 2 * 3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1)) *
      (2 ^ (3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1))) * z) hqR
  linear_combination -hscaled

/-- Later combined summands decrease at least geometrically. -/
theorem stonehamSumTerm_shift_le (k j : ℕ) :
    stonehamSumTerm (j + k) ≤ stonehamSumTerm k * (1 / 2 : ℝ) ^ j := by
  have hexp : 3 ^ (k + 1) + j ≤ 3 ^ (j + k + 1) := by
    have hj3 : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
    have hP : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc
      3 ^ (k + 1) + j ≤ 3 ^ (k + 1) * (j + 1) := by nlinarith
      _ ≤ 3 ^ (k + 1) * 3 ^ j := Nat.mul_le_mul_left _ hj3
      _ = 3 ^ (j + k + 1) := by rw [← pow_add]; congr 1; omega
  have hkey2 : (3 : ℝ) ^ (k + 1) * 2 ^ (3 ^ (k + 1)) * 2 ^ j
      ≤ 3 ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1)) := by
    have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (j + k + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (3 ^ (k + 1)) * 2 ^ j ≤ 2 ^ (3 ^ (j + k + 1)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ one_le_two hexp
    calc
      (3 : ℝ) ^ (k + 1) * 2 ^ (3 ^ (k + 1)) * 2 ^ j =
          3 ^ (k + 1) * (2 ^ (3 ^ (k + 1)) * 2 ^ j) := by ring
      _ ≤ 3 ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1)) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
  have hkey4 : (3 : ℝ) ^ (k + 1) * 4 ^ (3 ^ (k + 1)) * 2 ^ j
      ≤ 3 ^ (j + k + 1) * 4 ^ (3 ^ (j + k + 1)) := by
    have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (j + k + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h24 : (2 : ℝ) ^ j ≤ 4 ^ j := by gcongr <;> norm_num
    have h4 : (4 : ℝ) ^ (3 ^ (k + 1)) * 2 ^ j ≤ 4 ^ (3 ^ (j + k + 1)) := by
      calc
        (4 : ℝ) ^ (3 ^ (k + 1)) * 2 ^ j ≤ 4 ^ (3 ^ (k + 1)) * 4 ^ j :=
          mul_le_mul_of_nonneg_left h24 (by positivity)
        _ = 4 ^ (3 ^ (k + 1) + j) := (pow_add _ _ _).symm
        _ ≤ 4 ^ (3 ^ (j + k + 1)) := pow_le_pow_right₀ (by norm_num) hexp
    calc
      (3 : ℝ) ^ (k + 1) * 4 ^ (3 ^ (k + 1)) * 2 ^ j =
          3 ^ (k + 1) * (4 ^ (3 ^ (k + 1)) * 2 ^ j) := by ring
      _ ≤ 3 ^ (j + k + 1) * 4 ^ (3 ^ (j + k + 1)) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
  have hs2 : 1 / ((3 : ℝ) ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1))) ≤
      1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1))) * (1 / 2) ^ j := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey2
  have hs4 : 1 / ((3 : ℝ) ^ (j + k + 1) * 4 ^ (3 ^ (j + k + 1))) ≤
      1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1))) * (1 / 2) ^ j := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey4
  unfold stonehamSumTerm
  exact (add_le_add hs2 hs4).trans_eq (by ring)

/-- At the left edge of a zero window, twice the scaled tail majorant is below one. -/
theorem stonehamSumTerm_scaled_lt_half (k p : ℕ) (hp : p ≤ 3 ^ (k + 1)) :
    2 * ((2 : ℝ) ^ p * stonehamSumTerm k) < 1 := by
  have hpow : (2 : ℝ) ^ p ≤ 2 ^ (3 ^ (k + 1)) :=
    pow_le_pow_right₀ one_le_two hp
  have hthreeN : 3 ≤ 3 ^ (k + 1) := by
    calc
      3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hthree : (3 : ℝ) ≤ 3 ^ (k + 1) := by exact_mod_cast hthreeN
  have height : (8 : ℝ) ≤ 2 ^ (3 ^ (k + 1)) := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 ^ (k + 1)) := pow_le_pow_right₀ one_le_two hthreeN
  have hfirst : (2 : ℝ) ^ p *
      (1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1)))) ≤ 1 / 3 := by
    calc
      (2 : ℝ) ^ p * (1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1)))) ≤
          2 ^ (3 ^ (k + 1)) * (1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1)))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 / (3 : ℝ) ^ (k + 1) := by field_simp
      _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hthree
  have hfourpow : (4 : ℝ) ^ (3 ^ (k + 1)) =
      2 ^ (3 ^ (k + 1)) * 2 ^ (3 ^ (k + 1)) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hsecond : (2 : ℝ) ^ p *
      (1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1)))) ≤ 1 / 24 := by
    calc
      (2 : ℝ) ^ p * (1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1)))) ≤
          2 ^ (3 ^ (k + 1)) * (1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1)))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 / ((3 : ℝ) ^ (k + 1) * 2 ^ (3 ^ (k + 1))) := by
        rw [hfourpow]
        field_simp
      _ ≤ 1 / 24 := by
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith
  unfold stonehamSumTerm
  nlinarith [hfirst, hsecond]

theorem stonehamSumTerm_le_geom (j : ℕ) :
    stonehamSumTerm j ≤ (1 / 12 : ℝ) * (1 / 2) ^ j := by
  have hs : sterm j ≤ (1 / 24 : ℝ) * (1 / 2) ^ j := by
    unfold sterm
    rw [div_pow, one_pow, mul_one_div, div_div]
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    have h3 : (3 : ℝ) ≤ 3 ^ (j + 1) :=
      le_self_pow₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (j + 3) ≤ 2 ^ (3 ^ (j + 1)) := by
      apply pow_le_pow_right₀ one_le_two
      calc
        j + 3 ≤ 3 * (j + 1) := by omega
        _ ≤ 3 ^ (j + 1) := by
          calc
            3 * (j + 1) ≤ 3 * 3 ^ j := by
              have : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
              omega
            _ = 3 ^ (j + 1) := (pow_succ' 3 j).symm
    calc
      (24 : ℝ) * 2 ^ j = 3 * 2 ^ (j + 3) := by ring
      _ ≤ 3 ^ (j + 1) * 2 ^ (3 ^ (j + 1)) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
  have hf : 1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1))) ≤ sterm j := by
    unfold sterm
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    gcongr
    norm_num
  unfold stonehamSumTerm
  unfold sterm at hs hf
  nlinarith [hs, hf]

/-- The sum lies in `[0,1)`, so `digitOf` reads it without an integer-part correction. -/
theorem stoneham_sum_mem_Ico :
    stonehamAlpha 2 3 + stonehamAlpha 4 3 ∈ Set.Ico (0 : ℝ) 1 := by
  rw [stoneham_sum_eq_tsum]
  constructor
  · exact tsum_nonneg fun j => by unfold stonehamSumTerm; positivity
  · have hgeom : Summable fun j : ℕ => (1 / 12 : ℝ) * (1 / 2) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := summable_stonehamSumTerm.tsum_le_tsum stonehamSumTerm_le_geom hgeom
    rw [tsum_mul_left, tsum_geometric_two] at hle
    linarith

/-- `α₂,₃ + α₄,₃ = Σ_k ((2^(3^k)+1)/3^k)·4^(−3^k)` is a sum of disjoint integer blocks
(`3^(k+1) ∣ 2^(3^k) + 1`, lifting the exponent), so its binary digits vanish on
`[2·3^k, 3^(k+1))` (0-indexed `digitOf`). -/
theorem digitOf_stoneham_sum_eq_zero (k i : ℕ) (h₁ : 2 * 3 ^ k ≤ i) (h₂ : i < 3 ^ (k + 1)) :
    digitOf 2 (Int.fract (stonehamAlpha 2 3 + stonehamAlpha 4 3)) i = 0 := by
  set x : ℝ := stonehamAlpha 2 3 + stonehamAlpha 4 3 with hx
  set p : ℕ := i + 1 with hp
  have hp_le : p ≤ 3 ^ (k + 1) := by omega
  have hxfrac : Int.fract x = x := Int.fract_eq_self.mpr stoneham_sum_mem_Ico
  set g : ℕ → ℝ := fun j => (2 : ℝ) ^ p * stonehamSumTerm j with hg
  have hgsum : Summable g := summable_stonehamSumTerm.mul_left _
  have hmul : x * (2 : ℝ) ^ p = ∑' j, g j := by
    rw [hx, stoneham_sum_eq_tsum, tsum_mul_left, mul_comm]
  have hshift : Summable fun j => g (j + k) := (summable_nat_add_iff k).2 hgsum
  have hsplit : ∑' j, g j = (∑ j ∈ Finset.range k, g j) + ∑' j, g (j + k) :=
    (hgsum.sum_add_tsum_nat_add k).symm
  set T : ℝ := ∑' j, g (j + k) with hT
  set A : ℕ := ∑ j ∈ Finset.range k,
    2 ^ (p - 2 * 3 ^ (j + 1)) *
      ((2 ^ (3 ^ (j + 1)) + 1) / 3 ^ (j + 1)) with hA
  have hHead : (∑ j ∈ Finset.range k, g j) = (A : ℝ) := by
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hjpow : 3 ^ (j + 1) ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hg]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      stonehamSumTerm_scaled_eq_block j p (by omega)
  have hAeven : 2 ∣ A := by
    rw [hA]
    refine Finset.dvd_sum fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hjpow : 3 ^ (j + 1) ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hexp : 0 < p - 2 * 3 ^ (j + 1) := by omega
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hexp.ne') _
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact tsum_nonneg fun j => by
      simp only [hg]
      exact mul_nonneg (pow_nonneg (by norm_num) _) (by unfold stonehamSumTerm; positivity)
  have hTlt : T < 1 := by
    have hterm : ∀ j, g (j + k) ≤ g k * (1 / 2 : ℝ) ^ j := by
      intro j
      simp only [hg]
      calc
        (2 : ℝ) ^ p * stonehamSumTerm (j + k) ≤
            2 ^ p * (stonehamSumTerm k * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (stonehamSumTerm_shift_le k j) (by positivity)
        _ = (2 ^ p * stonehamSumTerm k) * (1 / 2 : ℝ) ^ j := by ring
    have hgeom : Summable fun j : ℕ => g k * (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift.tsum_le_tsum hterm hgeom
    rw [hT]
    refine lt_of_le_of_lt hle ?_
    rw [tsum_mul_left, tsum_geometric_two, hg]
    simpa [mul_comm] using stonehamSumTerm_scaled_lt_half k p hp_le
  have hval : x * (2 : ℝ) ^ p = (A : ℝ) + T := by
    rw [hmul, hsplit, hHead]
  have hfl : ⌊x * (2 : ℝ) ^ p⌋ = (A : ℤ) := by
    rw [hval, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold digitOf
  rw [hxfrac, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← hp, hfl,
    Int.toNat_natCast, Nat.mod_eq_zero_of_dvd hAeven]

/-- Hence the zero frequency is pushed toward `2/3` at `n = 3^(k+1)`. -/
theorem not_isSimplyNormal_stoneham_sum :
    ¬ IsSimplyNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 4 3) := by
  classical
  intro hnormal
  let x := stonehamAlpha 2 3 + stonehamAlpha 4 3
  let s : ℕ → ℕ := digitOf 2 (Int.fract x)
  let Z : ℕ → ℕ := fun n => ((Finset.range n).filter fun i => s i = 0).card
  have hcount (n : ℕ) : countOccurrences [0] ((List.range n).map s) = Z n :=
    Failures.countOccurrences_zero_eq_card s n
  have hlim : Tendsto (fun n => (Z n : ℝ) / n) atTop (nhds (1 / 2 : ℝ)) := by
    simpa [x, s, hcount, Z] using hnormal 0 (by norm_num)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨K, hK⟩ := hlim (1 / 100) (by norm_num)
  let k := max K 1
  let n₁ := 2 * 3 ^ k
  let n₂ := 3 ^ (k + 1)
  have hkK : K ≤ k := le_max_left _ _
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hkpow : k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
  have hn₁K : K ≤ n₁ := by dsimp [n₁]; omega
  have hn₂K : K ≤ n₂ := by
    dsimp [n₂]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hn₁₂ : n₁ ≤ n₂ := by
    dsimp [n₁, n₂]
    rw [pow_succ]
    omega
  have hforced : ∀ i, i ∈ Finset.Ico n₁ n₂ → s i = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact digitOf_stoneham_sum_eq_zero k i hi.1 hi.2
  have hstep : Z n₁ + (n₂ - n₁) ≤ Z n₂ := by
    have hdisj : Disjoint ((Finset.range n₁).filter fun i => s i = 0)
        (Finset.Ico n₁ n₂) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_Ico] at hb
      omega
    have hsub : ((Finset.range n₁).filter fun i => s i = 0) ∪ Finset.Ico n₁ n₂
        ⊆ (Finset.range n₂).filter fun i => s i = 0 := by
      intro a ha
      rw [Finset.mem_union] at ha
      rw [Finset.mem_filter, Finset.mem_range]
      rcases ha with ha | ha
      · rw [Finset.mem_filter, Finset.mem_range] at ha
        exact ⟨ha.1.trans_le hn₁₂, ha.2⟩
      · rw [Finset.mem_Ico] at ha
        exact ⟨ha.2, hforced a (Finset.mem_Ico.mpr ha)⟩
    have hc := Finset.card_le_card hsub
    simpa [Z, Finset.card_union_of_disjoint hdisj, Nat.card_Ico] using hc
  have h₁ := hK n₁ hn₁K
  have h₂ := hK n₂ hn₂K
  rw [Real.dist_eq, abs_lt] at h₁ h₂
  have hn₁pos : (0 : ℝ) < n₁ := by positivity
  have hn₂pos : (0 : ℝ) < n₂ := by positivity
  have e₁ : (1 / 2 - 1 / 100) * (n₁ : ℝ) < Z n₁ := by
    have hx : (1 / 2 - 1 / 100 : ℝ) < (Z n₁ : ℝ) / n₁ := by linarith [h₁.1]
    rwa [lt_div_iff₀ hn₁pos] at hx
  have e₂ : (Z n₂ : ℝ) < (1 / 2 + 1 / 100) * n₂ := by
    have hx : (Z n₂ : ℝ) / n₂ < (1 / 2 + 1 / 100 : ℝ) := by linarith [h₂.2]
    rwa [div_lt_iff₀ hn₂pos] at hx
  have e₃ : (Z n₁ : ℝ) + ((n₂ : ℝ) - n₁) ≤ Z n₂ := by
    have hc := (Nat.cast_le (α := ℝ)).2 hstep
    push_cast [Nat.cast_sub hn₁₂] at hc
    linarith
  have hn₁ : (n₁ : ℝ) = 2 * (3 : ℝ) ^ k := by simp [n₁]
  have hn₂ : (n₂ : ℝ) = 3 * (3 : ℝ) ^ k := by
    push_cast
    simp [n₂, pow_succ]
    ring
  have hkR : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [hn₁] at e₁ e₃
  rw [hn₂] at e₂ e₃
  nlinarith

end NormalNumbers
