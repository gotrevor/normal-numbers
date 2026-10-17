/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.StonehamSumsNormal

/-!
# Boundary witnesses for Stoneham combinations

This file formalizes the elementary integer-block witnesses at the boundary of the
Bailey--Borwein classification of rational Stoneham combinations.
-/

namespace NormalNumbers

open ReciprocalNormal
open Filter Topology

/-- Fermat followed by the elementary prime-power lift: the numerator of the
`j`-th block in the Bailey--Borwein L1 witness is divisible by `p^j`. -/
theorem prime_pow_dvd_stoneham_boundary_block (b p j : ℕ) (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    p ^ j ∣ b ^ ((p - 1) * p ^ j) - 1 := by
  have hcop : b.Coprime p := ((hp.coprime_iff_not_dvd).2 hpb).symm
  have hfermat := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    simp at hpb
  have hbase : 1 ≤ b ^ (p - 1) := Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.2 hb0)
  have hdvd : p ∣ b ^ (p - 1) - 1 := hfermat.symm.dvd'
  obtain ⟨a, ha⟩ := hdvd
  have hshape : b ^ (p - 1) = 1 + p * a := by omega
  have hlift := pow_pow_modEq_one p j a
  rw [← hshape] at hlift
  rw [← pow_mul] at hlift
  exact hlift.symm.dvd'

/-- The cyclotomic coefficient in the Bailey--Borwein L2 witness is integral.
The elementary proof lifts `729 ≡ 1` to a power of seven, selects the
`27^(7^n) + 1` factor modulo seven, and then selects `Φ₆(3^(7^n))`. -/
theorem seven_pow_dvd_stoneham_triple_block (n : ℕ) :
    7 ^ n ∣ 3 ^ (2 * 7 ^ n) - 3 ^ (7 ^ n) + 1 := by
  have h7prime : Nat.Prime 7 := by norm_num
  have hlift := pow_pow_modEq_one 7 n 104
  have hlift' : 7 ^ n ∣ 729 ^ (7 ^ n) - 1 := hlift.symm.dvd'
  set x : ℕ := 27 ^ (7 ^ n) with hx
  have hx_sq : x ^ 2 = 729 ^ (7 ^ n) := by
    calc
      x ^ 2 = 27 ^ (7 ^ n * 2) := by rw [hx, pow_mul]
      _ = 27 ^ (2 * 7 ^ n) := by congr 1 <;> omega
      _ = (27 ^ 2) ^ (7 ^ n) := by rw [pow_mul]
      _ = 729 ^ (7 ^ n) := by norm_num
  have hx_one : 1 ≤ x := Nat.one_le_pow _ _ (by norm_num)
  have hprod : 7 ^ n ∣ (x - 1) * (x + 1) := by
    rw [mul_comm, ← Nat.sq_sub_sq, one_pow, hx_sq]
    exact hlift'
  have hodd : Odd (7 ^ n) := (show Odd 7 by norm_num).pow
  obtain ⟨t, ht⟩ := hodd
  have hxmod : x ≡ 6 [MOD 7] := by
    rw [hx, ht, pow_add, pow_mul]
    have hbase : 27 ^ 2 ≡ 1 [MOD 7] := by norm_num
    simpa using (hbase.pow t).mul (show 27 ≡ 6 [MOD 7] by norm_num)
  have hxnot : ¬ 7 ∣ x - 1 := by
    intro h
    have hmod : 1 ≡ x [MOD 7] := Nat.modEq_of_dvd' hx_one h
    have hbad : 1 ≡ 6 [MOD 7] := hmod.trans hxmod
    norm_num at hbad
  have hxplus : 7 ^ n ∣ x + 1 :=
    h7prime.prime.pow_dvd_of_dvd_mul_left n hxnot hprod
  set a : ℕ := 3 ^ (7 ^ n) with ha
  have hcube : a ^ 3 + 1 = x + 1 := by
    calc
      a ^ 3 + 1 = 3 ^ (7 ^ n * 3) + 1 := by rw [ha, pow_mul]
      _ = 3 ^ (3 * 7 ^ n) + 1 := by congr 2 <;> omega
      _ = (3 ^ 3) ^ (7 ^ n) + 1 := by rw [pow_mul]
      _ = x + 1 := by rw [hx]; norm_num
  have hfactor : a ^ 3 + 1 = (a + 1) * (a ^ 2 - a + 1) := by
    have ha1 : 1 ≤ a := Nat.one_le_pow _ _ (by norm_num)
    have haa : a ≤ a ^ 2 := by nlinarith
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub haa]
    ring
  have hseven_mod_six : 7 ^ n ≡ 1 [MOD 6] := by
    simpa using (show 7 ≡ 1 [MOD 6] by norm_num).pow n
  have hdvd6 : 6 ∣ 7 ^ n - 1 := hseven_mod_six.symm.dvd'
  obtain ⟨u, hu⟩ := hdvd6
  have hexp : 7 ^ n = 6 * u + 1 := by omega
  have hamod : a ≡ 3 [MOD 7] := by
    rw [ha, hexp, pow_add, pow_mul]
    have hbase : 3 ^ 6 ≡ 1 [MOD 7] := by norm_num
    simpa using (hbase.pow u).mul (Nat.ModEq.refl 3)
  have hanot : ¬ 7 ∣ a + 1 := by
    intro h
    have hzero : a + 1 ≡ 0 [MOD 7] := Nat.modEq_zero_iff_dvd.mpr h
    have hfour : a + 1 ≡ 4 [MOD 7] := by simpa using hamod.add_right 1
    have hbad : 4 ≡ 0 [MOD 7] := hfour.symm.trans hzero
    norm_num at hbad
  have hphi : 7 ^ n ∣ a ^ 2 - a + 1 := by
    apply h7prime.prime.pow_dvd_of_dvd_mul_left n hanot
    rw [← hfactor, hcube]
    exact hxplus
  simpa [a, pow_two, show 2 * 7 ^ n = 7 ^ n + 7 ^ n by omega, pow_add] using hphi

/-! ### The ternary cyclotomic triple (L2) -/

/-- The `k`-th term of `α₃,₇ - α₉,₇ + α₂₇,₇`. -/
noncomputable def stonehamTripleTerm (k : ℕ) : ℝ :=
  1 / ((7 : ℝ) ^ (k + 1) * 3 ^ (7 ^ (k + 1))) -
    1 / ((7 : ℝ) ^ (k + 1) * 9 ^ (7 ^ (k + 1))) +
      1 / ((7 : ℝ) ^ (k + 1) * 27 ^ (7 ^ (k + 1)))

/-- The integral cyclotomic coefficient of the `k`-th ternary block. -/
def stonehamTripleBlock (k : ℕ) : ℕ :=
  (3 ^ (2 * 7 ^ (k + 1)) - 3 ^ (7 ^ (k + 1)) + 1) / 7 ^ (k + 1)

/-- The leading positive summand used to majorize the L2 tail. -/
noncomputable def stonehamTripleMajorant (k : ℕ) : ℝ :=
  1 / ((7 : ℝ) ^ (k + 1) * 3 ^ (7 ^ (k + 1)))

/-- Each triple term is its integral block ending at ternary position
`3 * 7^(k+1)`. -/
theorem stonehamTripleTerm_scaled_eq_block (k : ℕ) :
    (3 : ℝ) ^ (3 * 7 ^ (k + 1)) * stonehamTripleTerm k =
      stonehamTripleBlock k := by
  have hdvd := seven_pow_dvd_stoneham_triple_block (k + 1)
  set q : ℕ := stonehamTripleBlock k with hq
  have hqN : 7 ^ (k + 1) * q =
      3 ^ (2 * 7 ^ (k + 1)) - 3 ^ (7 ^ (k + 1)) + 1 := by
    rw [hq, stonehamTripleBlock]
    exact Nat.mul_div_cancel' hdvd
  have hleN : 3 ^ (7 ^ (k + 1)) ≤ 3 ^ (2 * 7 ^ (k + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqR : (7 : ℝ) ^ (k + 1) * q =
      3 ^ (2 * 7 ^ (k + 1)) - 3 ^ (7 ^ (k + 1)) + 1 := by
    push_cast [Nat.cast_sub hleN]
    exact_mod_cast hqN
  have h9 : (9 : ℝ) ^ (7 ^ (k + 1)) = 3 ^ (2 * 7 ^ (k + 1)) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, pow_mul]
  have h27 : (27 : ℝ) ^ (7 ^ (k + 1)) = 3 ^ (3 * 7 ^ (k + 1)) := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, pow_mul]
  have h2 : (3 : ℝ) ^ (2 * 7 ^ (k + 1)) =
      (3 ^ (7 ^ (k + 1))) ^ 2 := by
    rw [mul_comm, pow_mul]
  have h3 : (3 : ℝ) ^ (3 * 7 ^ (k + 1)) =
      (3 ^ (7 ^ (k + 1))) ^ 3 := by
    rw [mul_comm, pow_mul]
  rw [stonehamTripleTerm]
  rw [h9, h27, h2, h3]
  rw [h2] at hqR
  set z : ℝ := 3 ^ (7 ^ (k + 1)) with hz
  change z ^ 3 *
    (1 / ((7 : ℝ) ^ (k + 1) * z) -
      1 / ((7 : ℝ) ^ (k + 1) * z ^ 2) +
        1 / ((7 : ℝ) ^ (k + 1) * z ^ 3)) = q
  change (7 : ℝ) ^ (k + 1) * q = z ^ 2 - z + 1 at hqR
  have hz0 : z ≠ 0 := by positivity
  field_simp [hz0]
  nlinarith [hqR]

/-- Beyond its right endpoint, an L2 term is an integer block followed by
ternary zeros. -/
theorem stonehamTripleTerm_scaled_eq_shifted_block (k q : ℕ)
    (hq : 3 * 7 ^ (k + 1) ≤ q) :
    (3 : ℝ) ^ q * stonehamTripleTerm k =
      (3 ^ (q - 3 * 7 ^ (k + 1)) * stonehamTripleBlock k : ℕ) := by
  have hpow : (3 : ℝ) ^ (q - 3 * 7 ^ (k + 1)) * 3 ^ (3 * 7 ^ (k + 1)) = 3 ^ q := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (3 : ℝ) ^ q * stonehamTripleTerm k =
        (3 ^ (q - 3 * 7 ^ (k + 1)) * 3 ^ (3 * 7 ^ (k + 1))) *
          stonehamTripleTerm k := by rw [hpow]
    _ = 3 ^ (q - 3 * 7 ^ (k + 1)) *
          (3 ^ (3 * 7 ^ (k + 1)) * stonehamTripleTerm k) := by ring
    _ = 3 ^ (q - 3 * 7 ^ (k + 1)) * stonehamTripleBlock k := by
      rw [stonehamTripleTerm_scaled_eq_block]
    _ = (3 ^ (q - 3 * 7 ^ (k + 1)) * stonehamTripleBlock k : ℕ) := by
      push_cast
      rfl

/-- L2's cyclotomic terms are positive. -/
theorem stonehamTripleTerm_nonneg (k : ℕ) : 0 ≤ stonehamTripleTerm k := by
  unfold stonehamTripleTerm
  have h9 : (3 : ℝ) ^ (7 ^ (k + 1)) ≤ 9 ^ (7 ^ (k + 1)) := by gcongr <;> norm_num
  have h27 : (9 : ℝ) ^ (7 ^ (k + 1)) ≤ 27 ^ (7 ^ (k + 1)) := by gcongr <;> norm_num
  have hfirst : 1 / ((7 : ℝ) ^ (k + 1) * 9 ^ (7 ^ (k + 1))) ≤
      1 / ((7 : ℝ) ^ (k + 1) * 3 ^ (7 ^ (k + 1))) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  positivity

/-- The leading summand majorizes the positive triple term. -/
theorem stonehamTripleTerm_le_majorant (k : ℕ) :
    stonehamTripleTerm k ≤ stonehamTripleMajorant k := by
  unfold stonehamTripleTerm stonehamTripleMajorant
  have h : 1 / ((7 : ℝ) ^ (k + 1) * 27 ^ (7 ^ (k + 1))) ≤
      1 / ((7 : ℝ) ^ (k + 1) * 9 ^ (7 ^ (k + 1))) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr <;> norm_num
  linarith

/-- Later L2 majorants decrease at least geometrically. -/
theorem stonehamTripleMajorant_shift_le (k j : ℕ) :
    stonehamTripleMajorant (j + k) ≤
      stonehamTripleMajorant k * (1 / 2 : ℝ) ^ j := by
  have hcoeff : (7 : ℝ) ^ (k + 1) * 2 ^ j ≤ 7 ^ (j + k + 1) := by
    calc
      (7 : ℝ) ^ (k + 1) * 2 ^ j ≤ 7 ^ (k + 1) * 7 ^ j :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
            (by norm_num : (2 : ℝ) ≤ 7) j)
          (show 0 ≤ (7 : ℝ) ^ (k + 1) by positivity)
      _ = 7 ^ ((k + 1) + j) := (pow_add _ _ _).symm
      _ = 7 ^ (j + k + 1) := by congr 1 <;> omega
  have hexp : 7 ^ (k + 1) ≤ 7 ^ (j + k + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbase : (3 : ℝ) ^ (7 ^ (k + 1)) ≤ 3 ^ (7 ^ (j + k + 1)) := by
    exact pow_le_pow_right₀ (by norm_num) hexp
  have hden : (7 : ℝ) ^ (k + 1) * 3 ^ (7 ^ (k + 1)) * 2 ^ j ≤
      7 ^ (j + k + 1) * 3 ^ (7 ^ (j + k + 1)) := by
    calc
      (7 : ℝ) ^ (k + 1) * 3 ^ (7 ^ (k + 1)) * 2 ^ j =
          (7 ^ (k + 1) * 2 ^ j) * 3 ^ (7 ^ (k + 1)) := by ring
      _ ≤ 7 ^ (j + k + 1) * 3 ^ (7 ^ (j + k + 1)) :=
        mul_le_mul hcoeff hbase (by positivity) (by positivity)
  unfold stonehamTripleMajorant
  rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  exact div_le_div_of_nonneg_left one_pos.le (by positivity) hden

/-- Twice a scaled L2 majorant is below one whenever the scale has not
passed the block's left endpoint. -/
theorem stonehamTripleMajorant_scaled_lt_half (k q : ℕ)
    (hq : q ≤ 7 ^ (k + 1)) :
    2 * ((3 : ℝ) ^ q * stonehamTripleMajorant k) < 1 := by
  have hpow : (3 : ℝ) ^ q ≤ 3 ^ (7 ^ (k + 1)) :=
    pow_le_pow_right₀ (by norm_num) hq
  have hscaled : (3 : ℝ) ^ q * stonehamTripleMajorant k ≤
      1 / (7 : ℝ) ^ (k + 1) := by
    calc
      (3 : ℝ) ^ q * stonehamTripleMajorant k ≤
          3 ^ (7 ^ (k + 1)) * stonehamTripleMajorant k :=
        mul_le_mul_of_nonneg_right hpow (by unfold stonehamTripleMajorant; positivity)
      _ = 1 / (7 : ℝ) ^ (k + 1) := by
        unfold stonehamTripleMajorant
        field_simp
  have hseven : (7 : ℝ) ≤ 7 ^ (k + 1) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 1 ≤ k + 1)
  have hrecip : 2 * (1 / (7 : ℝ) ^ (k + 1)) ≤ 2 / 7 := by
    calc
      2 * (1 / (7 : ℝ) ^ (k + 1)) ≤ 2 * (1 / 7) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by norm_num) hseven) (by norm_num)
      _ = 2 / 7 := by ring
  nlinarith

/-- The L2 triple-term series is summable. -/
theorem summable_stonehamTripleTerm : Summable stonehamTripleTerm := by
  have h3 := StonehamSumsNormal.summable_stonehamAlpha_term 3 7 (by norm_num) (by norm_num)
  have h9 := StonehamSumsNormal.summable_stonehamAlpha_term 9 7 (by norm_num) (by norm_num)
  have h27 := StonehamSumsNormal.summable_stonehamAlpha_term 27 7 (by norm_num) (by norm_num)
  exact (h3.sub h9).add h27

/-- The Stoneham triple is exactly the sum of its cyclotomic blocks. -/
theorem stoneham_three_seven_triple_eq_tsum :
    stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7 =
      ∑' k, stonehamTripleTerm k := by
  have h3 := StonehamSumsNormal.summable_stonehamAlpha_term 3 7 (by norm_num) (by norm_num)
  have h9 := StonehamSumsNormal.summable_stonehamAlpha_term 9 7 (by norm_num) (by norm_num)
  have h27 := StonehamSumsNormal.summable_stonehamAlpha_term 27 7 (by norm_num) (by norm_num)
  unfold stonehamAlpha stonehamTripleTerm
  rw [← h3.tsum_sub h9, ← (h3.sub h9).tsum_add h27]
  apply tsum_congr
  intro k
  norm_num

/-- A geometric majorant for all L2 blocks. -/
theorem stonehamTripleMajorant_le_geom (k : ℕ) :
    stonehamTripleMajorant k ≤ (1 / 21 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hzero : stonehamTripleMajorant 0 ≤ (1 / 21 : ℝ) := by
    rw [stonehamTripleMajorant]
    norm_num
  have hshift := stonehamTripleMajorant_shift_le 0 k
  simpa only [Nat.add_zero] using
    hshift.trans (mul_le_mul_of_nonneg_right hzero (by positivity))

/-- The L2 triple lies in `[0,1)`, so its standard ternary digits can be
read without correcting the integer part. -/
theorem stoneham_three_seven_triple_mem_Ico :
    stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7 ∈ Set.Ico (0 : ℝ) 1 := by
  rw [stoneham_three_seven_triple_eq_tsum]
  constructor
  · exact tsum_nonneg stonehamTripleTerm_nonneg
  · have hgeom : Summable fun k : ℕ => (1 / 21 : ℝ) * (1 / 2 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle : ∀ k, stonehamTripleTerm k ≤ (1 / 21 : ℝ) * (1 / 2 : ℝ) ^ k :=
      fun k => (stonehamTripleTerm_le_majorant k).trans (stonehamTripleMajorant_le_geom k)
    have hsum := summable_stonehamTripleTerm.tsum_le_tsum hle hgeom
    rw [tsum_mul_left, tsum_geometric_two] at hsum
    linarith

/-- The ternary digits between one L2 block's right endpoint and the next
block's left endpoint vanish.  Indices are 0-based. -/
theorem digitOf_stoneham_three_seven_triple_eq_zero (k i : ℕ)
    (h₁ : 3 * 7 ^ (k + 1) ≤ i) (h₂ : i < 7 ^ (k + 2)) :
    digitOf 3
      (Int.fract (stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7)) i = 0 := by
  set x : ℝ := stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7 with hx
  set q : ℕ := i + 1 with hq
  have hq_le : q ≤ 7 ^ (k + 2) := by omega
  have hxfrac : Int.fract x = x :=
    Int.fract_eq_self.mpr stoneham_three_seven_triple_mem_Ico
  set g : ℕ → ℝ := fun j => (3 : ℝ) ^ q * stonehamTripleTerm j with hg
  have hgsum : Summable g := summable_stonehamTripleTerm.mul_left _
  have hmul : x * (3 : ℝ) ^ q = ∑' j, g j := by
    rw [hx, stoneham_three_seven_triple_eq_tsum, tsum_mul_left, mul_comm]
  have hshift : Summable fun j => g (j + (k + 1)) :=
    (summable_nat_add_iff (k + 1)).2 hgsum
  have hsplit : ∑' j, g j =
      (∑ j ∈ Finset.range (k + 1), g j) + ∑' j, g (j + (k + 1)) :=
    (hgsum.sum_add_tsum_nat_add (k + 1)).symm
  set T : ℝ := ∑' j, g (j + (k + 1)) with hT
  set A : ℕ := ∑ j ∈ Finset.range (k + 1),
    3 ^ (q - 3 * 7 ^ (j + 1)) * stonehamTripleBlock j with hA
  have hHead : (∑ j ∈ Finset.range (k + 1), g j) = (A : ℝ) := by
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    have hjpow : 3 * 7 ^ (j + 1) ≤ 3 * 7 ^ (k + 1) := by
      exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hg]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      stonehamTripleTerm_scaled_eq_shifted_block j q
        (hjpow.trans (h₁.trans (by omega)))
  have hAthree : 3 ∣ A := by
    rw [hA]
    refine Finset.dvd_sum fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    have hjpow : 3 * 7 ^ (j + 1) ≤ 3 * 7 ^ (k + 1) := by
      exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hendpoint := hjpow.trans h₁
    have hexp : 0 < q - 3 * 7 ^ (j + 1) := by omega
    exact Dvd.dvd.mul_right (dvd_pow_self 3 hexp.ne') _
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact tsum_nonneg fun j =>
      mul_nonneg (pow_nonneg (by norm_num) _) (stonehamTripleTerm_nonneg _)
  have hTlt : T < 1 := by
    have hterm : ∀ j, g (j + (k + 1)) ≤
        ((3 : ℝ) ^ q * stonehamTripleMajorant (k + 1)) *
          (1 / 2 : ℝ) ^ j := by
      intro j
      rw [hg]
      calc
        (3 : ℝ) ^ q * stonehamTripleTerm (j + (k + 1)) ≤
            3 ^ q * stonehamTripleMajorant (j + (k + 1)) :=
          mul_le_mul_of_nonneg_left (stonehamTripleTerm_le_majorant _) (by positivity)
        _ ≤ 3 ^ q *
            (stonehamTripleMajorant (k + 1) * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left
            (stonehamTripleMajorant_shift_le (k + 1) j) (by positivity)
        _ = (3 ^ q * stonehamTripleMajorant (k + 1)) * (1 / 2 : ℝ) ^ j := by ring
    have hgeom : Summable fun j : ℕ =>
        ((3 : ℝ) ^ q * stonehamTripleMajorant (k + 1)) * (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift.tsum_le_tsum hterm hgeom
    rw [hT]
    refine lt_of_le_of_lt hle ?_
    rw [tsum_mul_left, tsum_geometric_two]
    simpa [mul_comm, show k + 1 + 1 = k + 2 by omega] using
      stonehamTripleMajorant_scaled_lt_half (k + 1) q hq_le
  have hval : x * (3 : ℝ) ^ q = (A : ℝ) + T := by
    rw [hmul, hsplit, hHead]
  have hfl : ⌊x * (3 : ℝ) ^ q⌋ = (A : ℤ) := by
    rw [hval, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold digitOf
  rw [hxfrac, show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num, ← hq, hfl,
    Int.toNat_natCast, Nat.mod_eq_zero_of_dvd hAthree]

/-- **Bailey--Borwein boundary witness L2.**  The cyclotomic triple has
arbitrarily long ternary zero windows and hence is not simply normal. -/
@[blueprint (title := "A ternary Stoneham triple need not be simply normal")]
theorem not_isSimplyNormal_three_seven_triple :
    ¬ IsSimplyNormal 3
      (stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7) := by
  classical
  intro hnormal
  let x := stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7
  let s : ℕ → ℕ := digitOf 3 (Int.fract x)
  let Z : ℕ → ℕ := fun n => ((Finset.range n).filter fun i => s i = 0).card
  have hcount (n : ℕ) : countOccurrences [0] ((List.range n).map s) = Z n :=
    Failures.countOccurrences_zero_eq_card s n
  have hlim : Tendsto (fun n => (Z n : ℝ) / n) atTop (nhds (1 / 3 : ℝ)) := by
    simpa [x, s, hcount, Z] using hnormal 0 (by norm_num)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨K, hK⟩ := hlim (1 / 12 : ℝ) (by norm_num)
  let k := max K 1
  let n₁ := 3 * 7 ^ (k + 1)
  let n₂ := 7 ^ (k + 2)
  have hkK : K ≤ k := le_max_left _ _
  have hkpow : k ≤ 7 ^ k := (Nat.lt_pow_self (by norm_num)).le
  have hn₁K : K ≤ n₁ := by
    dsimp [n₁]
    calc
      K ≤ k := hkK
      _ ≤ 7 ^ k := hkpow
      _ ≤ 7 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 3 * 7 ^ (k + 1) := by
        have := pow_pos (by norm_num : 0 < (7 : ℕ)) (k + 1)
        omega
  have hn₂K : K ≤ n₂ := by
    dsimp [n₂]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hn₁₂ : n₁ ≤ n₂ := by
    dsimp [n₁, n₂]
    have hp : 7 ^ (k + 2) = 7 ^ (k + 1) * 7 := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    rw [hp]
    have hpos := pow_pos (by norm_num : 0 < (7 : ℕ)) (k + 1)
    omega
  have hforced : ∀ i, i ∈ Finset.Ico n₁ n₂ → s i = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact digitOf_stoneham_three_seven_triple_eq_zero k i hi.1 hi.2
  have hstep : Z n₁ + (n₂ - n₁) ≤ Z n₂ := by
    have hdisj : Disjoint ((Finset.range n₁).filter fun i => s i = 0)
        (Finset.Ico n₁ n₂) := by
      rw [Finset.disjoint_left]
      intro a ha hab
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_Ico] at hab
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
  have hn₁pos : (0 : ℝ) < n₁ := by
    exact_mod_cast mul_pos (by norm_num : 0 < (3 : ℕ)) (pow_pos (by norm_num) (k + 1))
  have hn₂pos : (0 : ℝ) < n₂ := by
    exact_mod_cast pow_pos (by norm_num : 0 < (7 : ℕ)) (k + 2)
  have e₁ : (1 / 4 : ℝ) * n₁ < Z n₁ := by
    have hx : (1 / 3 : ℝ) - 1 / 12 < (Z n₁ : ℝ) / n₁ := by linarith [h₁.1]
    rw [show (1 / 3 : ℝ) - 1 / 12 = 1 / 4 by norm_num,
      lt_div_iff₀ hn₁pos] at hx
    exact hx
  have e₂ : (Z n₂ : ℝ) < (5 / 12 : ℝ) * n₂ := by
    have hx : (Z n₂ : ℝ) / n₂ < (1 / 3 : ℝ) + 1 / 12 := by linarith [h₂.2]
    rw [show (1 / 3 : ℝ) + 1 / 12 = 5 / 12 by norm_num,
      div_lt_iff₀ hn₂pos] at hx
    exact hx
  have e₃ : (Z n₁ : ℝ) + ((n₂ : ℝ) - n₁) ≤ Z n₂ := by
    have hc := (Nat.cast_le (α := ℝ)).2 hstep
    push_cast [Nat.cast_sub hn₁₂] at hc
    linarith
  have hratio : (3 : ℝ) * n₂ = 7 * n₁ := by
    dsimp [n₁, n₂]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    push_cast
    ring
  nlinarith

/-! ### The exact joint-normality obligation behind L2

The zero-window theorem above proves that the three Stoneham constants are not jointly
normal.  To refute the stronger claim that pairwise joint normality implies joint normality,
one must additionally prove that each of their three pairs is jointly normal.  The
Bailey--Borwein research sketch asserts this via its same-prime criterion, but the criterion
has not yet been formalized.  The following definitions expose that missing premise instead
of allowing the non-joint half alone to masquerade as the full counterexample. -/

/-- A finite family is rationally jointly normal when every nonzero rational linear
combination of its coordinates is normal.  This is the Weyl-character formulation used by
the Bailey--Borwein joint-normality criterion. -/
def IsRationallyJointNormal (b : ℕ) {r : ℕ} (x : Fin r → ℝ) : Prop :=
  ∀ q : Fin r → ℚ, q ≠ 0 → IsNormal b (∑ i, (q i : ℝ) * x i)

/-- Pairwise rational joint normality asks for the corresponding property on every two
distinct coordinates. -/
def IsPairwiseRationallyJointNormal (b : ℕ) {r : ℕ} (x : Fin r → ℝ) : Prop :=
  Pairwise fun i j => ∀ a c : ℚ, a ≠ 0 ∨ c ≠ 0 →
    IsNormal b ((a : ℝ) * x i + (c : ℝ) * x j)

/-- The three Stoneham constants used by the L2 cyclotomic cancellation. -/
noncomputable def stonehamThreeSevenFamily : Fin 3 → ℝ :=
  ![stonehamAlpha 3 7, stonehamAlpha 9 7, stonehamAlpha 27 7]

/-- **Open L2 premise (85%).**  Each pair in the ternary Stoneham triple is rationally
jointly normal.  The unformalized same-prime criterion predicts this because
`ord_7(3) = 6` does not divide twice any difference among `1, 2, 3`.

This is the missing half of the proposed counterexample to "joint normality is pairwise". -/
def StonehamThreeSevenPairwiseNormal : Prop :=
  IsPairwiseRationallyJointNormal 3 stonehamThreeSevenFamily

/-! A first arithmetic prerequisite predicted by the same-prime criterion is elementary.  At
equal kick depth, the two newest terms differ by either `3^(7^n)` or its square.  The first
quantity is an approximate root of `X^2 - X + 1` modulo `7^n`; its square is therefore an
approximate root of `X^2 + X + 1`.  Taking the corresponding quadratic norm shows that deep
cancellation of a fixed coefficient pair forces the same power of seven to divide a fixed,
nonzero integer. -/

/-- Integer form of the cyclotomic divisibility already used by the L2 block. -/
theorem seven_pow_dvd_stoneham_phiSix_int (n : ℕ) :
    (7 : ℤ) ^ n ∣
      (3 : ℤ) ^ (2 * 7 ^ n) - (3 : ℤ) ^ (7 ^ n) + 1 := by
  have hle : 3 ^ (7 ^ n) ≤ 3 ^ (2 * 7 ^ n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast seven_pow_dvd_stoneham_triple_block n

/-- The resultant identity for an approximate sixth root of unity. -/
theorem dvd_pairNorm_of_phiSix (D a c z : ℤ)
    (hlin : D ∣ a + c * z) (hphi : D ∣ z ^ 2 - z + 1) :
    D ∣ a ^ 2 + a * c + c ^ 2 := by
  obtain ⟨u, hu⟩ := hlin
  obtain ⟨v, hv⟩ := hphi
  refine ⟨u * (a + c - c * z) + v * c ^ 2, ?_⟩
  calc
    a ^ 2 + a * c + c ^ 2 =
        (a + c * z) * (a + c - c * z) + c ^ 2 * (z ^ 2 - z + 1) := by ring
    _ = (D * u) * (a + c - c * z) + c ^ 2 * (D * v) := by rw [hu, hv]
    _ = D * (u * (a + c - c * z) + v * c ^ 2) := by ring

/-- Squaring an approximate sixth root gives an approximate third root. -/
theorem dvd_phiThree_sq_of_phiSix (D z : ℤ) (hphi : D ∣ z ^ 2 - z + 1) :
    D ∣ (z ^ 2) ^ 2 + z ^ 2 + 1 := by
  obtain ⟨v, hv⟩ := hphi
  refine ⟨v * (z ^ 2 + z + 1), ?_⟩
  calc
    (z ^ 2) ^ 2 + z ^ 2 + 1 =
        (z ^ 2 - z + 1) * (z ^ 2 + z + 1) := by ring
    _ = (D * v) * (z ^ 2 + z + 1) := by rw [hv]
    _ = D * (v * (z ^ 2 + z + 1)) := by ring

/-- The conjugate resultant identity for an approximate third root of unity. -/
theorem dvd_pairNorm_of_phiThree (D a c z : ℤ)
    (hlin : D ∣ a + c * z) (hphi : D ∣ z ^ 2 + z + 1) :
    D ∣ a ^ 2 - a * c + c ^ 2 := by
  obtain ⟨u, hu⟩ := hlin
  obtain ⟨v, hv⟩ := hphi
  refine ⟨u * (a - c - c * z) + v * c ^ 2, ?_⟩
  calc
    a ^ 2 - a * c + c ^ 2 =
        (a + c * z) * (a - c - c * z) + c ^ 2 * (z ^ 2 + z + 1) := by ring
    _ = (D * u) * (a - c - c * z) + c ^ 2 * (D * v) := by rw [hu, hv]
    _ = D * (u * (a - c - c * z) + v * c ^ 2) := by ring

/-- At exponent difference one, cancellation modulo `7^n` is bounded by the fixed positive
quadratic norm of the coefficient pair. -/
theorem seven_pow_dvd_stoneham_pairNorm_one (a c : ℤ) (n : ℕ)
    (hlin : (7 : ℤ) ^ n ∣ a + c * (3 : ℤ) ^ (7 ^ n)) :
    (7 : ℤ) ^ n ∣ a ^ 2 + a * c + c ^ 2 := by
  apply dvd_pairNorm_of_phiSix _ _ _ _ hlin
  simpa only [pow_two, ← pow_add, show 7 ^ n + 7 ^ n = 2 * 7 ^ n by omega] using
    seven_pow_dvd_stoneham_phiSix_int n

/-- At exponent difference two, the conjugate quadratic norm gives the same bounded-loss
conclusion. -/
theorem seven_pow_dvd_stoneham_pairNorm_two (a c : ℤ) (n : ℕ)
    (hlin : (7 : ℤ) ^ n ∣ a + c * ((3 : ℤ) ^ (7 ^ n)) ^ 2) :
    (7 : ℤ) ^ n ∣ a ^ 2 - a * c + c ^ 2 := by
  apply dvd_pairNorm_of_phiThree _ _ _ _ hlin
  exact dvd_phiThree_sq_of_phiSix _ _ (by
    simpa only [pow_two, ← pow_add, show 7 ^ n + 7 ^ n = 2 * 7 ^ n by omega] using
      seven_pow_dvd_stoneham_phiSix_int n)

/-- Neither quadratic norm can vanish for a nonzero integer coefficient pair. -/
theorem stoneham_pairNorms_ne_zero (a c : ℤ) (h : a ≠ 0 ∨ c ≠ 0) :
    a ^ 2 + a * c + c ^ 2 ≠ 0 ∧ a ^ 2 - a * c + c ^ 2 ≠ 0 := by
  constructor
  · intro hz
    rcases h with ha | hc
    · have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
      nlinarith [sq_nonneg (a + c), sq_nonneg c]
    · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
      nlinarith [sq_nonneg a, sq_nonneg (a + c)]
  · intro hz
    rcases h with ha | hc
    · have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
      nlinarith [sq_nonneg (a - c), sq_nonneg c]
    · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
      nlinarith [sq_nonneg a, sq_nonneg (a - c)]

/-- Quantitative bounded cancellation for a pair whose Stoneham exponents differ by one. -/
theorem stoneham_pair_cancellationDepth_le_one (a c : ℤ) (n : ℕ)
    (hac : a ≠ 0 ∨ c ≠ 0)
    (hlin : (7 : ℤ) ^ n ∣ a + c * (3 : ℤ) ^ (7 ^ n)) :
    n ≤ padicValInt 7 (a ^ 2 + a * c + c ^ 2) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd := seven_pow_dvd_stoneham_pairNorm_one a c n hlin
  exact ((padicValInt_dvd_iff n _).mp hdvd).resolve_left
    (stoneham_pairNorms_ne_zero a c hac).1

/-- Quantitative bounded cancellation for a pair whose Stoneham exponents differ by two. -/
theorem stoneham_pair_cancellationDepth_le_two (a c : ℤ) (n : ℕ)
    (hac : a ≠ 0 ∨ c ≠ 0)
    (hlin : (7 : ℤ) ^ n ∣ a + c * ((3 : ℤ) ^ (7 ^ n)) ^ 2) :
    n ≤ padicValInt 7 (a ^ 2 - a * c + c ^ 2) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd := seven_pow_dvd_stoneham_pairNorm_two a c n hlin
  exact ((padicValInt_dvd_iff n _).mp hdvd).resolve_left
    (stoneham_pairNorms_ne_zero a c hac).2

/-- Once the kick depth exceeds the coefficient norm's valuation, the actual 7-adic loss
in the equal-depth leading coefficient is bounded by that fixed valuation.  This is the
form needed when two same-prime Stoneham families enter their newest kicks together. -/
theorem stoneham_pair_leadingVal_le_one (a c : ℤ) (n : ℕ)
    (hac : a ≠ 0 ∨ c ≠ 0)
    (hn : padicValInt 7 (a ^ 2 + a * c + c ^ 2) < n) :
    padicValInt 7 (a + c * (3 : ℤ) ^ (7 ^ n)) ≤
      padicValInt 7 (a ^ 2 + a * c + c ^ 2) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let v := padicValInt 7 (a + c * (3 : ℤ) ^ (7 ^ n))
  have hvn : v < n := by
    by_contra h
    have hnv : n ≤ v := by omega
    have hd : (7 : ℤ) ^ n ∣ a + c * (3 : ℤ) ^ (7 ^ n) :=
      (padicValInt_dvd_iff n _).mpr (Or.inr hnv)
    have := stoneham_pair_cancellationDepth_le_one a c n hac hd
    omega
  have hlin : (7 : ℤ) ^ v ∣ a + c * (3 : ℤ) ^ (7 ^ n) := padicValInt_dvd _
  have hphiN : (7 : ℤ) ^ n ∣
      ((3 : ℤ) ^ (7 ^ n)) ^ 2 - (3 : ℤ) ^ (7 ^ n) + 1 := by
    simpa only [pow_two, ← pow_add, show 7 ^ n + 7 ^ n = 2 * 7 ^ n by omega] using
      seven_pow_dvd_stoneham_phiSix_int n
  have hphi : (7 : ℤ) ^ v ∣
      ((3 : ℤ) ^ (7 ^ n)) ^ 2 - (3 : ℤ) ^ (7 ^ n) + 1 := by
    exact (pow_dvd_pow (7 : ℤ) (by omega : v ≤ n)).trans hphiN
  have hnorm := dvd_pairNorm_of_phiSix ((7 : ℤ) ^ v) a c
    ((3 : ℤ) ^ (7 ^ n)) hlin hphi
  exact ((padicValInt_dvd_iff v _).mp hnorm).resolve_left
    (stoneham_pairNorms_ne_zero a c hac).1

/-- The analogous leading-coefficient valuation bound when the Stoneham exponents differ
by two. -/
theorem stoneham_pair_leadingVal_le_two (a c : ℤ) (n : ℕ)
    (hac : a ≠ 0 ∨ c ≠ 0)
    (hn : padicValInt 7 (a ^ 2 - a * c + c ^ 2) < n) :
    padicValInt 7 (a + c * ((3 : ℤ) ^ (7 ^ n)) ^ 2) ≤
      padicValInt 7 (a ^ 2 - a * c + c ^ 2) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let v := padicValInt 7 (a + c * ((3 : ℤ) ^ (7 ^ n)) ^ 2)
  have hvn : v < n := by
    by_contra h
    have hnv : n ≤ v := by omega
    have hd : (7 : ℤ) ^ n ∣ a + c * ((3 : ℤ) ^ (7 ^ n)) ^ 2 :=
      (padicValInt_dvd_iff n _).mpr (Or.inr hnv)
    have := stoneham_pair_cancellationDepth_le_two a c n hac hd
    omega
  have hlin : (7 : ℤ) ^ v ∣ a + c * ((3 : ℤ) ^ (7 ^ n)) ^ 2 :=
    padicValInt_dvd _
  have hphiSix : (7 : ℤ) ^ n ∣
      ((3 : ℤ) ^ (7 ^ n)) ^ 2 - (3 : ℤ) ^ (7 ^ n) + 1 := by
    simpa only [pow_two, ← pow_add, show 7 ^ n + 7 ^ n = 2 * 7 ^ n by omega] using
      seven_pow_dvd_stoneham_phiSix_int n
  have hphiN := dvd_phiThree_sq_of_phiSix ((7 : ℤ) ^ n)
    ((3 : ℤ) ^ (7 ^ n)) hphiSix
  have hphi : (7 : ℤ) ^ v ∣
      (((3 : ℤ) ^ (7 ^ n)) ^ 2) ^ 2 + ((3 : ℤ) ^ (7 ^ n)) ^ 2 + 1 := by
    exact (pow_dvd_pow (7 : ℤ) (by omega : v ≤ n)).trans hphiN
  have hnorm := dvd_pairNorm_of_phiThree ((7 : ℤ) ^ v) a c
    (((3 : ℤ) ^ (7 ^ n)) ^ 2) hlin hphi
  exact ((padicValInt_dvd_iff v _).mp hnorm).resolve_left
    (stoneham_pairNorms_ne_zero a c hac).2

/-- The L2 zero windows prove the *non-joint* half of the proposed pairwise counterexample,
with the exact rational-joint formulation made explicit. -/
@[blueprint (title := "The ternary Stoneham triple is not rationally jointly normal")]
theorem not_isRationallyJointNormal_stonehamThreeSeven :
    ¬ IsRationallyJointNormal 3 stonehamThreeSevenFamily := by
  intro hjoint
  let q : Fin 3 → ℚ := ![1, -1, 1]
  have hq : q ≠ 0 := by
    intro hzero
    have hzero0 := congrFun hzero (0 : Fin 3)
    norm_num [q] at hzero0
  have hnormal := hjoint q hq
  apply not_isSimplyNormal_three_seven_triple
  apply ReciprocalNormal.isSimplyNormal_of_isNormal
  simp only [stonehamThreeSevenFamily, q, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero] at hnormal
  norm_num at hnormal
  convert hnormal using 1 <;> ring

/-- Once the open pairwise premise is supplied, L2 is the claimed counterexample.  Keeping
the premise explicit prevents the Maze tier from overstating what the kernel currently
knows. -/
theorem stonehamThreeSeven_pairwise_not_joint
    (hpair : StonehamThreeSevenPairwiseNormal) :
    IsPairwiseRationallyJointNormal 3 stonehamThreeSevenFamily ∧
      ¬ IsRationallyJointNormal 3 stonehamThreeSevenFamily :=
  ⟨hpair, not_isRationallyJointNormal_stonehamThreeSeven⟩

/-- The positive paired summand in the L1 boundary witness.  It combines the
`(2k+1)`-st and `(2k+2)`-nd `p`-terms with the `k`-th `p²`-term. -/
noncomputable def stonehamBoundaryTerm (b p k : ℕ) : ℝ :=
  1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1))) -
    1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 2)))

/-- The natural-number coefficient of a paired L1 block. -/
def stonehamBoundaryBlock (b p k : ℕ) : ℕ :=
  (b ^ ((p - 1) * p ^ (2 * k + 1)) - 1) / p ^ (2 * k + 1)

/-- The first (and larger) summand of `stonehamBoundaryTerm`.  It is the
positive majorant used to control the tail between consecutive blocks. -/
noncomputable def stonehamBoundaryMajorant (b p k : ℕ) : ℝ :=
  1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1)))

/-- The paired summand is an integer block whose right endpoint is
`p^(2k+2)`. -/
theorem stonehamBoundaryTerm_scaled_eq_block (b p k : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hpb : ¬ p ∣ b) :
    (b : ℝ) ^ (p ^ (2 * k + 2)) * stonehamBoundaryTerm b p k =
      stonehamBoundaryBlock b p k := by
  have hdvd := prime_pow_dvd_stoneham_boundary_block b p (2 * k + 1) hp hpb
  set q : ℕ := stonehamBoundaryBlock b p k with hq
  have hqN : p ^ (2 * k + 1) * q =
      b ^ ((p - 1) * p ^ (2 * k + 1)) - 1 := by
    rw [hq, stonehamBoundaryBlock]
    exact Nat.mul_div_cancel' hdvd
  have hone : 1 ≤ b ^ ((p - 1) * p ^ (2 * k + 1)) :=
    Nat.one_le_pow _ _ (by omega)
  have hqR : (p : ℝ) ^ (2 * k + 1) * q =
      b ^ ((p - 1) * p ^ (2 * k + 1)) - 1 := by
    norm_cast
  have hdiff : p ^ (2 * k + 2) =
      (p - 1) * p ^ (2 * k + 1) + p ^ (2 * k + 1) := by
    calc
      p ^ (2 * k + 2) = p ^ (2 * k + 1) * p := by
        simpa only [show 2 * k + 2 = 2 * k + 1 + 1 by omega] using
          pow_succ p (2 * k + 1)
      _ = ((p - 1) + 1) * p ^ (2 * k + 1) := by
        rw [Nat.sub_add_cancel hp.one_le, mul_comm]
      _ = (p - 1) * p ^ (2 * k + 1) + p ^ (2 * k + 1) := by ring
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hqdiv : ((b : ℝ) ^ ((p - 1) * p ^ (2 * k + 1)) - 1) /
      (p : ℝ) ^ (2 * k + 1) = q := by
    rw [div_eq_iff (pow_ne_zero _ hpR.ne')]
    linarith [hqR]
  rw [stonehamBoundaryTerm]
  rw [hdiff, pow_add]
  rw [← hqdiv]
  field_simp

/-- Once scaled beyond its right endpoint, a paired summand is an integer
base-`b` block followed by zeros. -/
theorem stonehamBoundaryTerm_scaled_eq_shifted_block (b p k q : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hpb : ¬ p ∣ b) (hq : p ^ (2 * k + 2) ≤ q) :
    (b : ℝ) ^ q * stonehamBoundaryTerm b p k =
      (b ^ (q - p ^ (2 * k + 2)) * stonehamBoundaryBlock b p k : ℕ) := by
  have hpow : (b : ℝ) ^ (q - p ^ (2 * k + 2)) * b ^ (p ^ (2 * k + 2)) =
      b ^ q := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (b : ℝ) ^ q * stonehamBoundaryTerm b p k =
        (b ^ (q - p ^ (2 * k + 2)) * b ^ (p ^ (2 * k + 2))) *
          stonehamBoundaryTerm b p k := by rw [hpow]
    _ = b ^ (q - p ^ (2 * k + 2)) *
          (b ^ (p ^ (2 * k + 2)) * stonehamBoundaryTerm b p k) := by ring
    _ = b ^ (q - p ^ (2 * k + 2)) * stonehamBoundaryBlock b p k := by
      rw [stonehamBoundaryTerm_scaled_eq_block b p k hb hp hpb]
    _ = (b ^ (q - p ^ (2 * k + 2)) * stonehamBoundaryBlock b p k : ℕ) := by
      push_cast
      rfl

/-- Every boundary term is nonnegative. -/
theorem stonehamBoundaryTerm_nonneg (b p k : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    0 ≤ stonehamBoundaryTerm b p k := by
  unfold stonehamBoundaryTerm
  apply sub_nonneg.mpr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hexp : p ^ (2 * k + 1) ≤ p ^ (2 * k + 2) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have hbpow : (b : ℝ) ^ (p ^ (2 * k + 1)) ≤ b ^ (p ^ (2 * k + 2)) :=
    pow_le_pow_right₀ hbR hexp
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left hbpow (pow_nonneg hpR.le _)

/-- The first summand majorizes the positive boundary term. -/
theorem stonehamBoundaryTerm_le_majorant (b p k : ℕ) :
    stonehamBoundaryTerm b p k ≤ stonehamBoundaryMajorant b p k := by
  unfold stonehamBoundaryTerm stonehamBoundaryMajorant
  have hnonneg : 0 ≤
      1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 2))) := by positivity
  linarith

/-- Later majorants decrease at least geometrically, uniformly in the prime
and the base. -/
theorem stonehamBoundaryMajorant_shift_le (b p k j : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) :
    stonehamBoundaryMajorant b p (j + k) ≤
      stonehamBoundaryMajorant b p k * (1 / 2 : ℝ) ^ j := by
  have hjp : j + 1 ≤ p ^ (2 * j) := by
    calc
      j + 1 ≤ p ^ j := Nat.lt_pow_self hp.two_le
      _ ≤ p ^ (2 * j) := Nat.pow_le_pow_right hp.pos (by omega)
  have hexp : p ^ (2 * k + 1) + j ≤ p ^ (2 * (j + k) + 1) := by
    have hP : 1 ≤ p ^ (2 * k + 1) := Nat.one_le_pow _ _ hp.one_le
    calc
      p ^ (2 * k + 1) + j ≤ p ^ (2 * k + 1) * (j + 1) := by nlinarith
      _ ≤ p ^ (2 * k + 1) * p ^ (2 * j) := Nat.mul_le_mul_left _ hjp
      _ = p ^ (2 * (j + k) + 1) := by rw [← pow_add]; congr 1 <;> omega
  have hpcoeff : (p : ℝ) ^ (2 * k + 1) ≤ p ^ (2 * (j + k) + 1) := by
    exact_mod_cast Nat.pow_le_pow_right hp.pos (by omega)
  have hbbase : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpow : (b : ℝ) ^ (p ^ (2 * k + 1)) * 2 ^ j ≤
      b ^ (p ^ (2 * (j + k) + 1)) := by
    calc
      (b : ℝ) ^ (p ^ (2 * k + 1)) * 2 ^ j ≤
          b ^ (p ^ (2 * k + 1)) * b ^ j := by gcongr
      _ = b ^ (p ^ (2 * k + 1) + j) := (pow_add _ _ _).symm
      _ ≤ b ^ (p ^ (2 * (j + k) + 1)) :=
        pow_le_pow_right₀ (by linarith) hexp
  have hden : (p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1)) * 2 ^ j ≤
      p ^ (2 * (j + k) + 1) * b ^ (p ^ (2 * (j + k) + 1)) := by
    calc
      (p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1)) * 2 ^ j =
          p ^ (2 * k + 1) * (b ^ (p ^ (2 * k + 1)) * 2 ^ j) := by ring
      _ ≤ p ^ (2 * (j + k) + 1) * b ^ (p ^ (2 * (j + k) + 1)) :=
        mul_le_mul hpcoeff hbpow (by positivity) (by positivity)
  unfold stonehamBoundaryMajorant
  rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  exact div_le_div_of_nonneg_left one_pos.le (by positivity) hden

/-- At any positive block index, twice a majorized tail scaled no farther
than its left endpoint is still below one. -/
theorem stonehamBoundaryMajorant_scaled_lt_half (b p k q : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hk : 1 ≤ k) (hq : q ≤ p ^ (2 * k + 1)) :
    2 * ((b : ℝ) ^ q * stonehamBoundaryMajorant b p k) < 1 := by
  have hbpow : (b : ℝ) ^ q ≤ b ^ (p ^ (2 * k + 1)) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) hq
  have hscaled : (b : ℝ) ^ q * stonehamBoundaryMajorant b p k ≤
      1 / (p : ℝ) ^ (2 * k + 1) := by
    calc
      (b : ℝ) ^ q * stonehamBoundaryMajorant b p k ≤
          b ^ (p ^ (2 * k + 1)) * stonehamBoundaryMajorant b p k :=
        mul_le_mul_of_nonneg_right hbpow (by unfold stonehamBoundaryMajorant; positivity)
      _ = 1 / (p : ℝ) ^ (2 * k + 1) := by
        unfold stonehamBoundaryMajorant
        field_simp
  have hp8 : 8 ≤ p ^ (2 * k + 1) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
      _ ≤ p ^ (2 * k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hp8R : (8 : ℝ) ≤ (p : ℝ) ^ (2 * k + 1) := by exact_mod_cast hp8
  have hrecip : 2 * (1 / (p : ℝ) ^ (2 * k + 1)) ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by norm_num) hp8R) (by norm_num)).trans_eq
    norm_num
  nlinarith

/-- The block summand is exactly the termwise pairing of the two Stoneham
series in `α_{b,p} - (p+1)α_{b,p²}`. -/
theorem stonehamBoundaryTerm_eq_pair (b p k : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    stonehamBoundaryTerm b p k =
      1 / ((p : ℝ) ^ (2 * k + 1) * b ^ (p ^ (2 * k + 1))) +
        1 / ((p : ℝ) ^ (2 * k + 2) * b ^ (p ^ (2 * k + 2))) -
          (p + 1) *
            (1 / (((p ^ 2 : ℕ) : ℝ) ^ (k + 1) *
              b ^ ((p ^ 2) ^ (k + 1)))) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hp_pow : (p ^ 2) ^ (k + 1) = p ^ (2 * k + 2) := by
    rw [← pow_mul]
    congr 1
  have hp_powR : (((p ^ 2 : ℕ) : ℝ) ^ (k + 1)) =
      (p : ℝ) ^ (2 * k + 2) := by exact_mod_cast hp_pow
  rw [stonehamBoundaryTerm, hp_pow, hp_powR]
  field_simp
  ring

/-- The positive block series is summable. -/
theorem summable_stonehamBoundaryTerm (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    Summable (stonehamBoundaryTerm b p) := by
  let f : ℕ → ℝ := fun j =>
    1 / ((p : ℝ) ^ (j + 1) * b ^ (p ^ (j + 1)))
  let g : ℕ → ℝ := fun k =>
    1 / (((p ^ 2 : ℕ) : ℝ) ^ (k + 1) * b ^ ((p ^ 2) ^ (k + 1)))
  have hf : Summable f := by
    simpa only [f] using StonehamSumsNormal.summable_stonehamAlpha_term b p
      (by omega) hp.two_le
  have hg : Summable g := by
    simpa only [g] using StonehamSumsNormal.summable_stonehamAlpha_term b (p ^ 2) (by omega)
      (by nlinarith [hp.two_le])
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective (by
    intro a c h
    omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective (by
    intro a c h
    change 2 * a + 1 = 2 * c + 1 at h
    omega)
  have hpair : Summable (fun k => f (2 * k) + f (2 * k + 1) - (p + 1) * g k) :=
    (he.add ho).sub (hg.mul_left _)
  refine hpair.congr fun k => ?_
  symm
  simpa only [f, g, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
    show 2 * k + 0 + 1 = 2 * k + 1 by omega] using
      stonehamBoundaryTerm_eq_pair b p k hb hp

/-- The L1 combination is the sum of its positive integer blocks. -/
theorem stoneham_sub_succ_mul_eq_tsum_boundary (b p : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) :
    stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2) =
      ∑' k, stonehamBoundaryTerm b p k := by
  let f : ℕ → ℝ := fun j =>
    1 / ((p : ℝ) ^ (j + 1) * b ^ (p ^ (j + 1)))
  let g : ℕ → ℝ := fun k =>
    1 / (((p ^ 2 : ℕ) : ℝ) ^ (k + 1) * b ^ ((p ^ 2) ^ (k + 1)))
  have hf : Summable f := by
    simpa only [f] using StonehamSumsNormal.summable_stonehamAlpha_term b p
      (by omega) hp.two_le
  have hg : Summable g := by
    simpa only [g] using StonehamSumsNormal.summable_stonehamAlpha_term b (p ^ 2) (by omega)
      (by nlinarith [hp.two_le])
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective (by
    intro a c h
    omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective (by
    intro a c h
    change 2 * a + 1 = 2 * c + 1 at h
    omega)
  have hsplit : (∑' k, f (2 * k)) + ∑' k, f (2 * k + 1) = ∑' j, f j :=
    tsum_even_add_odd he ho
  have hpair : ∑' k, stonehamBoundaryTerm b p k =
      (∑' k, f (2 * k)) + (∑' k, f (2 * k + 1)) - (p + 1) * ∑' k, g k := by
    calc
      ∑' k, stonehamBoundaryTerm b p k =
          ∑' k, (f (2 * k) + f (2 * k + 1) - (p + 1) * g k) := by
            apply tsum_congr
            intro k
            simpa only [f, g, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
              show 2 * k + 0 + 1 = 2 * k + 1 by omega] using
                stonehamBoundaryTerm_eq_pair b p k hb hp
      _ = (∑' k, (f (2 * k) + f (2 * k + 1))) - ∑' k, (p + 1) * g k :=
        (he.add ho).tsum_sub (hg.mul_left _)
      _ = (∑' k, f (2 * k)) + (∑' k, f (2 * k + 1)) -
          (p + 1) * ∑' k, g k := by rw [he.tsum_add ho, hg.tsum_mul_left]
  have hf_eq : (∑' j, f j) = stonehamAlpha b p := rfl
  have hg_eq : (∑' k, g k) = stonehamAlpha b (p ^ 2) := rfl
  rw [← hf_eq, ← hg_eq, ← hsplit, ← hpair]

/-- A uniform geometric majorant for all boundary blocks. -/
theorem stonehamBoundaryMajorant_le_geom (b p j : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    stonehamBoundaryMajorant b p j ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ j := by
  have hbp : 4 ≤ b ^ p := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
      _ ≤ b ^ p := Nat.pow_le_pow_right (by omega) hp.two_le
  have hdenN : 8 ≤ p * b ^ p := by nlinarith [hp.two_le]
  have hdenR : (8 : ℝ) ≤ (p : ℝ) * b ^ p := by exact_mod_cast hdenN
  have hzero : stonehamBoundaryMajorant b p 0 ≤ (1 / 8 : ℝ) := by
    rw [stonehamBoundaryMajorant]
    simp only [mul_zero, zero_add, pow_one]
    exact one_div_le_one_div_of_le (by norm_num) hdenR
  have hshift := stonehamBoundaryMajorant_shift_le b p 0 j hb hp
  simpa only [Nat.add_zero] using
    hshift.trans (mul_le_mul_of_nonneg_right hzero (by positivity))

/-- The L1 boundary combination itself lies in `[0,1)`, so its standard
base-`b` digits can be read without an integer-part correction. -/
theorem stoneham_sub_succ_mul_mem_Ico (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime) :
    stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2) ∈ Set.Ico (0 : ℝ) 1 := by
  rw [stoneham_sub_succ_mul_eq_tsum_boundary b p hb hp]
  constructor
  · exact tsum_nonneg fun k => stonehamBoundaryTerm_nonneg b p k hb hp
  · have hgeom : Summable fun k : ℕ => (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle : ∀ k, stonehamBoundaryTerm b p k ≤
        (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k := fun k =>
      (stonehamBoundaryTerm_le_majorant b p k).trans
        (stonehamBoundaryMajorant_le_geom b p k hb hp)
    have hsum := (summable_stonehamBoundaryTerm b p hb hp).tsum_le_tsum hle hgeom
    rw [tsum_mul_left, tsum_geometric_two] at hsum
    linarith

/-- Between the end of one L1 integer block and the beginning of the next,
all base-`b` digits vanish.  The indices are 0-based. -/
theorem digitOf_stoneham_sub_succ_mul_eq_zero (b p k i : ℕ) (hb : 2 ≤ b)
    (hp : p.Prime) (hpb : ¬ p ∣ b) (h₁ : p ^ (2 * k + 2) ≤ i)
    (h₂ : i < p ^ (2 * k + 3)) :
    digitOf b (Int.fract (stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2))) i = 0 := by
  set x : ℝ := stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2) with hx
  set q : ℕ := i + 1 with hq
  have hq_le : q ≤ p ^ (2 * k + 3) := by omega
  have hxfrac : Int.fract x = x :=
    Int.fract_eq_self.mpr (stoneham_sub_succ_mul_mem_Ico b p hb hp)
  set g : ℕ → ℝ := fun j => (b : ℝ) ^ q * stonehamBoundaryTerm b p j with hg
  have hgsum : Summable g := (summable_stonehamBoundaryTerm b p hb hp).mul_left _
  have hmul : x * (b : ℝ) ^ q = ∑' j, g j := by
    rw [hx, stoneham_sub_succ_mul_eq_tsum_boundary b p hb hp, tsum_mul_left, mul_comm]
  have hshift : Summable fun j => g (j + (k + 1)) :=
    (summable_nat_add_iff (k + 1)).2 hgsum
  have hsplit : ∑' j, g j =
      (∑ j ∈ Finset.range (k + 1), g j) + ∑' j, g (j + (k + 1)) :=
    (hgsum.sum_add_tsum_nat_add (k + 1)).symm
  set T : ℝ := ∑' j, g (j + (k + 1)) with hT
  set A : ℕ := ∑ j ∈ Finset.range (k + 1),
    b ^ (q - p ^ (2 * j + 2)) * stonehamBoundaryBlock b p j with hA
  have hHead : (∑ j ∈ Finset.range (k + 1), g j) = (A : ℝ) := by
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    have hjpow : p ^ (2 * j + 2) ≤ p ^ (2 * k + 2) :=
      Nat.pow_le_pow_right hp.pos (by omega)
    rw [hg]
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      stonehamBoundaryTerm_scaled_eq_shifted_block b p j q hb hp hpb
        (hjpow.trans (h₁.trans (by omega)))
  have hAb : b ∣ A := by
    rw [hA]
    refine Finset.dvd_sum fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    have hjpow : p ^ (2 * j + 2) ≤ p ^ (2 * k + 2) :=
      Nat.pow_le_pow_right hp.pos (by omega)
    have hexp : 0 < q - p ^ (2 * j + 2) := by omega
    exact Dvd.dvd.mul_right (dvd_pow_self b hexp.ne') _
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact tsum_nonneg fun j => by
      rw [hg]
      exact mul_nonneg (pow_nonneg (by positivity) _)
        (stonehamBoundaryTerm_nonneg b p _ hb hp)
  have hTlt : T < 1 := by
    have hterm : ∀ j, g (j + (k + 1)) ≤
        ((b : ℝ) ^ q * stonehamBoundaryMajorant b p (k + 1)) *
          (1 / 2 : ℝ) ^ j := by
      intro j
      rw [hg]
      calc
        (b : ℝ) ^ q * stonehamBoundaryTerm b p (j + (k + 1)) ≤
            b ^ q * stonehamBoundaryMajorant b p (j + (k + 1)) :=
          mul_le_mul_of_nonneg_left (stonehamBoundaryTerm_le_majorant b p _) (by positivity)
        _ ≤ b ^ q *
            (stonehamBoundaryMajorant b p (k + 1) * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left
            (stonehamBoundaryMajorant_shift_le b p (k + 1) j hb hp) (by positivity)
        _ = (b ^ q * stonehamBoundaryMajorant b p (k + 1)) *
            (1 / 2 : ℝ) ^ j := by ring
    have hgeom : Summable fun j : ℕ =>
        ((b : ℝ) ^ q * stonehamBoundaryMajorant b p (k + 1)) *
          (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift.tsum_le_tsum hterm hgeom
    rw [hT]
    refine lt_of_le_of_lt hle ?_
    rw [tsum_mul_left, tsum_geometric_two]
    simpa [mul_comm] using
      stonehamBoundaryMajorant_scaled_lt_half b p (k + 1) q hb hp (by omega) (by
        simpa only [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using hq_le)
  have hval : x * (b : ℝ) ^ q = (A : ℝ) + T := by
    rw [hmul, hsplit, hHead]
  have hfl : ⌊x * (b : ℝ) ^ q⌋ = (A : ℤ) := by
    rw [hval, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold digitOf
  rw [hxfrac, ← hq, hfl, Int.toNat_natCast, Nat.mod_eq_zero_of_dvd hAb]

/-- **Bailey--Borwein boundary witness L1.**  For every prime `p` coprime to
the base, the same-class combination `α_{b,p} - (p+1)α_{b,p²}` has arbitrarily
long zero windows and is therefore not even simply normal. -/
@[blueprint (title := "Same-class Stoneham combinations need not be simply normal")]
theorem not_isSimplyNormal_stoneham_sub_succ_mul (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    ¬ IsSimplyNormal b (stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2)) := by
  classical
  intro hnormal
  let x := stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2)
  let s : ℕ → ℕ := digitOf b (Int.fract x)
  let Z : ℕ → ℕ := fun n => ((Finset.range n).filter fun i => s i = 0).card
  have hcount (n : ℕ) : countOccurrences [0] ((List.range n).map s) = Z n :=
    Failures.countOccurrences_zero_eq_card s n
  have hlim : Tendsto (fun n => (Z n : ℝ) / n) atTop (nhds (1 / b : ℝ)) := by
    simpa [x, s, hcount, Z] using hnormal 0 (by omega)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨K, hK⟩ := hlim (1 / (4 * (b : ℝ))) (by positivity)
  let k := max K 1
  let n₁ := p ^ (2 * k + 2)
  let n₂ := p ^ (2 * k + 3)
  have hkK : K ≤ k := le_max_left _ _
  have hkpow : k ≤ p ^ k := (Nat.lt_pow_self hp.two_le).le
  have hn₁K : K ≤ n₁ := by
    dsimp [n₁]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right hp.pos (by omega)))
  have hn₂K : K ≤ n₂ := by
    dsimp [n₂]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right hp.pos (by omega)))
  have hn₁₂ : n₁ ≤ n₂ := by
    dsimp [n₁, n₂]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hforced : ∀ i, i ∈ Finset.Ico n₁ n₂ → s i = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact digitOf_stoneham_sub_succ_mul_eq_zero b p k i hb hp hpb hi.1 hi.2
  have hstep : Z n₁ + (n₂ - n₁) ≤ Z n₂ := by
    have hdisj : Disjoint ((Finset.range n₁).filter fun i => s i = 0)
        (Finset.Ico n₁ n₂) := by
      rw [Finset.disjoint_left]
      intro a ha hab
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_Ico] at hab
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
  have hn₁pos : (0 : ℝ) < n₁ := by
    exact_mod_cast (pow_pos hp.pos (2 * k + 2))
  have hn₂pos : (0 : ℝ) < n₂ := by
    exact_mod_cast (pow_pos hp.pos (2 * k + 3))
  have heps : (1 / (b : ℝ) - 1 / (4 * b)) = 3 / (4 * b) := by
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have heps' : (1 / (b : ℝ) + 1 / (4 * b)) = 5 / (4 * b) := by
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have e₁ : (3 / (4 * (b : ℝ))) * (n₁ : ℝ) < Z n₁ := by
    have hx : (1 / (b : ℝ) - 1 / (4 * b)) < (Z n₁ : ℝ) / n₁ := by
      linarith [h₁.1]
    rw [heps, lt_div_iff₀ hn₁pos] at hx
    exact hx
  have e₂ : (Z n₂ : ℝ) < (5 / (4 * (b : ℝ))) * n₂ := by
    have hx : (Z n₂ : ℝ) / n₂ <
        (1 / (b : ℝ) + 1 / (4 * b)) := by linarith [h₂.2]
    rw [heps', div_lt_iff₀ hn₂pos] at hx
    exact hx
  have e₃ : (Z n₁ : ℝ) + ((n₂ : ℝ) - n₁) ≤ Z n₂ := by
    have hc := (Nat.cast_le (α := ℝ)).2 hstep
    push_cast [Nat.cast_sub hn₁₂] at hc
    linarith
  have hn₂eq : (n₂ : ℝ) = (p : ℝ) * n₁ := by
    dsimp [n₁, n₂]
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, pow_succ]
    push_cast
    ring
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb4pos : (0 : ℝ) < 4 * b := by positivity
  have e₁' : 3 * (n₁ : ℝ) < 4 * b * Z n₁ := by
    have := mul_lt_mul_of_pos_left e₁ hb4pos
    field_simp at this
    nlinarith
  have e₂' : 4 * b * Z n₂ < 5 * (n₂ : ℝ) := by
    have := mul_lt_mul_of_pos_left e₂ hb4pos
    field_simp at this
    nlinarith
  have e₃' : 4 * b * ((Z n₁ : ℝ) + ((n₂ : ℝ) - n₁)) ≤
      4 * b * Z n₂ := mul_le_mul_of_nonneg_left e₃ hb4pos.le
  have hmul : 2 * (p - 1) ≤ b * (p - 1) := Nat.mul_le_mul_right (p - 1) hb
  have hmul4 : 8 * (p - 1) ≤ 4 * b * (p - 1) := by
    calc
      8 * (p - 1) = 4 * (2 * (p - 1)) := by ring
      _ ≤ 4 * (b * (p - 1)) := Nat.mul_le_mul_left 4 hmul
      _ = 4 * b * (p - 1) := by ring
  have hp2 : 2 ≤ p := hp.two_le
  have hcoefN : 5 * p < 3 + 4 * b * (p - 1) := by omega
  have hcoefCast : ((5 * p : ℕ) : ℝ) < ((3 + 4 * b * (p - 1) : ℕ) : ℝ) := by
    exact_mod_cast hcoefN
  have hcoef : (5 : ℝ) * p < 3 + 4 * b * (p - 1) := by
    push_cast [Nat.cast_sub hp.one_le] at hcoefCast
    exact hcoefCast
  rw [hn₂eq] at e₂' e₃'
  have hn₁nonneg : (0 : ℝ) ≤ n₁ := hn₁pos.le
  nlinarith [mul_pos (sub_pos.mpr hcoef) hn₁pos]

end NormalNumbers
