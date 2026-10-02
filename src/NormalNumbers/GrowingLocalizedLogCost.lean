/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogExponent
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The cost side of crux N8: a closed-form bound on Vandehey's `A_k + B_k`

This is a crude form of Vandehey's Lemma 5.4, enough for `ζ_Y`.  With `s = |P|` and
`X = 2^{3s+2} Q M`:

* `cP_le`: `C_{P,x} ≤ (3/x)^s` for `0 < x ≤ 1`.  Each factor is `1 + 1/(p^x − 1)`, and
  `p^x − 1 ≥ x log 2 > x/2`.
* `cP_le_two`: `C_{P,x} ≤ 2^s` for `x ≥ 1`.
* `constPair_snd_le`: `B_k ≤ X`, and `constPair_fst_le`: `A_k ≤ 8 X 2^{(k+5)s}`.

So `A_k + B_k ≤ 9 · 2^{3s+2} Q M · 2^{(k+5)s}` (`constPair_sum_le`).  The `2^{ks}` growth is
Vandehey's Remark 5.5, and it cannot be removed.
-/

namespace NormalNumbers.GrowingLocalizedLog

open NormalNumbers.Literature.VandeheyDiff Finset

/-- `v ≥ 1 + d`, `d > 0` ⟹ `v/(v − 1) ≤ 1 + 1/d`. -/
lemma div_sub_one_le {v d : ℝ} (hd : 0 < d) (hv : 1 + d ≤ v) : v / (v - 1) ≤ 1 + 1 / d := by
  have h1 : 0 < v - 1 := by linarith
  rw [div_le_iff₀ h1]
  have : 1 ≤ (v - 1) * (1 / d) := by rw [mul_one_div, le_div_iff₀ hd]; linarith
  nlinarith

lemma rpow_ge_one_add {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 0 < x) :
    1 + x / 2 ≤ (p : ℝ) ^ x := by
  have h2 : (2 : ℝ) ^ x ≤ (p : ℝ) ^ x :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hx.le
  have : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) := Real.rpow_def_of_pos (by norm_num) x
  have he := Real.add_one_le_exp (Real.log 2 * x)
  have hl := Real.log_two_gt_d9
  nlinarith

lemma factor_pos {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 0 < x) :
    0 < (p : ℝ) ^ x / ((p : ℝ) ^ x - 1) := by
  have := rpow_ge_one_add hp hx
  apply div_pos <;> linarith

lemma cP_le {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    cP P x ≤ (3 / x) ^ P.card := by
  unfold cP
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod (fun p hp => (factor_pos (hP p hp) hx).le)
  intro p hp
  have hd : 0 < x / 2 := by linarith
  refine (div_sub_one_le hd (rpow_ge_one_add (hP p hp) hx)).trans ?_
  rw [show 1 / (x / 2) = 2 / x by field_simp, show (3 : ℝ) / x = 1 / x + 2 / x by ring]
  have : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  linarith

lemma cP_le_two {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    cP P x ≤ 2 ^ P.card := by
  unfold cP
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod (fun p hp => (factor_pos (hP p hp) (by linarith)).le)
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
  have : (p : ℝ) ≤ (p : ℝ) ^ x := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hx
  have := div_sub_one_le (by norm_num : (0 : ℝ) < 1) (by linarith : 1 + 1 ≤ (p : ℝ) ^ x)
  linarith

lemma cP_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {x : ℝ} (hx : 0 < x) : 0 ≤ cP P x :=
  Finset.prod_nonneg fun p hp => (factor_pos (hP p hp) hx).le

lemma primeProd_ge_one {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) : (1 : ℝ) ≤ primeProd P := by
  unfold primeProd
  have : 1 ≤ ∏ p ∈ P, p := Finset.one_le_prod' fun p hp => by have := hP p hp; omega
  exact_mod_cast this

lemma bigM_ge_one (b : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) : (1 : ℝ) ≤ bigM b P := by
  unfold bigM
  have : 1 ≤ ∏ p ∈ P, p ^ padicValNat p (b ^ (2 * orderOf (b : ZMod (primeProd P))) - 1) :=
    Finset.one_le_prod' fun p hp => Nat.one_le_pow _ _ (by have := hP p hp; omega)
  exact_mod_cast this

/-- `X = 2^{3s+2} Q M`. -/
noncomputable def costX (b : ℕ) (P : Finset ℕ) : ℝ :=
  (2 : ℝ) ^ (3 * P.card + 2) * primeProd P * bigM b P

lemma alpha_le_half (k : ℕ) : alpha k ≤ 1 / 2 := by
  have := alpha_le k
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have : 1 / (2 * (2 : ℝ) ^ k) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  linarith

lemma constPair_snd_le (b : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (k : ℕ) :
    (constPair b P k).2 ≤ costX b P := by
  have hQ := primeProd_ge_one hP
  have hM := bigM_ge_one b hP
  have hs : (1 : ℝ) ≤ 2 ^ P.card := one_le_pow₀ (by norm_num)
  induction k with
  | zero =>
    simp only [constPair, costX]
    have : (1 : ℝ) ≤ 2 ^ (3 * P.card + 2) := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ primeProd P)]
  | succ k ih =>
    simp only [constPair]
    set B := (constPair b P k).2
    have hB0 : 0 ≤ B := (constPair_nonneg b P k).2
    have ha := alpha_pos k
    have ha2 := alpha_le_half k
    have hX0 : 0 ≤ costX b P := hB0.trans ih
    rw [Real.sqrt_le_iff]
    refine ⟨hX0, ?_⟩
    have h2 : (2 : ℝ) ^ (1 + alpha k) ≤ 4 := by
      calc (2 : ℝ) ^ (1 + alpha k) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have hQa : (primeProd P : ℝ) ^ alpha k ≤ primeProd P := by
      conv_rhs => rw [← Real.rpow_one (primeProd P : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
    have hC : cP P (1 - alpha k) ≤ 2 ^ (3 * P.card) := by
      refine (cP_le hP (by linarith) (by linarith)).trans ?_
      rw [pow_mul]
      apply pow_le_pow_left₀ (by apply div_nonneg <;> linarith)
      rw [div_le_iff₀ (by linarith)]; norm_num; linarith
    have hC0 := cP_nonneg hP (by linarith : 0 < 1 - alpha k)
    have hQa0 : 0 ≤ (primeProd P : ℝ) ^ alpha k := Real.rpow_nonneg (by linarith) _
    have h20 : 0 ≤ (2 : ℝ) ^ (1 + alpha k) := Real.rpow_nonneg (by norm_num) _
    calc (2 : ℝ) ^ (1 + alpha k) * B * (bigM b P : ℝ) * (primeProd P : ℝ) ^ alpha k *
          cP P (1 - alpha k)
        ≤ 4 * costX b P * (bigM b P : ℝ) * primeProd P * 2 ^ (3 * P.card) := by gcongr
      _ = costX b P ^ 2 := by simp only [costX]; ring

lemma constPair_fst_le (b : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (k : ℕ) :
    (constPair b P k).1 ≤ 8 * costX b P * 2 ^ ((k + 5) * P.card) := by
  have hQ := primeProd_ge_one hP
  have hM := bigM_ge_one b hP
  set s := P.card
  have hu : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hX1 : (1 : ℝ) ≤ costX b P := by
    simp only [costX]
    have : (1 : ℝ) ≤ 2 ^ (3 * s + 2) := one_le_pow₀ (by norm_num)
    have := mul_le_mul this hQ zero_le_one (by linarith)
    nlinarith
  induction k with
  | zero =>
    simp only [constPair]
    have : (1 : ℝ) ≤ 2 ^ ((0 + 5) * s) := one_le_pow₀ (by norm_num)
    nlinarith
  | succ k ih =>
    simp only [constPair]
    set A := (constPair b P k).1
    set B := (constPair b P k).2
    obtain ⟨hA0, hB0⟩ := constPair_nonneg b P k
    have hBX := constPair_snd_le b hP k
    have ha := alpha_pos k
    have ha2 := alpha_le_half k
    set X := costX b P
    set W : ℝ := 2 ^ ((k + 4) * s)
    have hW : (1 : ℝ) ≤ W := one_le_pow₀ (by norm_num)
    have hWu : (2 : ℝ) ^ s ≤ W := pow_le_pow_right₀ (by norm_num) (by nlinarith)
    have hZ : (2 : ℝ) ^ ((k + 5) * s) = W * 2 ^ s := by
      simp only [W]; rw [← pow_add]; ring_nf
    have hZ' : (2 : ℝ) ^ ((k + 1 + 5) * s) = W * 2 ^ s * 2 ^ s := by
      simp only [W]; rw [← pow_add, ← pow_add]; ring_nf
    rw [hZ] at ih
    rw [hZ', Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    -- the three terms under the square root
    have hs2 : ((2 : ℝ) ^ ((s : ℝ) + 2)) = 2 ^ (s + 2) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    have hsQ : (2 : ℝ) ^ (s + 2) * primeProd P ≤ X := by
      simp only [X, costX]
      have : (2 : ℝ) ^ (s + 2) ≤ 2 ^ (3 * s + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have := mul_le_mul this hQ (by linarith) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ) ≤ 2 ^ (3 * s + 2) * primeProd P)]
    have hQX : (primeProd P : ℝ) ≤ X := by
      have : (1 : ℝ) ≤ 2 ^ (s + 2) := one_le_pow₀ (by norm_num)
      nlinarith
    have hMX : (bigM b P : ℝ) ≤ X := by
      simp only [X, costX]
      have : (1 : ℝ) ≤ 2 ^ (3 * s + 2) * primeProd P := by
        have : (1 : ℝ) ≤ 2 ^ (3 * s + 2) := one_le_pow₀ (by norm_num)
        nlinarith
      nlinarith
    have hCa : cP P (alpha k) ≤ W := by
      refine (cP_le hP ha (by linarith)).trans ?_
      show (3 / alpha k) ^ s ≤ _
      simp only [W]; rw [pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      rw [alpha_eq, div_div_eq_mul_div, div_one]
      have : (4 : ℝ) * 2 ^ k - 2 ≤ 4 * 2 ^ k := by linarith
      calc 3 * (4 * (2 : ℝ) ^ k - 2) ≤ 3 * (4 * 2 ^ k) := by linarith
        _ ≤ 2 ^ (k + 4) := by rw [pow_add]; norm_num; nlinarith [pow_pos (two_pos : (0:ℝ) < 2) k]
    have hC1 : cP P (1 + alpha k) ≤ 2 ^ s := cP_le_two hP (by linarith)
    have hCa0 := cP_nonneg hP ha
    have hC10 := cP_nonneg hP (by linarith : 0 < 1 + alpha k)
    set Z := 8 * X * (W * 2 ^ s)
    have hAZ : A + B ≤ 2 * Z := by
      have : X ≤ Z := by simp only [Z]; nlinarith [mul_le_mul hW hu zero_le_one (by linarith)]
      linarith
    rw [hs2]
    have t1 : (2 : ℝ) ^ (s + 2) * primeProd P * (A + B) * cP P (alpha k) ≤ X * (2 * Z) * W := by
      gcongr
    have t2 : 2 * (primeProd P : ℝ) ≤ X * Z * W := by
      have : 8 ≤ Z := by simp only [Z]; nlinarith [mul_le_mul hW hu zero_le_one (by linarith)]
      nlinarith [mul_le_mul hX1 hW zero_le_one (by linarith)]
    have t3 : 2 * A * (bigM b P : ℝ) * cP P (1 + alpha k) ≤ 2 * Z * X * W := by
      have : A ≤ Z := ih
      have : cP P (1 + alpha k) ≤ W := hC1.trans hWu
      gcongr
    have hZ0 : 0 ≤ Z := by positivity
    calc (2 : ℝ) ^ (s + 2) * primeProd P * (A + B) * cP P (alpha k) + 2 * primeProd P +
          2 * A * bigM b P * cP P (1 + alpha k)
        ≤ 5 * (X * Z * W) := by nlinarith
      _ ≤ (8 * X * (W * 2 ^ s * 2 ^ s)) ^ 2 := by
        simp only [Z]
        have hX0 : 0 ≤ X := by linarith
        have hW0 : 0 ≤ W := by linarith
        have : (1:ℝ) ≤ 2 ^ s * 2 ^ s * 2 ^ s := by nlinarith
        have : 0 ≤ X * X * W * W * 2 ^ s := by positivity
        nlinarith

/-- **Closed-form cost**: `A_k + B_k ≤ 9 X 2^{(k+5)s}`, `X = 2^{3s+2} Q M`. -/
theorem constPair_sum_le (b : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (k : ℕ) :
    (constPair b P k).1 + (constPair b P k).2 ≤ 9 * costX b P * 2 ^ ((k + 5) * P.card) := by
  have h1 := constPair_fst_le b hP k
  have h2 := constPair_snd_le b hP k
  have : (1 : ℝ) ≤ 2 ^ ((k + 5) * P.card) := one_le_pow₀ (by norm_num)
  have : 0 ≤ costX b P := ((constPair_nonneg b P k).2).trans h2
  nlinarith

end NormalNumbers.GrowingLocalizedLog
