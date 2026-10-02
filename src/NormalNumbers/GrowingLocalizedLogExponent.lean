/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureVandeheyDifferencing

/-!
# The exponent window for Vandehey's Theorem 5.1, without the constant `c`

Crux N8 of the `ζ_Y` campaign needs a replacement for Vandehey's Lemma 6.3 (the tabulated
windows `Ĩ_k` and the constant `c ∈ (−1.1710, −1.1709)`).  This file supplies one.

The key quantity is `F_k = (ν_k − γ_k)(2^{k+1} − 1) = (ν_k − γ_k)/(2α_k)`.  It obeys
`F_{k+1} = F_k(1 − α_k) + 1` with `F_0 = 1`, so `k − 1 < F_k ≤ k + 1`, and each step
adds `1 − α_k F_k ∈ [0, 1]`.  Together with `γ_k + ν_k = 2 − 2^{−k}` this gives
`gamma_add_alpha_le`/`nu_sub_alpha_le`: whenever `|F_k − y| ≤ 3/4`, both Vandehey exponents at
`m = N^y` are `≤ 1 − 2^{−k−4}`.  A discrete intermediate-value step (`exists_window`) finds such a
`k ≤ y + 2` for every `y ≥ 1/4`.

`vandehey_window_bound` is the consumable form: for `2 ≤ L ≤ m^4` there is a `k ≤ log m/log L + 2`
with `‖Σ_{n≤L} e(a bⁿ/m)‖ ≤ (A_k + B_k) L^{1−2^{−k−4}} (1 + log m)^{2^{−k}}`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open NormalNumbers.Literature.VandeheyDiff NormalNumbers.G4 Finset

lemma two_pow_ge (k : ℕ) : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
  have := (Nat.lt_two_pow_self (n := k))
  exact_mod_cast this

lemma alpha_eq (k : ℕ) : alpha k = 1 / (4 * (2 : ℝ) ^ k - 2) := by
  simp only [alpha, pow_add]; ring_nf

lemma alpha_pos (k : ℕ) : 0 < alpha k := by
  rw [alpha_eq]; have := two_pow_ge k; apply div_pos one_pos; linarith

lemma alpha_le (k : ℕ) : alpha k ≤ 1 / (2 * (2 : ℝ) ^ k) := by
  rw [alpha_eq]; have := two_pow_ge k
  apply one_div_le_one_div_of_le (by positivity); linarith

lemma expPair_succ (k : ℕ) : expPair (k + 1) =
    ((1 + (expPair k).1 + alpha k * (expPair k).2) / (2 * (1 + alpha k)),
     (1 + (expPair k).2) / 2 + (1 + (expPair k).1 - (expPair k).2) * alpha k
        / (2 * (1 + alpha k))) := rfl

/-- Vandehey eq. (15): `γ_k + ν_k = 2 − 2^{−k}`. -/
lemma expPair_sum (k : ℕ) : (expPair k).1 + (expPair k).2 = 2 - 1 / (2 : ℝ) ^ k := by
  induction k with
  | zero => simp [expPair]; norm_num
  | succ k ih =>
    rw [expPair_succ]
    have ha := alpha_pos k
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have e : (expPair k).2 = 2 - 1 / (2 : ℝ) ^ k - (expPair k).1 := by linarith
    rw [e, pow_succ]; field_simp; ring

/-- `F_k = (ν_k − γ_k)(2·2^k − 1)`. -/
noncomputable def F (k : ℕ) : ℝ := ((expPair k).2 - (expPair k).1) * (2 * (2 : ℝ) ^ k - 1)

lemma F_zero : F 0 = 1 := by simp [F, expPair]; norm_num

lemma alpha_mul_two_pow (k : ℕ) : alpha k * (2 * (2 : ℝ) ^ k - 1) = 1 / 2 := by
  rw [alpha_eq]; have := two_pow_ge k
  have : (4 * (2 : ℝ) ^ k - 2) ≠ 0 := by linarith
  field_simp; ring

lemma alpha_F (k : ℕ) : alpha k * F k = ((expPair k).2 - (expPair k).1) / 2 := by
  have := alpha_mul_two_pow k
  simp only [F]
  calc alpha k * (((expPair k).2 - (expPair k).1) * (2 * 2 ^ k - 1))
      = ((expPair k).2 - (expPair k).1) * (alpha k * (2 * 2 ^ k - 1)) := by ring
    _ = _ := by rw [this]; ring

lemma F_succ (k : ℕ) : F (k + 1) = F k * (1 - alpha k) + 1 := by
  have ha := alpha_pos k
  have h1 := two_pow_ge k
  simp only [F, expPair_succ, alpha_eq, pow_succ]
  have : (4 * (2 : ℝ) ^ k - 2) ≠ 0 := by linarith
  have : (4 * (2 : ℝ) ^ k - 2 + 1) ≠ 0 := by linarith
  field_simp
  ring

lemma F_bounds (k : ℕ) :
    (k : ℝ) - 1 + ((k : ℝ) + 2) / (2 : ℝ) ^ k ≤ F k ∧ F k ≤ (k : ℝ) + 1 := by
  induction k with
  | zero => simp [F_zero]; norm_num
  | succ k ih =>
    obtain ⟨hl, hu⟩ := ih
    have ha := alpha_pos k
    have hal := alpha_le k
    have ht := two_pow_ge k
    have htp : (0 : ℝ) < 2 ^ k := by positivity
    have hq : ((k : ℝ) + 2) / 2 ^ k ≤ 2 := by
      rw [div_le_iff₀ htp]; linarith
    have hq0 : 0 ≤ ((k : ℝ) + 2) / 2 ^ k := by positivity
    have hF0 : 0 ≤ F k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [F_zero]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
    have ha1 : alpha k ≤ 1 := by
      have : 1 / (2 * (2 : ℝ) ^ k) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    rw [F_succ]
    push_cast
    constructor
    · -- `L_k + 1 − L_{k+1} = (k+1)/(2·2^k) ≥ α (k+1) ≥ α L_k`
      have key : alpha k * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) / (2 * 2 ^ k) := by
        calc alpha k * ((k : ℝ) + 1) ≤ 1 / (2 * 2 ^ k) * ((k : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hal (by positivity)
          _ = _ := by ring
      have e : ((k : ℝ) + 1 + 2) / 2 ^ (k + 1) = ((k : ℝ) + 2) / 2 ^ k - ((k : ℝ) + 1) / (2 * 2 ^ k) := by
        rw [pow_succ]; field_simp; ring
      rw [e]
      have hLk : (k : ℝ) - 1 + ((k : ℝ) + 2) / 2 ^ k ≤ (k : ℝ) + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : (0:ℝ) ≤ 1 - alpha k),
        mul_le_mul_of_nonneg_left hLk ha.le]
    · nlinarith [mul_nonneg ha.le hF0]

lemma F_nonneg (k : ℕ) : 0 ≤ F k := by
  have := (F_bounds k).1
  have : 0 ≤ ((k : ℝ) + 2) / (2 : ℝ) ^ k := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [F_zero]
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith

lemma F_step_le (k : ℕ) : F (k + 1) ≤ F k + 1 := by
  rw [F_succ]; nlinarith [mul_nonneg (alpha_pos k).le (F_nonneg k)]

/-- **Discrete window.**  For every `y ≥ 1/4` some `k ≤ y + 2` has `|F_k − y| ≤ 3/4`. -/
theorem exists_window (y : ℝ) (hy : 1 / 4 ≤ y) :
    ∃ k : ℕ, (k : ℝ) ≤ y + 2 ∧ |F k - y| ≤ 3 / 4 := by
  classical
  have hex : ∃ k : ℕ, y - 3 / 4 ≤ F k := by
    obtain ⟨n, hn⟩ := exists_nat_gt (y + 1)
    refine ⟨n, ?_⟩
    have := (F_bounds n).1
    have : 0 ≤ ((n : ℝ) + 2) / (2 : ℝ) ^ n := by positivity
    linarith
  set k := Nat.find hex with hk
  have hspec : y - 3 / 4 ≤ F k := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, F_zero] at hspec
    refine ⟨0, by simp; linarith, ?_⟩
    rw [F_zero, abs_le]; constructor <;> linarith
  · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hmin : ¬ (y - 3 / 4 ≤ F j) := Nat.find_min hex (by omega)
    push Not at hmin
    have hstep := F_step_le j
    have hjl := (F_bounds j).1
    have : 0 ≤ ((j : ℝ) + 2) / (2 : ℝ) ^ j := by positivity
    refine ⟨k, ?_, ?_⟩
    · rw [hj]; push_cast; linarith
    · rw [abs_le]; rw [hj] at hspec ⊢; constructor <;> linarith

lemma gamma_eq (k : ℕ) :
    (expPair k).1 = 1 - 1 / (2 * (2 : ℝ) ^ k) - alpha k * F k := by
  have hs := expPair_sum k
  rw [alpha_F]
  have : (2 : ℝ) ^ k ≠ 0 := by positivity
  have e : 1 / (2 : ℝ) ^ k = 2 * (1 / (2 * 2 ^ k)) := by field_simp
  linarith

lemma nu_eq (k : ℕ) :
    (expPair k).2 = 1 - 1 / (2 * (2 : ℝ) ^ k) + alpha k * F k := by
  have hs := expPair_sum k
  have hg := gamma_eq k
  have : (2 : ℝ) ^ k ≠ 0 := by positivity
  have e : 1 / (2 : ℝ) ^ k = 2 * (1 / (2 * 2 ^ k)) := by field_simp
  linarith

lemma alpha_mul_le (k : ℕ) : 3 / 4 * alpha k ≤ 1 / (2 * (2 : ℝ) ^ k) - 1 / (2 : ℝ) ^ (k + 4) := by
  rw [alpha_eq]
  have ht := two_pow_ge k
  have htp : (0 : ℝ) < 2 ^ k := by positivity
  rw [pow_add]
  have hpos : (0 : ℝ) < 4 * 2 ^ k - 2 := by linarith
  rw [show 1 / (2 * (2 : ℝ) ^ k) - 1 / (2 ^ k * 2 ^ 4) = 7 / (16 * 2 ^ k) by field_simp; ring]
  rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-- Both Vandehey exponents at `m = N^y` save `2^{−k−4}` once `|F_k − y| ≤ 3/4`. -/
theorem exponents_le (k : ℕ) (y : ℝ) (h : |F k - y| ≤ 3 / 4) :
    alpha k * y + (expPair k).1 ≤ 1 - 1 / (2 : ℝ) ^ (k + 4) ∧
    -(alpha k * y) + (expPair k).2 ≤ 1 - 1 / (2 : ℝ) ^ (k + 4) := by
  rw [gamma_eq, nu_eq]
  have ha := alpha_pos k
  have hm := alpha_mul_le k
  rw [abs_le] at h
  constructor <;> nlinarith

lemma constPair_nonneg (b : ℕ) (P : Finset ℕ) (k : ℕ) :
    0 ≤ (constPair b P k).1 ∧ 0 ≤ (constPair b P k).2 := by
  cases k with
  | zero => simp [constPair]
  | succ k => exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩

/-- **Consumable Theorem 5.1 at a self-chosen depth.**  For `2 ≤ L` and `L ≤ m^4` there is a
depth `k ≤ log m / log L + 2` at which the Korobov sum of length `L` saves `L^{−2^{−k−4}}`,
at the cost `(A_k + B_k)(1 + log m)^{2^{−k}}`. -/
theorem vandehey_window_bound (hV : VandeheyThm51) (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p b) (m : ℕ) (hm : 2 ≤ m)
    (hmP : ∀ p, p.Prime → p ∣ m → p ∈ P) (a : ℤ) (ha : IsCoprime a (m : ℤ)) (L : ℕ)
    (hL : 2 ≤ L) (hLm : Real.log L ≤ 4 * Real.log m) :
    ∃ k : ℕ, (k : ℝ) ≤ Real.log m / Real.log L + 2 ∧
      ‖∑ n ∈ Icc 1 L, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
        ((constPair b P k).1 + (constPair b P k).2) *
          (L : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) * (1 + Real.log m) ^ ((2 : ℝ) ^ (-(k : ℝ))) := by
  have hLpos : (0 : ℝ) < Real.log L := Real.log_pos (by exact_mod_cast hL)
  set y := Real.log m / Real.log L with hy
  have hy4 : 1 / 4 ≤ y := by
    rw [hy, le_div_iff₀ hLpos]; linarith
  obtain ⟨k, hk, hw⟩ := exists_window y hy4
  refine ⟨k, hk, ?_⟩
  have hbound := hV b hb P hP m hm hmP a ha k L (by omega)
  refine hbound.trans ?_
  obtain ⟨e1, e2⟩ := exponents_le k y hw
  obtain ⟨hA, hB⟩ := constPair_nonneg b P k
  have hL0 : (0 : ℝ) < L := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hm0 : (0 : ℝ) < m := by positivity
  -- `m = L^y`
  have hmL : (m : ℝ) = (L : ℝ) ^ y := by
    rw [Real.rpow_def_of_pos hL0, hy, mul_div_cancel₀ _ hLpos.ne', Real.exp_log hm0]
  have hlog : 0 ≤ (1 + Real.log m) ^ ((2 : ℝ) ^ (-(k : ℝ))) := by
    apply Real.rpow_nonneg; have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m) :
      (1 : ℝ) ≤ m); linarith
  have t1 : (m : ℝ) ^ alpha k * (L : ℝ) ^ (expPair k).1 ≤ (L : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) := by
    rw [hmL, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have t2 : (m : ℝ) ^ (-alpha k) * (L : ℝ) ^ (expPair k).2 ≤
      (L : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) := by
    rw [hmL, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  apply mul_le_mul_of_nonneg_right _ hlog
  calc (constPair b P k).1 * (m : ℝ) ^ alpha k * (L : ℝ) ^ (expPair k).1 +
        (constPair b P k).2 * (m : ℝ) ^ (-alpha k) * (L : ℝ) ^ (expPair k).2
      = (constPair b P k).1 * ((m : ℝ) ^ alpha k * (L : ℝ) ^ (expPair k).1) +
        (constPair b P k).2 * ((m : ℝ) ^ (-alpha k) * (L : ℝ) ^ (expPair k).2) := by ring
    _ ≤ (constPair b P k).1 * (L : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) +
        (constPair b P k).2 * (L : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 4)) := by
      gcongr
    _ = _ := by ring

end NormalNumbers.GrowingLocalizedLog
