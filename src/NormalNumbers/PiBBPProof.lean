/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import NormalNumbers.PiBBP

/-!
# Lane-2 discharge of the frozen node `PiBBP`

The one obligation of this file is `piBBP_proved : PiBBP`, i.e. the BBP
formula `HasSum bbpTerm Real.pi` (Bailey–Borwein–Plouffe, Math. Comp. 66
(1997) 903–913).

## Route: complex log Taylor series, no integrals

Instead of the classical `∫₀^{1/√2}` computation we run the roots-of-unity
filter through mathlib's `Complex.hasSum_taylorSeries_neg_log`
(`∑ zⁿ/n = -log(1-z)` on the open unit disk).  With `x = 1/√2` and
`ω = e^{iπ/4}`, the BBP summand is the residue-class-mod-8 repackaging of
the single series `∑ c_{n mod 8} xⁿ/n`, whose character decomposition has
exactly four nonvanishing frequencies:

  `w n = (-2·xⁿ - 2·(-x)ⁿ + (2-2i)·z₁ⁿ + (2+2i)·z̄₁ⁿ) / n`,  `z₁ = (1+i)/2`.

Summing the four geometric-log series:

  `∑ w n = 2 log(1-x) + 2 log(1+x) - (2-2i) log(1-z₁) - (2+2i) log(1-z̄₁)`
        `= -2 log 2 + (2 log 2 + π) = π`,

using `log((1∓i)/2) = -½ log 2 ∓ (π/4)i`.  Grouping `ℕ ≃ ℕ × Fin 8`
(`Nat.divModEquiv`) and summing each fiber of eight terms reproduces
`bbpTerm j` exactly (the r = 0,2,3,7 numerators vanish identically), and
`Complex.hasSum_ofReal` lands the real statement.
-/

namespace NormalNumbers

namespace PiBBPProof

open Complex Real

/-- The real point of the filter: `x = 1/√2`. -/
noncomputable def x : ℝ := (Real.sqrt 2)⁻¹

/-- The complex point of the filter: `z₁ = (1+i)/2 = x·e^{iπ/4}`. -/
noncomputable def z1 : ℂ := (1 + I) / 2

/-- The conjugate point: `z̄₁ = (1-i)/2 = x·e^{-iπ/4}`. -/
noncomputable def z2 : ℂ := (1 - I) / 2

/-- The combined filtered series whose sum is π and whose mod-8 fiber sums
are the BBP terms. -/
noncomputable def w (n : ℕ) : ℂ :=
  ((-2) * (x : ℂ) ^ n + (-2) * (-(x : ℂ)) ^ n
    + (2 - 2 * I) * z1 ^ n + (2 + 2 * I) * z2 ^ n) / n

/-! ### Elementary facts about the points -/

lemma sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma x_pos : (0 : ℝ) < x := inv_pos.mpr sqrt2_pos

lemma x_sq : x ^ 2 = 2⁻¹ := by
  rw [x, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma x_lt_one : x < 1 := by
  nlinarith [x_sq, x_pos]

lemma cx_sq : ((x : ℝ) : ℂ) ^ 2 = 2⁻¹ := by
  rw [← Complex.ofReal_pow, x_sq]
  norm_num

lemma z1_sq : z1 ^ 2 = I / 2 := by
  rw [z1]
  field_simp
  ring_nf
  simp [Complex.I_sq]

lemma z2_sq : z2 ^ 2 = -I / 2 := by
  rw [z2]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma z1_pow8 : z1 ^ 8 = 16⁻¹ := by
  have : z1 ^ 8 = (z1 ^ 2) ^ 4 := by ring
  rw [this, z1_sq]
  field_simp
  norm_num [show (I/2)^4 = I^4/16 by ring, Complex.I_pow_four]

lemma z2_pow8 : z2 ^ 8 = 16⁻¹ := by
  have : z2 ^ 8 = (z2 ^ 2) ^ 4 := by ring
  rw [this, z2_sq]
  field_simp
  norm_num [show (-I/2)^4 = I^4/16 by ring, Complex.I_pow_four]

lemma cx_pow8 : ((x : ℝ) : ℂ) ^ 8 = 16⁻¹ := by
  have : ((x : ℝ) : ℂ) ^ 8 = (((x : ℝ) : ℂ) ^ 2) ^ 4 := by ring
  rw [this, cx_sq]
  norm_num

/-! ### Norm bounds: all four points are in the open unit disk -/

lemma norm_cx_lt : ‖((x : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos x_pos]
  exact x_lt_one

lemma norm_neg_cx_lt : ‖(-((x : ℝ) : ℂ))‖ < 1 := by
  rw [norm_neg]; exact norm_cx_lt

lemma norm_z1_lt : ‖z1‖ < 1 := by
  have h : ‖z1‖ ^ 2 < 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [z1]
    simp
    norm_num [Complex.normSq_apply]
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h

lemma norm_z2_lt : ‖z2‖ < 1 := by
  have h : ‖z2‖ ^ 2 < 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [z2]
    simp
    norm_num [Complex.normSq_apply]
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h

lemma neg_cx_pow8 : (-((x : ℝ) : ℂ)) ^ 8 = 16⁻¹ := by
  rw [show (-((x:ℝ):ℂ)) ^ 8 = ((x:ℝ):ℂ) ^ 8 by ring, cx_pow8]

/-! ### The four logs -/

/-- `exp(-½ log 2) = 1/√2` (real). -/
lemma exp_neg_half_log_two : Real.exp (-(Real.log 2 / 2)) = x := by
  have h2 : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [sq, ← Real.exp_add]
    rw [show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring]
    exact Real.exp_log (by norm_num)
  have h : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    conv_rhs => rw [← h2]
    rw [Real.sqrt_sq (Real.exp_pos _).le]
  rw [Real.exp_neg, h, x]

lemma sqrt2C_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma sqrt2C_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h2 := sqrt2C_sq
  rw [h] at h2
  norm_num at h2

/-- The exponential landing on `z̄₁ = (1-i)/2 = 1 - z₁`. -/
lemma exp_eq_z2 :
    Complex.exp (((-(Real.log 2 / 2)) : ℝ) + ((-(π / 4)) : ℝ) * I) = z2 := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, exp_neg_half_log_two,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
    x, z2]
  push_cast
  field_simp
  ring

/-- The exponential landing on `z₁ = (1+i)/2 = 1 - z̄₁`. -/
lemma exp_eq_z1 :
    Complex.exp (((-(Real.log 2 / 2)) : ℝ) + ((π / 4) : ℝ) * I) = z1 := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, exp_neg_half_log_two,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four, x, z1]
  push_cast
  field_simp

/-- `log(1 - z₁) = -½ log 2 - (π/4) i`. -/
lemma log_one_sub_z1 :
    Complex.log (1 - z1) = ((-(Real.log 2 / 2)) : ℝ) + ((-(π / 4)) : ℝ) * I := by
  have h1 : 1 - z1 = Complex.exp (((-(Real.log 2 / 2)) : ℝ) + ((-(π / 4)) : ℝ) * I) := by
    rw [exp_eq_z2, z1, z2]
    ring
  have him : ((((-(Real.log 2 / 2)) : ℝ) : ℂ) + (((-(π / 4)) : ℝ) : ℂ) * I).im
      = -(π / 4) := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    ring
  rw [h1, Complex.log_exp (by rw [him]; linarith [Real.pi_pos])
    (by rw [him]; linarith [Real.pi_pos])]

/-- `log(1 - z̄₁) = -½ log 2 + (π/4) i`. -/
lemma log_one_sub_z2 :
    Complex.log (1 - z2) = ((-(Real.log 2 / 2)) : ℝ) + ((π / 4) : ℝ) * I := by
  have h1 : 1 - z2 = Complex.exp (((-(Real.log 2 / 2)) : ℝ) + ((π / 4) : ℝ) * I) := by
    rw [exp_eq_z1, z1, z2]
    ring
  have him : ((((-(Real.log 2 / 2)) : ℝ) : ℂ) + (((π / 4) : ℝ)) * I).im
      = π / 4 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    ring
  rw [h1, Complex.log_exp (by rw [him]; linarith [Real.pi_pos])
    (by rw [him]; linarith [Real.pi_pos])]

/-- The two real logs combine: `log(1-x) + log(1+x) = -log 2`. -/
lemma log_one_sub_add_log_one_add :
    Real.log (1 - x) + Real.log (1 + x) = -Real.log 2 := by
  have hx1 := x_lt_one
  have hx0 := x_pos
  rw [← Real.log_mul (by nlinarith) (by nlinarith),
    show (1 - x) * (1 + x) = 1 - x ^ 2 by ring, x_sq,
    show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, Real.log_inv]

/-! ### The master sum -/

/-- **The filtered series sums to π.** -/
lemma hasSum_w : HasSum w ((π : ℝ) : ℂ) := by
  have h1 := (Complex.hasSum_taylorSeries_neg_log norm_cx_lt).mul_left (-2)
  have h2 := (Complex.hasSum_taylorSeries_neg_log norm_neg_cx_lt).mul_left (-2)
  have h3 := (Complex.hasSum_taylorSeries_neg_log norm_z1_lt).mul_left (2 - 2 * I)
  have h4 := (Complex.hasSum_taylorSeries_neg_log norm_z2_lt).mul_left (2 + 2 * I)
  have h := ((h1.add h2).add h3).add h4
  have hfun : (fun n : ℕ => -2 * (((x : ℝ) : ℂ) ^ n / n) + -2 * ((-((x : ℝ) : ℂ)) ^ n / n)
      + (2 - 2 * I) * (z1 ^ n / n) + (2 + 2 * I) * (z2 ^ n / n)) = w := by
    funext n
    rw [w]
    ring
  rw [hfun] at h
  have hr1 : Complex.log (1 - ((x : ℝ) : ℂ)) = ((Real.log (1 - x) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - ((x : ℝ) : ℂ) = (((1 - x : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by linarith [x_lt_one])]
  have hr2 : Complex.log (1 - (-((x : ℝ) : ℂ))) = ((Real.log (1 + x) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (-((x : ℝ) : ℂ)) = (((1 + x : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by linarith [x_pos])]
  rw [hr1, hr2, log_one_sub_z1, log_one_sub_z2] at h
  have hL : ((Real.log (1 - x) : ℝ) : ℂ) + ((Real.log (1 + x) : ℝ) : ℂ)
      = -((Real.log 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, log_one_sub_add_log_one_add]
    push_cast
    ring
  have hval : -2 * -((Real.log (1 - x) : ℝ) : ℂ) + -2 * -((Real.log (1 + x) : ℝ) : ℂ)
      + (2 - 2 * I) * -((((-(Real.log 2 / 2)) : ℝ) : ℂ) + (((-(π / 4)) : ℝ) : ℂ) * I)
      + (2 + 2 * I) * -((((-(Real.log 2 / 2)) : ℝ) : ℂ) + (((π / 4) : ℝ) : ℂ) * I)
      = ((π : ℝ) : ℂ) := by
    push_cast
    linear_combination (2 : ℂ) * hL - ((π : ℝ) : ℂ) * Complex.I_sq
  rwa [hval] at h

/-! ### Fiber sums: eight consecutive terms make one BBP term -/

/-- Power-block decomposition of `w` along `n = 8j + r`. -/
lemma w_block (j r : ℕ) :
    w (j * 8 + r) = ((16⁻¹ : ℂ) ^ j *
      ((-2) * ((x : ℝ) : ℂ) ^ r + (-2) * (-((x : ℝ) : ℂ)) ^ r
        + (2 - 2 * I) * z1 ^ r + (2 + 2 * I) * z2 ^ r)) / ((j * 8 + r : ℕ) : ℂ) := by
  rw [w, pow_add, pow_add, pow_add, pow_add, pow_mul', pow_mul', pow_mul', pow_mul',
    z1_pow8, z2_pow8, cx_pow8, neg_cx_pow8]
  ring

/-- Residue 0: the numerator vanishes identically (also killing `j = 0`
division by zero). -/
lemma w_r0 (j : ℕ) : w (j * 8 + 0) = 0 := by
  rw [w_block, z1, z2]
  ring

lemma w_r1 (j : ℕ) :
    w (j * 8 + 1) = 4 * (16⁻¹ : ℂ) ^ j / ((j * 8 + 1 : ℕ) : ℂ) := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 1 : ℕ) : ℂ) * (-2)) * Complex.I_sq

lemma w_r2 (j : ℕ) : w (j * 8 + 2) = 0 := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 2 : ℕ) : ℂ) * (-1)) * Complex.I_sq
    + ((16⁻¹ : ℂ) ^ j / ((j * 8 + 2 : ℕ) : ℂ) * (-4)) * cx_sq

lemma w_r3 (j : ℕ) : w (j * 8 + 3) = 0 := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 3 : ℕ) : ℂ) * ((1 - I ^ 2) / 2))
    * Complex.I_sq

lemma w_r4 (j : ℕ) :
    w (j * 8 + 4) = (-2) * (16⁻¹ : ℂ) ^ j / ((j * 8 + 4 : ℕ) : ℂ) := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 4 : ℕ) : ℂ) * ((5 - 3 * I ^ 2) / 4))
      * Complex.I_sq
    + ((16⁻¹ : ℂ) ^ j / ((j * 8 + 4 : ℕ) : ℂ) * (-4 * ((x : ℝ) : ℂ) ^ 2 - 2)) * cx_sq

lemma w_r5 (j : ℕ) :
    w (j * 8 + 5) = (-1) * (16⁻¹ : ℂ) ^ j / ((j * 8 + 5 : ℕ) : ℂ) := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 5 : ℕ) : ℂ)
    * ((9 - 4 * I ^ 2 - I ^ 4) / 8)) * Complex.I_sq

lemma w_r6 (j : ℕ) :
    w (j * 8 + 6) = (-1) * (16⁻¹ : ℂ) ^ j / ((j * 8 + 6 : ℕ) : ℂ) := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 6 : ℕ) : ℂ) * ((9 - 5 * I ^ 4) / 16))
      * Complex.I_sq
    + ((16⁻¹ : ℂ) ^ j / ((j * 8 + 6 : ℕ) : ℂ)
      * (-4 * ((x : ℝ) : ℂ) ^ 4 - 2 * ((x : ℝ) : ℂ) ^ 2 - 1)) * cx_sq

lemma w_r7 (j : ℕ) : w (j * 8 + 7) = 0 := by
  rw [w_block, z1, z2]
  linear_combination ((16⁻¹ : ℂ) ^ j / ((j * 8 + 7 : ℕ) : ℂ)
    * ((1 - I ^ 2) * (I ^ 4 + 14 * I ^ 2 + 1) / 32)) * Complex.I_sq

/-- **Fiber identity**: `∑_{r<8} w (8j + r) = bbpTerm j`. -/
lemma hasSum_fiber (j : ℕ) :
    HasSum (fun r : Fin 8 => w (j * 8 + (r : ℕ))) ((bbpTerm j : ℝ) : ℂ) := by
  have h := hasSum_fintype (fun r : Fin 8 => w (j * 8 + (r : ℕ)))
  have hsum : ∑ r : Fin 8, w (j * 8 + (r : ℕ)) = ((bbpTerm j : ℝ) : ℂ) := by
    rw [Fin.sum_univ_eight]
    simp only [show ((0 : Fin 8) : ℕ) = 0 from rfl, show ((1 : Fin 8) : ℕ) = 1 from rfl,
      show ((2 : Fin 8) : ℕ) = 2 from rfl, show ((3 : Fin 8) : ℕ) = 3 from rfl,
      show ((4 : Fin 8) : ℕ) = 4 from rfl, show ((5 : Fin 8) : ℕ) = 5 from rfl,
      show ((6 : Fin 8) : ℕ) = 6 from rfl, show ((7 : Fin 8) : ℕ) = 7 from rfl]
    rw [w_r0, w_r1, w_r2, w_r3, w_r4, w_r5, w_r6, w_r7]
    have hd1 : ((j * 8 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd4 : ((j * 8 + 4 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd5 : ((j * 8 + 5 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd6 : ((j * 8 + 6 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h16 : ((16 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [bbpTerm, bbpKick]
    push_cast at hd1 hd4 hd5 hd6 ⊢
    have hpow : ((1 : ℂ) / 16) ^ j * 16 ^ j = 1 := by
      rw [div_pow, one_pow, div_mul_cancel₀ _ h16]
    field_simp
    linear_combination (376 + (j : ℂ) * 1208 + (j : ℂ) ^ 2 * 960) * hpow
  rwa [hsum] at h

end PiBBPProof

open PiBBPProof in
/-- **Lane-2 discharge of the frozen node `PiBBP`** (BBP 1997):
the BBP series sums to π. -/
theorem piBBP_proved : PiBBP := by
  rw [PiBBP, ← Complex.hasSum_ofReal]
  have h : HasSum (w ∘ (Nat.divModEquiv 8).symm) ((Real.pi : ℝ) : ℂ) :=
    ((Nat.divModEquiv 8).symm.hasSum_iff).mpr hasSum_w
  exact HasSum.prod_fiberwise h hasSum_fiber

end NormalNumbers
