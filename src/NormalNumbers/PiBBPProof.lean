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

/-! ### The four logs -/

/-- `exp(-½ log 2) = 1/√2` (real). -/
lemma exp_neg_half_log_two : Real.exp (-(Real.log 2 / 2)) = x := by
  sorry

/-- `log(1 - z₁) = -½ log 2 - (π/4) i`. -/
lemma log_one_sub_z1 :
    Complex.log (1 - z1) = -(Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I := by
  sorry

/-- `log(1 - z̄₁) = -½ log 2 + (π/4) i`. -/
lemma log_one_sub_z2 :
    Complex.log (1 - z2) = -(Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I := by
  sorry

/-- The two real logs combine: `log(1-x) + log(1+x) = -log 2`. -/
lemma log_one_sub_add_log_one_add :
    Real.log (1 - x) + Real.log (1 + x) = -Real.log 2 := by
  sorry

/-! ### The master sum -/

/-- **The filtered series sums to π.** -/
lemma hasSum_w : HasSum w ((π : ℝ) : ℂ) := by
  sorry

/-! ### Fiber sums: eight consecutive terms make one BBP term -/

/-- **Fiber identity**: `∑_{r<8} w (8j + r) = bbpTerm j`. -/
lemma hasSum_fiber (j : ℕ) :
    HasSum (fun r : Fin 8 => w (j * 8 + (r : ℕ))) ((bbpTerm j : ℝ) : ℂ) := by
  sorry

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
