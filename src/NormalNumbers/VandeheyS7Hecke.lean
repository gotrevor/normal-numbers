/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Cell

/-!
# The Hecke-approximation route to §7, and why it cannot work

The repo *owns* Vandehey 2017 Theorem 1.1 (`Literature.vandehey_matrix_action_holds`): the image
of a CF-normal number under any `GL₂(ℚ)` Möbius map is CF-normal.  The most natural way to try to
carry that to `φ` is to approximate: `F_{k+1}/F_k → φ`, each `r_k x` is CF-normal by Theorem 1.1,
`r_k x → φ x`, and two nearby reals share a long CF prefix — so take a diagonal limit.

This module closes that route with a theorem, not a hand-wave.  The obstruction is that `φ` is the
**worst-approximable** real number, so buying agreement depth costs *exponentially* in the
determinant of the matrix Theorem 1.1 must be applied to.

## The accounting

* `abs_sub_mul_goldenRatio_ge` — `|p − qφ| ≥ 1/(4q)` for every `q ≥ 1`, from
  `(p − qφ)(p − qψ) = p² − pq − q²`, a nonzero integer.  No Lagrange, no CF of `φ`.
* `den_sq_gt_of_image_approx` — hence `|(p/q)x − φx| < δ` forces `q² > |x|/(4δ)`.
* `pow_lt_den_sq_of_image_approx` — in the form the route needs: agreement of the two images to
  within `|x|/(4cᴺ)` forces `q² > cᴺ`.  CF agreement to depth `N` needs exactly an error of that
  shape (`c = φ²` is the Lévy scale), so the denominator, and with it the determinant
  `det diag(p,q) = pq ≥ q²` (`sq_le_det_of_approx`), is **exponential in the depth bought**.

An automaton with `e^{Ω(N)}` states, run for `N` steps, has not even visited its state space, so
Theorem 1.1's equidistribution — which is an asymptotic statement about that automaton — says
nothing about the first `N` digits.  The diagonal limit therefore has no content.  Maze row:
`hall_hecke_approximation`.

## Guard rule

Content locator: `abs_sub_mul_goldenRatio_ge` is sharp in shape — `goldenNorm_factor` shows the
whole content is the norm form of `ℤ[φ]`, and `one_le_abs_goldenNorm` is where the integrality
enters; for a rational target the norm form vanishes and the bound is false, which is exactly why
Theorem 1.1 works and this does not.  Degenerate cases: `q = 0` is excluded (`goldenNorm_ne_zero`
needs `(p,q) ≠ (0,0)`), `N = 0` makes `pow_lt_den_sq_of_image_approx` say `1 < q²`, i.e. `q ≥ 2`,
which is the true content at depth zero, and `x = 0` is excluded since then both images agree
identically.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-! ## The norm form of `ℤ[φ]` -/

/-- `(p − qφ)(p − qψ) = p² − pq − q²`: the norm form, from `φ + ψ = 1` and `φψ = −1`. -/
theorem goldenNorm_factor (p q : ℤ) :
    ((p : ℝ) - q * Real.goldenRatio) * ((p : ℝ) - q * Real.goldenConj)
      = ((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ) := by
  have hsum : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
  have hmul : Real.goldenRatio * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
  push_cast
  linear_combination (-(p : ℝ) * (q : ℝ)) * hsum + ((q : ℝ) ^ 2) * hmul

/-- The norm form vanishes only at the origin: otherwise `φ` or `ψ` would be rational. -/
theorem goldenNorm_ne_zero {p q : ℤ} (h : ¬ (p = 0 ∧ q = 0)) : p ^ 2 - p * q - q ^ 2 ≠ 0 := by
  intro hz
  rcases eq_or_ne q 0 with hq | hq
  · subst hq
    have hp2 : p ^ 2 = 0 := by linarith
    exact h ⟨sq_eq_zero_iff.mp hp2, rfl⟩
  · have hq0 : ((q : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hq
    have hfac : ((p : ℝ) - q * Real.goldenRatio) * ((p : ℝ) - q * Real.goldenConj) = 0 := by
      rw [goldenNorm_factor, hz]; simp
    rcases mul_eq_zero.1 hfac with h1 | h1
    · refine Real.goldenRatio_irrational ⟨(p : ℚ) / (q : ℚ), ?_⟩
      have hpe : (p : ℝ) = (q : ℝ) * Real.goldenRatio := by linarith
      push_cast
      rw [div_eq_iff hq0, hpe]; ring
    · refine Real.goldenConj_irrational ⟨(p : ℚ) / (q : ℚ), ?_⟩
      have hpe : (p : ℝ) = (q : ℝ) * Real.goldenConj := by linarith
      push_cast
      rw [div_eq_iff hq0, hpe]; ring

/-- Integrality: the norm form is at least `1` in absolute value away from the origin. -/
theorem one_le_abs_goldenNorm {p q : ℤ} (h : ¬ (p = 0 ∧ q = 0)) :
    (1 : ℝ) ≤ |((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ)| := by
  have h1 : (1 : ℤ) ≤ |p ^ 2 - p * q - q ^ 2| := Int.one_le_abs (goldenNorm_ne_zero h)
  rw [← Int.cast_abs]
  exact_mod_cast h1

/-! ## `φ` is badly approximable, explicitly -/

theorem sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

/-- **`φ` is badly approximable, with an explicit constant.**  `|p − qφ| ≥ 1/(4q)` for every
integer `p` and every `q ≥ 1`.  This is the whole obstruction to the Hecke route. -/
theorem abs_sub_mul_goldenRatio_ge {p q : ℤ} (hq : 0 < q) :
    1 / (4 * (q : ℝ)) ≤ |(p : ℝ) - q * Real.goldenRatio| := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hne : ¬ (p = 0 ∧ q = 0) := by rintro ⟨-, rfl⟩; exact absurd hq (by norm_num)
  have hAB : 1 ≤ |(p : ℝ) - q * Real.goldenRatio| * |(p : ℝ) - q * Real.goldenConj| := by
    rw [← abs_mul, goldenNorm_factor]
    exact one_le_abs_goldenNorm hne
  have hApos : 0 ≤ |(p : ℝ) - q * Real.goldenRatio| := abs_nonneg _
  rcases le_or_gt 1 |(p : ℝ) - q * Real.goldenRatio| with hA1 | hA1
  · have : 1 / (4 * (q : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  · have hBle : |(p : ℝ) - q * Real.goldenConj|
        ≤ |(p : ℝ) - q * Real.goldenRatio| + (q : ℝ) * Real.sqrt 5 := by
      have hsplit : (p : ℝ) - q * Real.goldenConj
          = ((p : ℝ) - q * Real.goldenRatio)
            + (q : ℝ) * (Real.goldenRatio - Real.goldenConj) := by ring
      rw [hsplit, Real.goldenRatio_sub_goldenConj]
      calc |((p : ℝ) - q * Real.goldenRatio) + (q : ℝ) * Real.sqrt 5|
          ≤ |(p : ℝ) - q * Real.goldenRatio| + |(q : ℝ) * Real.sqrt 5| := abs_add_le _ _
        _ = |(p : ℝ) - q * Real.goldenRatio| + (q : ℝ) * Real.sqrt 5 := by
            rw [abs_of_nonneg (show (0:ℝ) ≤ (q : ℝ) * Real.sqrt 5 by positivity)]
    have hB4 : |(p : ℝ) - q * Real.goldenConj| ≤ 4 * (q : ℝ) := by
      nlinarith [sqrt_five_lt_three, Real.sqrt_nonneg 5]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (q : ℝ))]
    nlinarith

/-! ## The accounting for the route -/

/-- `|p − qφ| = q · |p/q − φ|`. -/
theorem abs_sub_eq_mul {p q : ℤ} (hq : 0 < q) :
    |(p : ℝ) - q * Real.goldenRatio| = (q : ℝ) * |(p : ℝ) / q - Real.goldenRatio| := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [← abs_of_pos hqpos, ← abs_mul, abs_of_pos hqpos]
  congr 1
  field_simp

/-- A rational within `δ` of `φ` has `q² > 1/(4δ)`. -/
theorem den_sq_gt_of_approx {p q : ℤ} (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ)
    (h : |(p : ℝ) / q - Real.goldenRatio| < δ) : 1 / (4 * δ) < (q : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hb := abs_sub_mul_goldenRatio_ge (p := p) (q := q) hq
  rw [abs_sub_eq_mul hq] at hb
  have hlt : 1 / (4 * (q : ℝ)) < (q : ℝ) * δ := by
    calc 1 / (4 * (q : ℝ)) ≤ (q : ℝ) * |(p : ℝ) / q - Real.goldenRatio| := hb
      _ < (q : ℝ) * δ := mul_lt_mul_of_pos_left h hqpos
  rw [div_lt_iff₀ (by positivity)] at hlt ⊢
  nlinarith

/-- **The accounting, on the images.**  If the two images `(p/q)·x` and `φ·x` are within `δ`
(`x ≠ 0`), then the denominator already satisfies `q² > |x|/(4δ)`. -/
theorem den_sq_gt_of_image_approx {p q : ℤ} (hq : 0 < q) {x δ : ℝ} (hx : x ≠ 0) (hδ : 0 < δ)
    (h : |((p : ℝ) / q) * x - Real.goldenRatio * x| < δ) : |x| / (4 * δ) < (q : ℝ) ^ 2 := by
  have hxpos : 0 < |x| := abs_pos.2 hx
  have hsplit : ((p : ℝ) / q) * x - Real.goldenRatio * x
      = ((p : ℝ) / q - Real.goldenRatio) * x := by ring
  rw [hsplit, abs_mul] at h
  have hq' : |(p : ℝ) / q - Real.goldenRatio| < δ / |x| := by
    rw [lt_div_iff₀ hxpos]; exact h
  have := den_sq_gt_of_approx hq (by positivity) hq'
  calc |x| / (4 * δ) = 1 / (4 * (δ / |x|)) := by field_simp
    _ < (q : ℝ) ^ 2 := this

/-- **The route's cost, in the shape it needs.**  Buying agreement of the two images to within
`|x|/(4cᴺ)` — the error budget for `N` CF digits at scale `c` — forces `q² > cᴺ`. -/
theorem pow_lt_den_sq_of_image_approx {p q : ℤ} (hq : 0 < q) {x c : ℝ} (hx : x ≠ 0)
    (hc : 0 < c) (N : ℕ)
    (h : |((p : ℝ) / q) * x - Real.goldenRatio * x| < |x| / (4 * c ^ N)) :
    c ^ N < (q : ℝ) ^ 2 := by
  have hxpos : 0 < |x| := abs_pos.2 hx
  have hcN : (0 : ℝ) < c ^ N := by positivity
  have hδ : (0 : ℝ) < |x| / (4 * c ^ N) := by positivity
  have hmain := den_sq_gt_of_image_approx hq hx hδ h
  have hrw : |x| / (4 * (|x| / (4 * c ^ N))) = c ^ N := by field_simp
  rwa [hrw] at hmain

/-- Once the approximation is any good at all, `q ≤ p`, so the determinant of the integer matrix
`diag(p,q)` realizing `t ↦ (p/q) t` is at least `q²`. -/
theorem sq_le_det_of_approx {p q : ℤ} (hq : 0 < q)
    (h : |(p : ℝ) / q - Real.goldenRatio| < 1 / 2) : q ^ 2 ≤ p * q := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hgold : (3 : ℝ) / 2 < Real.goldenRatio := by
    rw [Real.goldenRatio]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have habs := abs_lt.1 h
  have hgt : (1 : ℝ) < (p : ℝ) / q := by linarith [habs.1]
  have hqp : (q : ℝ) < (p : ℝ) := by
    rw [lt_div_iff₀ hqpos] at hgt; linarith
  have : q ≤ p := by exact_mod_cast hqp.le
  nlinarith [hq, this]

section Audit

#print axioms goldenNorm_factor
#print axioms goldenNorm_ne_zero
#print axioms one_le_abs_goldenNorm
#print axioms abs_sub_mul_goldenRatio_ge
#print axioms den_sq_gt_of_approx
#print axioms den_sq_gt_of_image_approx
#print axioms pow_lt_den_sq_of_image_approx
#print axioms sq_le_det_of_approx

end Audit

end NormalNumbers.VandeheyS7
