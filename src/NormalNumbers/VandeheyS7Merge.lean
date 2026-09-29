/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Birkhoff
import NormalNumbers.VandeheyS7Branch

/-!
# Loss of memory: a UNIFORM contraction factor per two input digits

`VandeheyS7Birkhoff` built the instrument (the Hilbert projective metric, the Birkhoff
coefficient `birkhoffCoeff`, and its analytic core `birkhoff_denom_bound`) but left the
hypothesis `0 < b`, `0 < c` unverified: a single Gauss branch `A_a = (0, 1; 1, a)` has a zero
corner, so ONE input digit never contracts.  This module supplies the missing step and, with it,
considerably more than was expected.

## The pair state

Two digits compose to

    A_a · A_b  =  (1, B; A, 1 + A B),      A = max 1 a,  B = max 1 b,

which is **strictly positive in all four entries** (`gaussPair_a_pos` … `gaussPair_d_pos`) with
determinant exactly `1` (`gaussPair_det`).  So the Birkhoff diameter is finite after two digits
no matter what the digits are, and no matter what state the machine was in — the contraction is a
property of the *input word*, not of the state, which is precisely what is needed over `ℤ[φ]`,
where the state set is infinite (`infinite_zPhi_abs_le_one`).

## The surprise: the factor is uniform, and the worst case is `a = b = 1`

With `ad = 1 + t` and `bc = t` for `t = A B ≥ 1`, the coefficient collapses to a closed form

    `birkhoffCoeff_one_add` :  birkhoffCoeff a b c d = (√(1+t) − √t)^2 ,

because rationalising the denominator leaves `(1+t) − t = 1`.  And `√(1+t) − √t = 1/(√(1+t)+√t)`
is DECREASING in `t`, so large digits contract *more*.  The worst case is therefore the smallest
possible product `t = 1`, i.e. `a = b = 1`, and

    `gaussPair_birkhoffCoeff_le` :  birkhoffCoeff (A_a A_b) ≤ 3 − 2√2 ≈ 0.1716

for **every** pair of digits.  There is no digit bound, no positive-frequency argument and no
large-deviation step: every two input digits contract the Hilbert metric by a fixed factor
`3 − 2√2 < 1`.  This is the loss of memory that replaces the finite-chain merging Vandehey cites
Saloff-Coste–Zúñiga for, and which `infinite_zPhi_abs_le_one` makes unavailable here.

Note what this does *not* say, and must not be misread as saying: it bounds the distance between
the images of two different starting states, never making them equal.  Pathwise merging stays
refuted (`conj_goldenRatio_integral_forces_diagonal`).

## Guard rule

Content locator: `birkhoffCoeff_one_add_one` — at `t = 1` the bound is attained, `3 − 2√2`, so
the constant is sharp and is not an artefact of slack in `birkhoff_denom_bound`.
Degenerate case: `birkhoffCoeff_single_gaussBranch` — a SINGLE branch has the zero corner `a = 0`,
so `a d = 0 < b c` and the coefficient is `-1`: modulus one, no contraction at all.  Two digits is
not a convenience; it is necessary.
-/

namespace NormalNumbers.VandeheyS7

open Real

namespace MobState

/-- Two Gauss branches composed: the two-digit state. -/
noncomputable def gaussPair (a b : ℕ) : MobState := (gaussBranch a).comp (gaussBranch b)

@[simp] theorem gaussPair_a (a b : ℕ) : (gaussPair a b).a = 1 := by
  simp [gaussPair, gaussBranch]

@[simp] theorem gaussPair_b (a b : ℕ) : (gaussPair a b).b = ((max 1 b : ℕ) : ℝ) := by
  simp [gaussPair, gaussBranch]

@[simp] theorem gaussPair_c (a b : ℕ) : (gaussPair a b).c = ((max 1 a : ℕ) : ℝ) := by
  simp [gaussPair, gaussBranch]

@[simp] theorem gaussPair_d (a b : ℕ) :
    (gaussPair a b).d = 1 + ((max 1 a : ℕ) : ℝ) * ((max 1 b : ℕ) : ℝ) := by
  simp [gaussPair, gaussBranch]

theorem gaussPair_a_pos (a b : ℕ) : 0 < (gaussPair a b).a := by simp

theorem gaussPair_b_pos (a b : ℕ) : 0 < (gaussPair a b).b := by
  rw [gaussPair_b]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 b)

theorem gaussPair_c_pos (a b : ℕ) : 0 < (gaussPair a b).c := by
  rw [gaussPair_c]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 a)

theorem gaussPair_d_pos (a b : ℕ) : 0 < (gaussPair a b).d := (gaussPair a b).hd

/-- The two-digit state has determinant exactly `1`. -/
theorem gaussPair_det (a b : ℕ) :
    (gaussPair a b).a * (gaussPair a b).d - (gaussPair a b).b * (gaussPair a b).c = 1 := by
  simp; ring

/-- Degenerate case: a SINGLE Gauss branch has the zero corner `a = 0`, so `a d = 0 < b c` and the
coefficient is `-1` — modulus one, no contraction at all.  The pair is not a convenience. -/
theorem birkhoffCoeff_single_gaussBranch (a : ℕ) :
    birkhoffCoeff (gaussBranch a).a (gaussBranch a).b (gaussBranch a).c (gaussBranch a).d
      = -1 := by
  have h1 : (1:ℝ) ≤ ((max 1 a : ℕ) : ℝ) := one_le_gaussBranch_d a
  have hbc : (gaussBranch a).b * (gaussBranch a).c = 1 := by simp [gaussBranch]
  have had : (gaussBranch a).a * (gaussBranch a).d = 0 := by simp [gaussBranch]
  rw [birkhoffCoeff, hbc, had]
  norm_num

end MobState

/-! ## The closed form, and the uniform bound -/

/-- **Closed form when the determinant is `1`.**  Rationalising the denominator of
`(√(1+t) − √t)/(√(1+t) + √t)` leaves `(1+t) − t = 1`. -/
theorem birkhoffCoeff_one_add {a b c d : ℝ} (hbc : 0 ≤ b * c) (h : a * d = 1 + b * c) :
    birkhoffCoeff a b c d = (Real.sqrt (a * d) - Real.sqrt (b * c)) ^ 2 := by
  have had : (0:ℝ) ≤ a * d := by rw [h]; linarith
  have hs : Real.sqrt (a * d) ^ 2 = a * d := Real.sq_sqrt had
  have ht : Real.sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt hbc
  have hsum : 0 < Real.sqrt (a * d) + Real.sqrt (b * c) := by
    have h1 : Real.sqrt (a * d) ^ 2 = 1 + b * c := by rw [hs, h]
    nlinarith [Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c)]
  rw [birkhoffCoeff, div_eq_iff hsum.ne']
  nlinarith [hs, ht, h]

/-- `√(1+t) − √t ≤ √2 − 1` for `t ≥ 1`: the difference is `1/(√(1+t)+√t)`, decreasing. -/
theorem sqrt_succ_sub_sqrt_le {t : ℝ} (ht : 1 ≤ t) :
    Real.sqrt (1 + t) - Real.sqrt t ≤ Real.sqrt 2 - 1 := by
  have h0 : (0:ℝ) ≤ t := by linarith
  have hs : Real.sqrt (1 + t) ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
  have hu : Real.sqrt t ^ 2 = t := Real.sq_sqrt h0
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1t : Real.sqrt 2 ≤ Real.sqrt (1 + t) := Real.sqrt_le_sqrt (by linarith)
  have h1u : (1:ℝ) ≤ Real.sqrt t := by
    have := Real.sqrt_le_sqrt ht
    simpa using this
  -- `(√(1+t) − √t)(√(1+t) + √t) = 1 = (√2 − 1)(√2 + 1)`
  have e1 : (Real.sqrt (1 + t) - Real.sqrt t) * (Real.sqrt (1 + t) + Real.sqrt t) = 1 := by
    nlinarith [hs, hu]
  have e2 : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by nlinarith [h2]
  have hv : Real.sqrt 2 + 1 ≤ Real.sqrt (1 + t) + Real.sqrt t := by linarith
  have hu0 : 0 ≤ Real.sqrt (1 + t) - Real.sqrt t := by
    have := Real.sqrt_le_sqrt (show t ≤ 1 + t by linarith)
    linarith
  have hpos : (0:ℝ) < Real.sqrt 2 + 1 := by linarith [Real.sqrt_nonneg (2:ℝ)]
  -- `u (√2+1) ≤ u v = 1 = (√2−1)(√2+1)`, then divide by `√2+1 > 0`
  have hmul : (Real.sqrt (1 + t) - Real.sqrt t) * (Real.sqrt 2 + 1)
      ≤ (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) := by
    have := mul_le_mul_of_nonneg_left hv hu0
    rw [e2]
    linarith [this, e1]
  exact le_of_mul_le_mul_right (by linarith [hmul]) hpos

/-- Content locator: at `t = 1` the bound is attained exactly, so `3 − 2√2` is sharp. -/
theorem birkhoffCoeff_one_add_one :
    birkhoffCoeff 2 1 1 1 = 3 - 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [birkhoffCoeff_one_add (by norm_num) (by norm_num)]
  norm_num
  nlinarith [h2]

namespace MobState

/-- **The uniform contraction factor.**  Every two input digits contract the Hilbert projective
metric by at least `3 − 2√2 < 1`, whatever the digits are and whatever state the machine is in. -/
theorem gaussPair_birkhoffCoeff_le (a b : ℕ) :
    birkhoffCoeff (gaussPair a b).a (gaussPair a b).b (gaussPair a b).c (gaussPair a b).d
      ≤ 3 - 2 * Real.sqrt 2 := by
  set A : ℝ := ((max 1 a : ℕ) : ℝ) with hA
  set B : ℝ := ((max 1 b : ℕ) : ℝ) with hB
  have hA1 : (1:ℝ) ≤ A := by rw [hA]; exact_mod_cast le_max_left 1 a
  have hB1 : (1:ℝ) ≤ B := by rw [hB]; exact_mod_cast le_max_left 1 b
  have hbc : (gaussPair a b).b * (gaussPair a b).c = B * A := by
    rw [gaussPair_b, gaussPair_c]
  have had : (gaussPair a b).a * (gaussPair a b).d = 1 + B * A := by
    rw [gaussPair_a, gaussPair_d]; ring
  have ht : (1:ℝ) ≤ B * A := by nlinarith
  rw [birkhoffCoeff_one_add (by rw [hbc]; nlinarith) (by rw [hbc, had])]
  rw [hbc, had]
  have hkey := sqrt_succ_sub_sqrt_le ht
  have hnn : 0 ≤ Real.sqrt (1 + B * A) - Real.sqrt (B * A) := by
    have := Real.sqrt_le_sqrt (show B * A ≤ 1 + B * A by linarith)
    linarith
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2l : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  nlinarith [hkey, hnn, h2]

/-- The contraction factor is a genuine one: `3 − 2√2 < 1`. -/
theorem three_sub_two_sqrt_two_lt_one : 3 - 2 * Real.sqrt 2 < 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2:ℝ), h2]

theorem three_sub_two_sqrt_two_nonneg : (0:ℝ) ≤ 3 - 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2:ℝ), h2]

end MobState

section Audit

#print axioms MobState.gaussPair_det
#print axioms birkhoffCoeff_one_add
#print axioms MobState.gaussPair_birkhoffCoeff_le

end Audit

end NormalNumbers.VandeheyS7
