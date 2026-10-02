/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7QuadDigit
import NormalNumbers.VandeheyS7Cell

/-!
# Leg 1 of the ergodic route, discharged: the image of a CF-normal number is irrational

`affineCFN_of_orbitCellBound_log` proves the frozen §7 target from three hypotheses: the cited
`GaussACRigidity`, the crux `OrbitCellBound`, and `AffineImageIrrational q r₀` — "the image of
every CF-normal input is irrational".  The third was the one leg that is not open mathematics,
only work.  This module discharges it for **both** frozen instances:

* `affineImageIrrational_goldenRatio : AffineImageIrrational φ 0`;
* `affineImageIrrational_add_goldenRatio : AffineImageIrrational 1 φ`.

## The argument

Suppose `φ·x` is rational, `= r`.  Put `z = Int.fract x` and `m = ⌊x⌋`, so `x = z + m` and
`r = φ (z + m)`.  Then

  `(z + m)² + r (z + m) − r² = (z+m)² (1 + φ − φ²) = 0`

because `φ² = φ + 1`.  Clearing the denominator of `r = p/q` turns this into an **integer**
quadratic `A z² + B z + C = 0` with `A = q² ≠ 0`.  `cfDigit_le_of_quadratic` then bounds every
partial quotient of `z` by `⌊2|A| + |B|⌋₊`, and `not_isCFNormal_of_bddDigits` contradicts the
CF-normality of `z`.  The additive case is the same computation with `z − s = −φ`, `s = r − m`.

Neither case needs Lagrange's theorem, an eventual periodicity statement, or any input beyond
`φ² = φ + 1`: the *only* property of `φ` used is that it is a root of a fixed integer quadratic,
so the proof is written once as `affineImageIrrational_of_quadratic_witness` and instantiated
twice.

## Guard rule

Content locator: `not_isCFNormal_of_rational_image` — all the content is "a CF-normal number
cannot satisfy an integer quadratic", and the two frozen instances are pure algebra on top of it.
Degenerate cases: `r = 0` needs no separate treatment (`A = q²` is nonzero whatever `r` is, and the
quadratic then says `z = −m`, which the irrationality of `z` already refutes); and
`not_affineImageIrrational_zero_of_exists` (in `VandeheyS7Orbit`) records that `q = 0` genuinely
fails, so the hypothesis is not vacuous.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-- **The content of this module.**  A CF-normal number of `(0,1)` is not a root of a nonzero
integer quadratic.  Everything else here is the algebra that produces the quadratic. -/
theorem not_isCFNormal_of_quadratic {A B C : ℤ} (hA : A ≠ 0) {z : ℝ} (hirr : Irrational z)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hroot : (A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ) = 0) :
    ¬ IsCFNormal z :=
  not_isCFNormal_of_bddDigits (M := ⌊2 * |(A:ℝ)| + |(B:ℝ)|⌋₊)
    (cfDigit_le_of_quadratic hA hirr hz hroot)

/-- The fractional part of a CF-normal number's argument is itself CF-normal, irrational and in
`(0,1)`: the three facts every instance below starts from. -/
theorem fract_data {x : ℝ} (hx : IsCFNormal (Int.fract x)) :
    Irrational (Int.fract x) ∧ Int.fract x ∈ Set.Ioo (0:ℝ) 1 := by
  have hirr : Irrational (Int.fract x) := by
    by_contra h
    exact Literature.not_isCFNormal_of_not_irrational h hx
  refine ⟨hirr, ?_, Int.fract_lt_one x⟩
  rcases lt_or_eq_of_le (Int.fract_nonneg x) with h | h
  · exact h
  · exact absurd ⟨0, by rw [← h]; norm_num⟩ hirr

/-- Extract a rational witness from a failure of irrationality. -/
theorem exists_rat_of_not_irrational {y : ℝ} (h : ¬ Irrational y) : ∃ r : ℚ, (r : ℝ) = y := by
  rw [Irrational, not_not] at h
  exact h

/-- `(r.num : ℝ) = r * r.den`. -/
theorem num_eq_mul_den (r : ℚ) : ((r.num : ℤ) : ℝ) = (r : ℝ) * ((r.den : ℤ) : ℝ) := by
  have hd : ((r.den : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  rw [Rat.cast_def]
  push_cast
  field_simp

/-- `q = r.den` is a nonzero integer, and so is `q²`. -/
theorem den_sq_ne_zero (r : ℚ) : ((r.den : ℤ)) ^ 2 ≠ 0 := by
  have : (0:ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
  positivity

/-! ## The multiplicative instance: `x ↦ φ x` -/

/-- **Leg 1 for `x ↦ φ·x`.**  If `φ x` were rational then `Int.fract x` would satisfy an integer
quadratic with leading coefficient `r.den²`, hence have bounded partial quotients, hence fail to be
CF-normal. -/
theorem affineImageIrrational_goldenRatio :
    AffineImageIrrational Real.goldenRatio 0 := by
  intro x hx
  rw [add_zero]
  by_contra hcon
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hcon
  obtain ⟨hirr, hmem⟩ := fract_data hx
  set z : ℝ := Int.fract x with hzdef
  set m : ℤ := ⌊x⌋ with hmdef
  set p : ℤ := r.num with hpdef
  set q : ℤ := (r.den : ℤ) with hqdef
  have hx_eq : x = z + (m : ℝ) := by
    rw [hzdef, hmdef]; exact (Int.fract_add_floor x).symm
  have hgold : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hR : (r : ℝ) = Real.goldenRatio * (z + (m : ℝ)) := by rw [hr, ← hx_eq]
  have key : (z + (m:ℝ)) ^ 2 + (r:ℝ) * (z + (m:ℝ)) - (r:ℝ) ^ 2 = 0 := by
    rw [hR]; linear_combination (-((z : ℝ) + (m : ℝ)) ^ 2) * hgold
  have hp : ((p : ℤ) : ℝ) = (r : ℝ) * ((q : ℤ) : ℝ) := by
    rw [hpdef, hqdef]; exact num_eq_mul_den r
  have hroot : ((q ^ 2 : ℤ) : ℝ) * z ^ 2 + ((q * (p + 2 * m * q) : ℤ) : ℝ) * z
      + (((p + m * q) ^ 2 - p * (p + m * q) - p ^ 2 : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination ((q:ℝ)) ^ 2 * key
      + ((q:ℝ) * z + (m:ℝ) * (q:ℝ) - (p:ℝ) - (q:ℝ) * (r:ℝ)) * hp
  exact not_isCFNormal_of_quadratic (den_sq_ne_zero r) hirr hmem hroot hx

/-! ## The additive instance: `x ↦ x + φ` -/

/-- **Leg 1 for `x ↦ x + φ`.**  If `x + φ` were rational, `z = Int.fract x` would satisfy
`z² + (1 − 2s) z + (s² − s − 1) = 0` with `s = r − m`, again an integer quadratic after clearing
`r.den`. -/
theorem affineImageIrrational_add_goldenRatio :
    AffineImageIrrational 1 Real.goldenRatio := by
  intro x hx
  rw [one_mul]
  by_contra hcon
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hcon
  obtain ⟨hirr, hmem⟩ := fract_data hx
  set z : ℝ := Int.fract x with hzdef
  set m : ℤ := ⌊x⌋ with hmdef
  set p : ℤ := r.num with hpdef
  set q : ℤ := (r.den : ℤ) with hqdef
  have hx_eq : x = z + (m : ℝ) := by
    rw [hzdef, hmdef]; exact (Int.fract_add_floor x).symm
  have hgold : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hphi : Real.goldenRatio = (r : ℝ) - (m : ℝ) - z := by
    rw [hx_eq] at hr; linarith
  have key : z ^ 2 + (1 - 2 * ((r:ℝ) - (m:ℝ))) * z
      + (((r:ℝ) - (m:ℝ)) ^ 2 - ((r:ℝ) - (m:ℝ)) - 1) = 0 := by
    rw [hphi] at hgold; linear_combination hgold
  have hp : ((p : ℤ) : ℝ) = (r : ℝ) * ((q : ℤ) : ℝ) := by
    rw [hpdef, hqdef]; exact num_eq_mul_den r
  have hroot : ((q ^ 2 : ℤ) : ℝ) * z ^ 2 + ((q * (q - 2 * (p - m * q)) : ℤ) : ℝ) * z
      + (((p - m * q) ^ 2 - q * (p - m * q) - q ^ 2 : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination ((q:ℝ)) ^ 2 * key
      + (-(q:ℝ) * 2 * z + (q:ℝ) * ((r:ℝ) - (m:ℝ)) + (p:ℝ) - (m:ℝ) * (q:ℝ) - (q:ℝ)) * hp
  exact not_isCFNormal_of_quadratic (den_sq_ne_zero r) hirr hmem hroot hx

/-! ## The frozen targets, one hypothesis lighter -/

/-- **`x ↦ φ·x`, on the ergodic route, with leg 1 discharged.**  Two hypotheses remain: the cited
`GaussACRigidity` and the crux `OrbitCellBound`. -/
theorem vandeheyS7_mul_phi_of_orbitCellBound {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (hcell : OrbitCellBound Real.goldenRatio 0 C) : vandeheyS7_mul_phi :=
  affineCFN_of_orbitCellBound_log hC affineImageIrrational_goldenRatio hrig hcell

/-- **`x ↦ x + φ`, likewise.** -/
theorem vandeheyS7_add_phi_of_orbitCellBound {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (hcell : OrbitCellBound 1 Real.goldenRatio C) : vandeheyS7_add_phi :=
  affineCFN_of_orbitCellBound_log hC affineImageIrrational_add_goldenRatio hrig hcell

/-! ## Guard rule -/

/-- Content locator: strip the affine map away and the module says exactly this. -/
theorem not_isCFNormal_of_rational_image {A B C : ℤ} (hA : A ≠ 0) {z : ℝ}
    (hirr : Irrational z) (hz : z ∈ Set.Ioo (0:ℝ) 1)
    (hroot : (A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ) = 0) : ¬ IsCFNormal z :=
  not_isCFNormal_of_quadratic hA hirr hz hroot

section Audit

#print axioms not_isCFNormal_of_quadratic
#print axioms fract_data
#print axioms num_eq_mul_den
#print axioms affineImageIrrational_goldenRatio
#print axioms affineImageIrrational_add_goldenRatio
#print axioms vandeheyS7_mul_phi_of_orbitCellBound
#print axioms vandeheyS7_add_phi_of_orbitCellBound

end Audit

end NormalNumbers.VandeheyS7
