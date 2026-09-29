/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Fix
import NormalNumbers.VandeheyS7Lattice

/-!
# S7-W2: the width is an arithmetic quantity

Lap 71 showed the width floor cannot be bought from the image (the bootstrap has coefficient `3`),
and named the non-looping alternative: the width is a *height* quantity of the state as a lattice
point.  This module proves that, and the `ℤ[φ]` consequence.

## The identity

* `width_eq` — `width s = |ad − bc| / ((c+d)·d)`, exactly.  Equivalently
  `width_eq_det_div` — `width s = |ad − bc| / (distortion s · d²)`, since `distortion = (c+d)/d`.

So a width floor `width ≥ η` is precisely **an upper bound on the state's denominator entries**,
measured against the determinant.  It is a height statement, not a dynamical one.

## The arithmetic floor

For the additive instance the state has entries in `ℤ[φ]`, so `det = ad − bc` is a nonzero element
of `ℤ[φ]` and `|det| ≥ 1/|det′|` by Galois repulsion (`abs_zval_ge_inv_abs_zconj`, lap 58).  Hence

* `width_ge_of_zdet` — `width s ≥ 1 / (|det′| · distortion s · d²)`.

**This is a width floor with no ergodic input at all.**  What it costs is a bound on the conjugate
`|det′|` and on the denominator entry `d`, i.e. exactly a height bound on the state in
`SL₂(ℤ[φ])` — the object lap 58 identified.  The route's tail obligation is therefore reduced to a
lattice-height statement, which is the shape directive fact (γ) asks for and which, unlike the
bootstrap, does not refer to the image orbit.

## Guard rule

Content locator: `width_eq` is an identity, so nothing is lost there; all the content of
`width_ge_of_zdet` is the reciprocal `1/|det′|`, which is where integrality of `ℤ[φ]` enters and
which is false over `ℚ(φ)`.  Degenerate case: a state with `det` a *unit* of `ℤ[φ]` (e.g. `det =
±1`, the `SL₂` case) has `|det| = 1` and the floor is simply `1/(distortion · d²)`.
-/

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- **The width identity.** -/
theorem width_eq (s : MobState) :
    s.width = |s.a * s.d - s.b * s.c| / ((s.c + s.d) * s.d) := by
  have hd : 0 < s.d := s.hd
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  rw [width, mob, mob]
  have h1 : s.a * 1 + s.b = s.a + s.b := by ring
  have h2 : s.c * 1 + s.d = s.c + s.d := by ring
  have h3 : s.a * 0 + s.b = s.b := by ring
  have h4 : s.c * 0 + s.d = s.d := by ring
  rw [h1, h2, h3, h4]
  rw [div_sub_div _ _ hcd.ne' hd.ne', abs_div, abs_of_pos (mul_pos hcd hd)]
  congr 1
  congr 1
  ring

/-- The same, against the distortion: `width = |det| / (distortion · d²)`. -/
theorem width_eq_det_div (s : MobState) :
    s.width = |s.a * s.d - s.b * s.c| / (s.distortion * s.d ^ 2) := by
  have hd : 0 < s.d := s.hd
  rw [width_eq, distortion]
  congr 1
  field_simp
  try ring

/-- **A width floor is a height bound.**  Given a lower bound on the determinant and an upper
bound on `distortion · d²`, the width is bounded below. -/
theorem width_ge_of_height (s : MobState) {D₀ H : ℝ} (hD₀ : 0 ≤ D₀)
    (hdet : D₀ ≤ |s.a * s.d - s.b * s.c|) (hH : 0 < H) (hHle : s.distortion * s.d ^ 2 ≤ H) :
    D₀ / H ≤ s.width := by
  have hd : 0 < s.d := s.hd
  have hdist : 0 < s.distortion := s.distortion_pos
  have hpos : 0 < s.distortion * s.d ^ 2 := by positivity
  rw [width_eq_det_div]
  rw [div_le_div_iff₀ hH hpos]
  nlinarith [hdet, hHle, hD₀, hpos]

/-- **The arithmetic width floor.**  If the determinant is the `ℤ[φ]`-number `m₁ + m₂φ` (the
additive instance), Galois repulsion gives a floor with no ergodic input:
`width ≥ 1 / (|m₁ + m₂ψ| · distortion · d²)`. -/
theorem width_ge_of_zdet (s : MobState) {m₁ m₂ : ℤ} (hm : ¬ (m₁ = 0 ∧ m₂ = 0))
    (hdet : s.a * s.d - s.b * s.c = zval m₁ m₂) :
    1 / (|zconj m₁ m₂| * (s.distortion * s.d ^ 2)) ≤ s.width := by
  have hd : 0 < s.d := s.hd
  have hdist : 0 < s.distortion := s.distortion_pos
  have hpos : 0 < s.distortion * s.d ^ 2 := by positivity
  have hcpos : 0 < |zconj m₁ m₂| := abs_pos.2 (zconj_ne_zero hm)
  have hrep : 1 / |zconj m₁ m₂| ≤ |zval m₁ m₂| := abs_zval_ge_inv_abs_zconj hm
  rw [width_eq_det_div, hdet]
  rw [div_le_div_iff₀ (by positivity) hpos]
  have h1 : 1 / |zconj m₁ m₂| * (s.distortion * s.d ^ 2)
      ≤ |zval m₁ m₂| * (s.distortion * s.d ^ 2) := by
    exact mul_le_mul_of_nonneg_right hrep hpos.le
  calc (1:ℝ) * (s.distortion * s.d ^ 2)
      = (1 / |zconj m₁ m₂| * (s.distortion * s.d ^ 2)) * |zconj m₁ m₂| := by
        field_simp
    _ ≤ (|zval m₁ m₂| * (s.distortion * s.d ^ 2)) * |zconj m₁ m₂| := by
        exact mul_le_mul_of_nonneg_right h1 hcpos.le
    _ = |zval m₁ m₂| * (|zconj m₁ m₂| * (s.distortion * s.d ^ 2)) := by ring

end MobState

section Audit

#print axioms MobState.width_eq
#print axioms MobState.width_eq_det_div
#print axioms MobState.width_ge_of_height
#print axioms MobState.width_ge_of_zdet

end Audit

end NormalNumbers.VandeheyS7
