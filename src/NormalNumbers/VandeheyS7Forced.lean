/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Pull
import NormalNumbers.VandeheyS7Boundary

/-!
# S7-FB: a forced block reads the state's BASEPOINT, and it prices the state's width

Lap 74's `VandeheyS7Pull` closed the measure side of the crux: a state of width `≥ η` and
distortion `≤ K` pulls any target — and any *tower* `G^{-j} I_w` — back to Gauss mass
`≤ (2K/η)·γ(I_w)`.  This module says where that instrument *cannot* reach, exactly, and why.

## Forced emission

The transducer emits a digit only when the WHOLE image interval lies in one cylinder.  So while
the input point is frozen the emitted digits do not depend on the input point at all: they are the
CF digits shared by every point of the image.  Two theorems make that precise.

* `MobState.cfDigit_image_eq_basepoint` — every image point agrees with the **basepoint**
  `s.mob 0` in its first `m` digits, as soon as `width · distortion` is below the scale at which
  the basepoint's orbit stays off the cylinder boundaries.  `contract_le` (lap 74) pins the whole
  image to the basepoint; `cfDigit_agree_depth` (lap 24) carries that up the orbit.
  **So a forced block is a chunk of the CF expansion of `s.mob 0`.**  For the §7 states
  `s = O_t⁻¹ Φ P_n` the basepoint is `O_t⁻¹ Φ (p/q)` — a `GL₂(ℤ)`-image of `φ·(rational)`, hence
  by Serret CF-tail-equivalent to `φ p/q`.  That is the arithmetic of `Φ`, in the place where the
  route needs it.

* `MobState.preimage_cfCylinder_eq_of_forced` — the pullback of `I_w` is then **all or nothing**:
  it is the whole of `(0,1)`, or empty.

## The price

`MobState.width_le_of_forced`: if the state forces the word `w`, then

    width ≤ 2 · distortion · γ(I_w).

Equivalently (`one_le_pullbackConstant_of_forced`) the pullback constant `2·distortion/width` of
`gaussMeasure_preimage_le` is at least `1/γ(I_w)`, so on a forced block that bound says only
`≤ 1` — the trivial bound.  **This is the exact content locator for the crux**: measure alone
cannot see a forced block, and the constant degenerates at precisely the rate `1/γ(I_w)`.  The
crux's remaining content therefore lives entirely in the *distribution of the basepoints*
`O_t⁻¹ Φ (p_n/q_n)`, not in any pullback estimate.

It also explains lap 30's fact (β) quantitatively and closes the question the lap-74 review
raised about `StateClock`: long forced blocks and a width floor are mutually exclusive.

## Guard rule

Content locator: at `w = []` the price reads `width ≤ 2·distortion`, which is the trivial
statement (`γ(I_[]) = 1`), so all the content is in the decay of `γ(I_w)` with `w`.
Degenerate cases: a state forcing a single digit `a` has `width ≤ 2·distortion·γ(I_[a])`, i.e.
emitting a large digit costs width `≍ a⁻²`, which is the burst; and `hforced` at
`w.length = 0` is vacuous, matching the locator.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

namespace MobState

/-- The whole image is pinned to the basepoint at scale `width · distortion`. -/
theorem abs_mob_sub_basepoint_le (s : MobState) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    |s.mob 0 - s.mob t| ≤ s.width * s.distortion := by
  have h := s.contract_le (le_refl (0:ℝ)) (by norm_num) ht.1.le ht.2.le
  have habs : |(0:ℝ) - t| ≤ 1 := by
    rw [zero_sub, abs_neg, abs_of_pos ht.1]
    exact ht.2.le
  have hc : 0 ≤ s.width * s.distortion := by
    have := s.width_pos; have := s.distortion_pos; positivity
  calc |s.mob 0 - s.mob t| ≤ s.width * s.distortion * |(0:ℝ) - t| := h
    _ ≤ s.width * s.distortion * 1 := by exact mul_le_mul_of_nonneg_left habs hc
    _ = s.width * s.distortion := by ring

/-- **A forced block reads the basepoint.**  Every image point agrees with `s.mob 0` in its first
`m` digits, provided the basepoint's orbit avoids the cylinder boundaries at the accumulated
scale `δ · scale`, for some `δ` above the image's diameter. -/
theorem cfDigit_image_eq_basepoint (s : MobState) {δ : ℝ}
    (hδ : s.width * s.distortion < δ) (m : ℕ)
    (hgood : ∀ i < m, gaussMap^[i] (s.mob 0) ∈ Set.Ioo (0:ℝ) 1 ∧
      gaussMap^[i] (s.mob 0) ∉ boundaryBad (δ * scale (s.mob 0) i))
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) (htpos : 0 < s.mob t) :
    ∀ i < m, cfDigit (s.mob t) i = cfDigit (s.mob 0) i :=
  cfDigit_agree_depth (lt_of_le_of_lt (s.abs_mob_sub_basepoint_le ht) hδ) htpos m hgood

/-- **All or nothing.**  If the state forces the word `w`, its pullback of `I_w` is everything. -/
theorem preimage_cfCylinder_eq_of_forced (s : MobState) {w : List ℕ}
    (himg : ∀ t ∈ Set.Ioo (0:ℝ) 1, s.mob t ∈ Set.Ioo (0:ℝ) 1)
    (hforced : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ i < w.length, cfDigit (s.mob t) i = w.getD i 0) :
    s.mob ⁻¹' (cfCylinder w) ∩ Set.Ioo (0:ℝ) 1 = Set.Ioo (0:ℝ) 1 := by
  ext t
  refine ⟨fun h => h.2, fun ht => ⟨⟨himg t ht, hforced t ht⟩, ht⟩⟩

/-- `γ` is a probability measure on `(0,1)`. -/
theorem gaussMeasure_Ioo_one : gaussMeasure (Set.Ioo (0:ℝ) 1) = 1 := by
  have h := gaussMeasure_inter_Ioo (S := (Set.univ : Set ℝ)) MeasurableSet.univ
  rw [Set.univ_inter] at h
  rw [h, gaussMeasure_univ]

/-- **The pullback constant degenerates on a forced block.**  It is at least `1/γ(I_w)`, so the
bound of `gaussMeasure_preimage_le` says only `≤ 1`. -/
theorem one_le_pullbackConstant_of_forced (s : MobState) {w : List ℕ}
    (himg : ∀ t ∈ Set.Ioo (0:ℝ) 1, s.mob t ∈ Set.Ioo (0:ℝ) 1)
    (hforced : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ i < w.length, cfDigit (s.mob t) i = w.getD i 0) :
    1 ≤ 2 * s.distortion / s.width * (gaussMeasure (cfCylinder w)).toReal := by
  have hw := s.width_pos
  have hdist := s.distortion_pos
  have hc : (0:ℝ) ≤ 2 * s.distortion / s.width := by positivity
  have hkey := s.gaussMeasure_preimage_le (measurableSet_cfCylinder w) (cfCylinder_subset_Ioo w)
  rw [preimage_cfCylinder_eq_of_forced s himg hforced, gaussMeasure_Ioo_one] at hkey
  have hfin : ENNReal.ofReal (2 * s.distortion / s.width) * gaussMeasure (cfCylinder w) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono hfin hkey
  rwa [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h'

/-- **The price of forced emission.**  A state that forces the word `w` has width at most
`2 · distortion · γ(I_w)`.  Forcing a long word therefore forces an exponentially narrow state —
which is lap 30's fact (β), quantitatively, and rules out any uniform width floor. -/
theorem width_le_of_forced (s : MobState) {w : List ℕ}
    (himg : ∀ t ∈ Set.Ioo (0:ℝ) 1, s.mob t ∈ Set.Ioo (0:ℝ) 1)
    (hforced : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ i < w.length, cfDigit (s.mob t) i = w.getD i 0) :
    s.width ≤ 2 * s.distortion * (gaussMeasure (cfCylinder w)).toReal := by
  have hw := s.width_pos
  have h := s.one_le_pullbackConstant_of_forced himg hforced
  have heq : 2 * s.distortion / s.width * (gaussMeasure (cfCylinder w)).toReal
      = 2 * s.distortion * (gaussMeasure (cfCylinder w)).toReal / s.width := by
    field_simp
  rw [heq, le_div_iff₀ hw, one_mul] at h
  exact h

end MobState

section Audit

#print axioms MobState.abs_mob_sub_basepoint_le
#print axioms MobState.cfDigit_image_eq_basepoint
#print axioms MobState.preimage_cfCylinder_eq_of_forced
#print axioms MobState.gaussMeasure_Ioo_one
#print axioms MobState.one_le_pullbackConstant_of_forced
#print axioms MobState.width_le_of_forced

end Audit

end NormalNumbers.VandeheyS7
