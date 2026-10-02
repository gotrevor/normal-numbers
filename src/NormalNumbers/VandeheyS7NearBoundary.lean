/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-NB: a point near a cylinder boundary has a large digit within two steps

The lap-91 probe located the mechanism behind the greedy transducer's width: a reduced state is one
whose image STRADDLES a cylinder boundary (S7-SS), so a NARROW reduced state is one whose image
point sits within `width` of a boundary `1/(k+1)` — and the measured consequence was that the next
output digit is then `≍ 1/√width` (median ratio `1.2` to `e^{slack/2}`, correlation `0.65`).

This module proves the continued-fraction fact behind that measurement, for the Gauss map itself.

* `gaussMap_le_or_ge_of_near_boundary` — if `|y − 1/(k+1)| ≤ w` with `w` small, then one Gauss step
  lands near an ENDPOINT of `(0,1)`:  `G y ≤ 2(k+1)²w` or `G y ≥ 1 − (k+1)²w`.
* `exists_small_orbit_of_near_boundary` — hence within two steps the orbit point is small:
  `∃ i ≤ 2, Gⁱ y ≤ 4(k+1)²w`.
* `exists_large_digit_of_near_boundary` — hence a large digit appears within two steps:
  `∃ i ≤ 2, 1/(4(k+1)²w) ≤ cfDigit y i`.

Combined with S7-GC (the greedy output IS the image's continued fraction) this says: **every narrow
time of the greedy run injects a large digit into the output stream**, at a position the run is
about to emit.  Since S7-LD2 caps the output's total height by the input's, that is the shape of the
frequency bound the width debt needs — the remaining gap being the multiplicity of narrow times per
large digit.

## Guard rule

**Content locator.**  Both branches are the same two-line computation
`1/y − (k+1) = (1 − (k+1)y)/y` with `y ≥ 1/(2(k+1))`; the smallness hypothesis
`w ≤ 1/(4(k+1)²)` is only used to keep the fractional part on the right side of `1`.

**Degenerate cases.**  `y = 1/(k+1)` exactly gives `G y = 0` and the first branch with room to
spare.  `w` large makes the conclusion vacuous (`2(k+1)²w ≥ 1`), which is why the hypothesis is
there.
-/
import NormalNumbers.CFDefs
import NormalNumbers.VandeheyS7Run

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

/-- **One Gauss step from near a boundary lands near an endpoint.** -/
theorem gaussMap_le_or_ge_of_near_boundary {y w : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hy : y ∈ Ioo (0:ℝ) 1) (hw : 0 < w) (hwsmall : w ≤ 1 / (4 * ((k : ℝ) + 1) ^ 2))
    (hnear : |y - 1 / ((k : ℝ) + 1)| ≤ w) :
    gaussMap y ≤ 2 * ((k : ℝ) + 1) ^ 2 * w ∨ 1 - ((k : ℝ) + 1) ^ 2 * w ≤ gaussMap y := by
  have hkR : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by linarith
  have hk1sq : (0:ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have habs := abs_le.1 hnear
  -- `y` is at least half the boundary value
  have hwle : w ≤ 1 / (2 * ((k : ℝ) + 1)) := by
    have hmono : 1 / (4 * ((k : ℝ) + 1) ^ 2) ≤ 1 / (2 * ((k : ℝ) + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  have hylow : 1 / (2 * ((k : ℝ) + 1)) ≤ y := by
    have h1 : 1 / ((k : ℝ) + 1) - w ≤ y := by linarith [habs.1]
    have h2 : 1 / ((k : ℝ) + 1) - 1 / (2 * ((k : ℝ) + 1)) = 1 / (2 * ((k : ℝ) + 1)) := by
      field_simp
      ring
    linarith [hwle]
  have hylow' : 1 ≤ 2 * ((k : ℝ) + 1) * y := by
    have hmul := mul_le_mul_of_nonneg_left hylow (by positivity : (0:ℝ) ≤ 2 * ((k : ℝ) + 1))
    rw [mul_one_div, div_self (by positivity : (2 * ((k : ℝ) + 1)) ≠ 0)] at hmul
    linarith
  have hypos : 0 < y := hy.1
  have hyne : y ≠ 0 := hypos.ne'
  -- the key computation
  have hkey : y⁻¹ - ((k : ℝ) + 1) = (1 - ((k : ℝ) + 1) * y) / y := by
    field_simp
  rcases le_total y (1 / ((k : ℝ) + 1)) with hle | hlt
  · -- below the boundary: `1/y ≥ k+1`, and the excess is at most `2(k+1)²w`
    left
    have hnum : 1 - ((k : ℝ) + 1) * y ≤ ((k : ℝ) + 1) * w := by
      have hb : 1 / ((k : ℝ) + 1) - w ≤ y := by linarith [habs.1]
      have hmul := mul_le_mul_of_nonneg_left hb hk1.le
      rw [mul_sub, mul_one_div, div_self hk1.ne'] at hmul
      linarith
    have hnum0 : 0 ≤ 1 - ((k : ℝ) + 1) * y := by
      have hmul := mul_le_mul_of_nonneg_left hle hk1.le
      rw [mul_one_div, div_self hk1.ne'] at hmul
      linarith
    have hexc : y⁻¹ - ((k : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) ^ 2 * w := by
      rw [hkey, div_le_iff₀ hypos]
      nlinarith [mul_nonneg (mul_nonneg hk1.le hw.le) hypos.le]
    have hge : ((k : ℝ) + 1) ≤ y⁻¹ := by
      rw [le_inv_comm₀ hk1 hypos, ← one_div]
      exact hle
    -- so the floor is `k+1` and the fractional part is the excess
    have hlt' : y⁻¹ < ((k : ℝ) + 1) + 1 := by
      have : 2 * ((k : ℝ) + 1) ^ 2 * w ≤ 1 / 2 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        rw [le_div_iff₀ (by positivity)] at hwsmall
        nlinarith
      linarith
    have hfloor : ⌊y⁻¹⌋ = (k : ℤ) + 1 := by
      refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    rw [gaussMap, if_neg hyne, Int.fract, hfloor]
    push_cast
    linarith
  · -- above the boundary: `1/y ≤ k+1`, and the deficit is at most `(k+1)²w`
    rcases eq_or_lt_of_le hlt with heq | hgt
    · -- exactly on the boundary: one step lands on `0`
      left
      have hinv : y⁻¹ = ((k : ℝ) + 1) := by
        rw [← heq]; simp
      have hfl : ⌊y⁻¹⌋ = (k : ℤ) + 1 := by
        rw [hinv]
        refine Int.floor_eq_iff.2 ⟨?_, ?_⟩ <;> push_cast <;> linarith
      rw [gaussMap, if_neg hyne, Int.fract, hfl, hinv]
      push_cast
      have : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) ^ 2 * w := by positivity
      linarith
    right
    have hlt' : 1 ≤ ((k : ℝ) + 1) * y := by
      have hmul := mul_le_mul_of_nonneg_left hlt hk1.le
      rw [mul_one_div, div_self hk1.ne'] at hmul
      linarith
    have hnum : ((k : ℝ) + 1) * y - 1 ≤ ((k : ℝ) + 1) * w := by
      have hb : y ≤ 1 / ((k : ℝ) + 1) + w := by linarith [habs.2, hgt]
      have hmul := mul_le_mul_of_nonneg_left hb hk1.le
      rw [mul_add, mul_one_div, div_self hk1.ne'] at hmul
      linarith
    have hdef : ((k : ℝ) + 1) - y⁻¹ ≤ ((k : ℝ) + 1) ^ 2 * w := by
      have h : ((k : ℝ) + 1) - y⁻¹ = (((k : ℝ) + 1) * y - 1) / y := by field_simp
      rw [h, div_le_iff₀ hypos]
      have hy1 : y ≤ 1 := hy.2.le
      nlinarith [mul_nonneg (mul_nonneg hk1.le hw.le) hypos.le, hlt']
    have hle' : y⁻¹ < ((k : ℝ) + 1) := by
      rw [inv_lt_comm₀ hypos hk1, ← one_div]
      exact hgt
    have hge' : ((k : ℝ) + 1) - 1 ≤ y⁻¹ := by
      have : ((k : ℝ) + 1) ^ 2 * w ≤ 1 / 4 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)] at *
        rw [le_div_iff₀ (by positivity)] at hwsmall
        nlinarith
      linarith
    have hfloor : ⌊y⁻¹⌋ = (k : ℤ) := by
      refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    rw [gaussMap, if_neg hyne, Int.fract, hfloor]
    push_cast
    linarith

/-- **Within two steps the orbit is small.** -/
theorem exists_small_orbit_of_near_boundary {y w : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hy : ∀ j : ℕ, gaussMap^[j] y ∈ Ioo (0:ℝ) 1) (hw : 0 < w)
    (hwsmall : w ≤ 1 / (4 * ((k : ℝ) + 1) ^ 2))
    (hnear : |y - 1 / ((k : ℝ) + 1)| ≤ w) :
    ∃ i ≤ 2, gaussMap^[i] y ≤ 4 * ((k : ℝ) + 1) ^ 2 * w := by
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by
    have : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rcases gaussMap_le_or_ge_of_near_boundary hk (by simpa using hy 0) hw hwsmall
      (by simpa using hnear) with h | h
  · refine ⟨1, by norm_num, ?_⟩
    have hone : gaussMap^[1] y = gaussMap y := by simp
    rw [hone]
    nlinarith [hw, sq_nonneg ((k : ℝ) + 1)]
  · -- `G y` is near `1`, so one more step is near `0`
    refine ⟨2, le_refl 2, ?_⟩
    set z := gaussMap y with hz
    have hz01 : z ∈ Ioo (0:ℝ) 1 := by
      have := hy 1; simpa [hz] using this
    have hzne : z ≠ 0 := hz01.1.ne'
    have hsmall : ((k : ℝ) + 1) ^ 2 * w ≤ 1 / 4 := by
      rw [le_div_iff₀ (by positivity)] at hwsmall
      nlinarith
    have hzlow : 1 - ((k : ℝ) + 1) ^ 2 * w ≤ z := h
    have hA : 0 < ((k : ℝ) + 1) ^ 2 * w := by positivity
    -- `1/z ∈ (1, 1 + 2(k+1)²w]`
    have hzpos : 0 < z := hz01.1
    have hinv_lt : 1 < z⁻¹ := by
      rw [lt_inv_comm₀ zero_lt_one hzpos]
      simpa using hz01.2
    have hinv_le : z⁻¹ ≤ 1 + 2 * ((k : ℝ) + 1) ^ 2 * w := by
      rw [inv_le_iff_one_le_mul₀ hzpos]
      nlinarith [hA, hsmall, hzlow]
    have hfloor : ⌊z⁻¹⌋ = 1 := by
      refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast
        have : 2 * ((k : ℝ) + 1) ^ 2 * w ≤ 1 / 2 := by nlinarith
        linarith
    have hstep : gaussMap^[2] y = gaussMap z := by
      rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
      simp [hz]
    rw [hstep, gaussMap, if_neg hzne, Int.fract, hfloor]
    push_cast
    linarith

/-- **S7-NB.**  A point within `w` of a cylinder boundary has a digit at least `1/(4(k+1)²w)`
within two steps. -/
theorem exists_large_digit_of_near_boundary {y w : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hy : ∀ j : ℕ, gaussMap^[j] y ∈ Ioo (0:ℝ) 1) (hw : 0 < w)
    (hwsmall : w ≤ 1 / (4 * ((k : ℝ) + 1) ^ 2))
    (hnear : |y - 1 / ((k : ℝ) + 1)| ≤ w) :
    ∃ i ≤ 2, 1 / (4 * ((k : ℝ) + 1) ^ 2 * w) - 1 ≤ ((cfDigit y i : ℕ) : ℝ) := by
  obtain ⟨i, hi, hsmall⟩ := exists_small_orbit_of_near_boundary hk hy hw hwsmall hnear
  refine ⟨i, hi, ?_⟩
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by
    have : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0:ℝ) < 4 * ((k : ℝ) + 1) ^ 2 * w := by positivity
  have horb := hy i
  have hinv : 1 / (4 * ((k : ℝ) + 1) ^ 2 * w) ≤ (gaussMap^[i] y)⁻¹ := by
    have h := one_div_le_one_div_of_le horb.1 hsmall
    rwa [one_div (gaussMap^[i] y)] at h
  have hfl : (gaussMap^[i] y)⁻¹ - 1 ≤ ((⌊(gaussMap^[i] y)⁻¹⌋₊ : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor ((gaussMap^[i] y)⁻¹)
    linarith
  rw [cfDigit]
  linarith

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.gaussMap_le_or_ge_of_near_boundary
#print axioms NormalNumbers.VandeheyS7.exists_small_orbit_of_near_boundary
#print axioms NormalNumbers.VandeheyS7.exists_large_digit_of_near_boundary

end Audit
