/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-GS: a narrow greedy state means the IMAGE's orbit is near a cylinder boundary

The greedy state is reduced at every time (`not_emittable_grunState`, S7-GR), so S7-SS applies to it
unconditionally: its image interval straddles a cylinder boundary.  Pushing that through S7-GC's
correctness gives the sharp form of the width debt for the greedy run.

* `straddleSet_mono` — the straddle set grows with the scale.
* `grunState_mem_straddleSet` — at every time the greedy state's left endpoint lies in
  `straddleSet (width)`, hence in `straddleSet η` whenever `width < η`.
* `gaussMap_iterate_image_eq` — the image's orbit point at output time `|gOut Φ x n|` is exactly
  the greedy state's value at the input orbit point: `G^{|gOut n|}(Φ.mob x) = (grunState n).mob (Gⁿx)`.
* `image_orbit_near_boundary_of_narrow` — **the reduction**: if `width (grunState Φ x n) < η` then

      ∃ k ≥ 1,  |G^{|gOut Φ x n|} (Φ.mob x) − 1/k| ≤ 2η .

So the width debt of the greedy run — `WidthAfford`, `MeanSlack`, and with them the non-vacuity of
the crux (S7-WQ) — is implied by a NO-CONCENTRATION statement about the image orbit: it must not
over-visit the neighbourhood of the cylinder boundaries.  S7-SM prices that neighbourhood at
`≍ √η`, and the lap-91 probe measures the greedy run's narrow-time frequency at exactly `√η` across
five decades.  This is strictly weaker than the headline (no digit frequencies, only a
no-concentration bound), and it is the sharpest form the remaining scalar obligation has taken.

## Guard rule

**Content locator.**  Everything is an application: S7-SS supplies the straddle, S7-GC the
identification of the state's value with the image's orbit point, and `abs_sub_le_width` moves from
the endpoint to the value.

**Degenerate cases.**  The hypothesis `0 < min (mob 0) (mob 1)` excludes the image interval touching
`0`, where every digit is a candidate and the machine can stall forever (S7-SS's guard rule).
-/
import NormalNumbers.VandeheyS7GreedyCorrect
import NormalNumbers.VandeheyS7StallStraddle

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

lemma straddleSet_mono {w w' : ℝ} (h : w ≤ w') : straddleSet w ⊆ straddleSet w' := by
  rintro z ⟨k, hk, h1, h2⟩
  exact ⟨k, hk, h1, by linarith⟩

namespace MapState

/-- At every time the greedy state straddles a cylinder boundary. -/
theorem grunState_mem_straddleSet (Φ : MapState) (x : ℝ) (n : ℕ)
    (hpos : 0 < min ((grunState Φ x n).mob 0) ((grunState Φ x n).mob 1)) :
    min ((grunState Φ x n).mob 0) ((grunState Φ x n).mob 1)
      ∈ straddleSet (grunState Φ x n).width :=
  straddle_of_not_emittable (not_emittable_grunState Φ x n) hpos

/-- **The image's orbit point at output time.**  Stripping the output word off the image leaves the
greedy state's value at the input's orbit point. -/
theorem gaussMap_iterate_image_eq (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ)
    (hinner : (grunState Φ x n).mob (gaussMap^[n] x) ∈ Set.Ioo (0:ℝ) 1) :
    gaussMap^[(gOut Φ x n).length] (Φ.mob x) = (grunState Φ x n).mob (gaussMap^[n] x) := by
  rw [mob_eq_cylMap_gOut Φ hx n]
  exact gaussMap_iterate_cylMap_mob (gOut Φ x n) (gOut_pos Φ x n) hinner

/-- **S7-GS, the reduction.**  A narrow greedy state puts the image's orbit point within `2η` of a
cylinder boundary. -/
theorem image_orbit_near_boundary_of_narrow (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ)
    (hinner : (grunState Φ x n).mob (gaussMap^[n] x) ∈ Set.Ioo (0:ℝ) 1)
    (hpos : 0 < min ((grunState Φ x n).mob 0) ((grunState Φ x n).mob 1))
    {η : ℝ} (hη : (grunState Φ x n).width < η) :
    ∃ k : ℕ, 1 ≤ k ∧ |gaussMap^[(gOut Φ x n).length] (Φ.mob x) - 1 / (k : ℝ)| ≤ 2 * η := by
  classical
  obtain ⟨k, hk, hle, hlt⟩ :=
    straddleSet_mono hη.le (grunState_mem_straddleSet Φ x n hpos)
  refine ⟨k, hk, ?_⟩
  set s := grunState Φ x n with hs
  set lo : ℝ := min (s.mob 0) (s.mob 1) with hlo
  set v : ℝ := s.mob (gaussMap^[n] x) with hv
  have hxn : gaussMap^[n] x ∈ Set.Ioo (0:ℝ) 1 := hx n
  -- the value is within the width of the left endpoint
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hvx : gaussMap^[n] x ∈ Icc (0:ℝ) 1 := ⟨hxn.1.le, hxn.2.le⟩
  have hd0 : |v - s.mob 0| ≤ s.width := abs_sub_le_width s hvx h0
  have hd1 : |v - s.mob 1| ≤ s.width := abs_sub_le_width s hvx h1
  have hvlo : |v - lo| ≤ s.width := by
    rcases min_cases (s.mob 0) (s.mob 1) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [hlo, he]; exact hd0
    · rw [hlo, he]; exact hd1
  -- and the boundary is within the width of the endpoint
  have hbd : |lo - 1 / (k : ℝ)| ≤ η := by
    rw [abs_le]
    constructor <;> linarith
  have hstep := gaussMap_iterate_image_eq Φ hx n hinner
  rw [hstep]
  have htri : |v - 1 / (k : ℝ)| ≤ |v - lo| + |lo - 1 / (k : ℝ)| := by
    have := abs_add_le (v - lo) (lo - 1 / (k : ℝ))
    simpa using this
  have hwlt : s.width < η := hη
  calc |v - 1 / (k : ℝ)| ≤ |v - lo| + |lo - 1 / (k : ℝ)| := htri
    _ ≤ s.width + η := by linarith
    _ ≤ 2 * η := by linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.grunState_mem_straddleSet
#print axioms NormalNumbers.VandeheyS7.MapState.gaussMap_iterate_image_eq
#print axioms NormalNumbers.VandeheyS7.MapState.image_orbit_near_boundary_of_narrow

end Audit
