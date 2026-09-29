/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-EE: emission is available as soon as the state is narrow around an irrational

S7-MS made the emission step unconditional *given* the cylinder condition on the two endpoint
values.  This module supplies the cylinder condition from the only thing a transducer ever has:
the state's image is a short interval around the image orbit point, which is irrational.

* `exists_digit_of_irrational` — an irrational `p ∈ (0,1)` lies in the OPEN cylinder
  `(1/(a+1), 1/a)` for `a = ⌊1/p⌋`; the openness is exactly what irrationality buys (a rational
  `1/k` sits on a wall between two cylinders, directive fact (β)).
* `MapState.dist_mob_le` — a `MapState` is Lipschitz on `[0,1]` with constant
  `|det| / min(d, c+d)²`, so its image is an interval of controlled width.
* `MapState.exists_emit_of_close` — **the emission criterion**: if both endpoint values are within
  `r` of an irrational `p` and `r` is smaller than `p`'s distance to the two cylinder walls, the
  emission exists.  No width floor, no distortion bound: only "narrow around an irrational".

This is the missing half of the `clockUnbounded` field of S7-PN's `StatePin`.  The remaining step,
for the next lap, is that the state really does become narrow — which is contraction of the input
cylinders composed with a fixed Lipschitz state, and is where the emitted words re-expand.
-/
import NormalNumbers.VandeheyS7MapState

namespace NormalNumbers.VandeheyS7

open Set

/-- **Irrationality opens the cylinder.**  Every irrational `p ∈ (0,1)` is interior to the
cylinder it belongs to. -/
theorem exists_digit_of_irrational {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (hirr : Irrational p) :
    ∃ a : ℕ, 1 ≤ a ∧ p ∈ Ioo (1 / ((a : ℝ) + 1)) (1 / (a : ℝ)) := by
  have hp0 : 0 < p := hp.1
  have hinv : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; simpa using hp.2
  set m : ℤ := ⌊1 / p⌋ with hm
  have hm1 : 1 ≤ m := by rw [hm, Int.le_floor]; exact_mod_cast hinv.le
  have hmle : (m : ℝ) ≤ 1 / p := Int.floor_le _
  have hltm : 1 / p < (m : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one (1 / p)
  have hne : (m : ℝ) ≠ 1 / p := by
    intro h
    have : Irrational (1 / p) := by
      rw [one_div]; exact hirr.inv
    exact this ⟨(m : ℚ), by push_cast; exact h⟩
  have hmlt : (m : ℝ) < 1 / p := lt_of_le_of_ne hmle hne
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hacast : ((a : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) ha
  have hm0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < m)
  have hA : (1:ℝ) < ((m : ℝ) + 1) * p := (div_lt_iff₀ hp0).1 hltm
  have hB : (m : ℝ) * p < 1 := (lt_div_iff₀ hp0).1 hmlt
  refine ⟨a, by omega, ?_, ?_⟩
  · rw [hacast, div_lt_iff₀ (by linarith : (0:ℝ) < (m:ℝ) + 1)]
    linarith
  · rw [hacast, lt_div_iff₀ hm0]
    linarith

namespace MapState

/-- The smallest value of the denominator on `[0,1]`. -/
noncomputable def minDen (s : MapState) : ℝ := min s.d (s.c + s.d)

lemma minDen_pos (s : MapState) : 0 < s.minDen := lt_min s.hd s.hcd

lemma minDen_le (s : MapState) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : s.minDen ≤ s.c * z + s.d := by
  have h : s.c * z + s.d = (1 - z) * s.d + z * (s.c + s.d) := by ring
  rw [h]
  have h1 : s.minDen ≤ s.d := min_le_left _ _
  have h2 : s.minDen ≤ s.c + s.d := min_le_right _ _
  nlinarith [hz.1, hz.2, s.minDen_pos]

/-- **Lipschitz on `[0,1]`.**  The image is an interval of width at most `|det|/minDen²`. -/
theorem dist_mob_le (s : MapState) {z z' : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hz' : z' ∈ Icc (0:ℝ) 1) :
    |s.mob z - s.mob z'| ≤ |s.a * s.d - s.b * s.c| / s.minDen ^ 2 * |z - z'| := by
  have hd1 : 0 < s.c * z + s.d := s.den_pos hz
  have hd2 : 0 < s.c * z' + s.d := s.den_pos hz'
  have hkey : s.mob z - s.mob z'
      = (s.a * s.d - s.b * s.c) * (z - z') / ((s.c * z + s.d) * (s.c * z' + s.d)) := by
    unfold mob
    rw [div_sub_div _ _ hd1.ne' hd2.ne']
    congr 1
    ring
  rw [hkey, abs_div, abs_mul, abs_of_pos (mul_pos hd1 hd2)]
  rw [div_le_iff₀ (mul_pos hd1 hd2)]
  have hm1 := s.minDen_le hz
  have hm2 := s.minDen_le hz'
  have hmp := s.minDen_pos
  have hsq : s.minDen ^ 2 ≤ (s.c * z + s.d) * (s.c * z' + s.d) := by nlinarith
  have hdiv : |s.a * s.d - s.b * s.c| / s.minDen ^ 2 * |z - z'| * s.minDen ^ 2
      = |s.a * s.d - s.b * s.c| * |z - z'| := by
    field_simp
  nlinarith [abs_nonneg (s.a * s.d - s.b * s.c), abs_nonneg (z - z'),
    mul_nonneg (abs_nonneg (s.a * s.d - s.b * s.c)) (abs_nonneg (z - z')),
    mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (div_nonneg (abs_nonneg (s.a * s.d - s.b * s.c)) (sq_nonneg s.minDen))
        (abs_nonneg (z - z')))]

/-- **The emission criterion.**  A state whose two endpoint values sit within `r` of an irrational
`p`, with `r` below `p`'s distance to the cylinder walls, emits. -/
theorem exists_emit_of_close (t : MapState) {p r : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (hirr : Irrational p) (_hr : 0 < r)
    (h0 : |t.mob 0 - p| ≤ r) (h1 : |t.mob 1 - p| ≤ r)
    (hwall : ∀ a : ℕ, 1 ≤ a → p ∈ Ioo (1 / ((a : ℝ) + 1)) (1 / (a : ℝ)) →
      1 / ((a : ℝ) + 1) + r < p ∧ p + r < 1 / (a : ℝ)) :
    ∃ (a : ℕ) (ha : 1 ≤ a) (u : MapState),
      (readMap (a : ℝ) (by exact_mod_cast ha)).comp u = t := by
  obtain ⟨a, ha, hmem⟩ := exists_digit_of_irrational hp hirr
  obtain ⟨hw1, hw2⟩ := hwall a ha hmem
  have ha1 : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb0 := abs_le.1 h0
  have hb1 := abs_le.1 h1
  obtain ⟨u, hu⟩ := t.exists_emit ha1
    (by linarith [hb0.1]) (by linarith [hb0.2]) (by linarith [hb1.1]) (by linarith [hb1.2])
  exact ⟨a, ha, u, hu⟩

end MapState

section Audit

#print axioms exists_digit_of_irrational
#print axioms MapState.dist_mob_le
#print axioms MapState.exists_emit_of_close

end Audit

end NormalNumbers.VandeheyS7
