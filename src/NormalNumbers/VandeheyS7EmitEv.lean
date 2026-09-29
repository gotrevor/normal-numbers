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


/-! ## S7-EE2: width, and emission from the orbit point alone -/

namespace MapState

/-- The width of a state: the length of the image interval `mob([0,1])`. -/
noncomputable def width (s : MapState) : ℝ := |s.mob 1 - s.mob 0|

lemma width_nonneg (s : MapState) : 0 ≤ s.width := abs_nonneg _

/-- The difference formula: `mob` moves monotonically, with sign the sign of the determinant. -/
lemma mob_sub_eq (s : MapState) {z z' : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hz' : z' ∈ Icc (0:ℝ) 1) :
    s.mob z - s.mob z'
      = (s.a * s.d - s.b * s.c) * (z - z') / ((s.c * z + s.d) * (s.c * z' + s.d)) := by
  have hd1 : 0 < s.c * z + s.d := s.den_pos hz
  have hd2 : 0 < s.c * z' + s.d := s.den_pos hz'
  unfold mob
  rw [div_sub_div _ _ hd1.ne' hd2.ne']
  congr 1
  ring

/-- Every value of `mob` on `[0,1]` lies between the two endpoint values. -/
theorem mob_mem_uIcc (s : MapState) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
    s.mob z ∈ uIcc (s.mob 0) (s.mob 1) := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hdz : 0 < s.c * z + s.d := s.den_pos hz
  have hd0 : 0 < s.c * (0:ℝ) + s.d := s.den_pos h0
  have hd1 : 0 < s.c * (1:ℝ) + s.d := s.den_pos h1
  have e0 : s.mob z - s.mob 0
      = (s.a * s.d - s.b * s.c) * (z - 0) / ((s.c * z + s.d) * (s.c * 0 + s.d)) :=
    s.mob_sub_eq hz h0
  have e1 : s.mob 1 - s.mob z
      = (s.a * s.d - s.b * s.c) * (1 - z) / ((s.c * 1 + s.d) * (s.c * z + s.d)) :=
    s.mob_sub_eq h1 hz
  rcases lt_trichotomy (s.a * s.d - s.b * s.c) 0 with hD | hD | hD
  · refine Set.mem_uIcc.2 (Or.inr ⟨?_, ?_⟩)
    · have : s.mob 1 - s.mob z ≤ 0 := by
        rw [e1]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hD.le (by linarith [hz.2])) (by positivity)
      linarith
    · have : s.mob z - s.mob 0 ≤ 0 := by
        rw [e0]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hD.le (by linarith [hz.1])) (by positivity)
      linarith
  · exact absurd hD s.hdet
  · refine Set.mem_uIcc.2 (Or.inl ⟨?_, ?_⟩)
    · have : 0 ≤ s.mob z - s.mob 0 := by
        rw [e0]
        exact div_nonneg (mul_nonneg hD.le (by linarith [hz.1])) (by positivity)
      linarith
    · have : 0 ≤ s.mob 1 - s.mob z := by
        rw [e1]
        exact div_nonneg (mul_nonneg hD.le (by linarith [hz.2])) (by positivity)
      linarith

/-- **Everything inside the image interval.**  Two points of `[0,1]` never spread further than the
endpoints do. -/
theorem abs_sub_le_width (s : MapState) {z z' : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (hz' : z' ∈ Icc (0:ℝ) 1) : |s.mob z - s.mob z'| ≤ s.width := by
  have h1 := Set.mem_uIcc.1 (s.mob_mem_uIcc hz)
  have h2 := Set.mem_uIcc.1 (s.mob_mem_uIcc hz')
  rw [width, abs_sub_le_iff]
  rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases h2 with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
    constructor <;>
    · rcases abs_cases (s.mob 1 - s.mob 0) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith

/-- **Emission from the orbit point.**  If the state's image contains the irrational `p` and the
state is narrower than `p`'s distance to its two cylinder walls, the digit of `p` is emitted. -/
theorem exists_emit_of_width (t : MapState) {z₀ : ℝ} (hz₀ : z₀ ∈ Icc (0:ℝ) 1)
    (hp : t.mob z₀ ∈ Ioo (0:ℝ) 1) (hirr : Irrational (t.mob z₀))
    (hnarrow : ∀ a : ℕ, 1 ≤ a → t.mob z₀ ∈ Ioo (1 / ((a : ℝ) + 1)) (1 / (a : ℝ)) →
      t.width < min (t.mob z₀ - 1 / ((a : ℝ) + 1)) (1 / (a : ℝ) - t.mob z₀)) :
    ∃ (a : ℕ) (ha : 1 ≤ a) (u : MapState),
      (readMap (a : ℝ) (by exact_mod_cast ha)).comp u = t := by
  obtain ⟨a, ha, hmem⟩ := exists_digit_of_irrational hp hirr
  have ha1 : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hw := hnarrow a ha hmem
  have h0 : |t.mob 0 - t.mob z₀| ≤ t.width :=
    t.abs_sub_le_width ⟨le_refl 0, zero_le_one⟩ hz₀
  have h1 : |t.mob 1 - t.mob z₀| ≤ t.width :=
    t.abs_sub_le_width ⟨zero_le_one, le_refl 1⟩ hz₀
  have hb0 := abs_le.1 h0
  have hb1 := abs_le.1 h1
  have hmin1 : t.width < t.mob z₀ - 1 / ((a : ℝ) + 1) := lt_of_lt_of_le hw (min_le_left _ _)
  have hmin2 : t.width < 1 / (a : ℝ) - t.mob z₀ := lt_of_lt_of_le hw (min_le_right _ _)
  obtain ⟨u, hu⟩ := t.exists_emit ha1
    (by linarith [hb0.1]) (by linarith [hb0.2]) (by linarith [hb1.1]) (by linarith [hb1.2])
  exact ⟨a, ha, u, hu⟩

/-- Width contracts under a fixed left factor at that factor's Lipschitz rate. -/
theorem width_comp_le (s t : MapState) :
    (s.comp t).width ≤ |s.a * s.d - s.b * s.c| / s.minDen ^ 2 * t.width := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  rw [width, mob_comp s t h1, mob_comp s t h0]
  have hb := s.dist_mob_le (t.mapsTo h1) (t.mapsTo h0)
  rw [width]
  exact hb

end MapState

section Audit2

#print axioms MapState.abs_sub_le_width
#print axioms MapState.exists_emit_of_width
#print axioms MapState.width_comp_le

end Audit2

end NormalNumbers.VandeheyS7
