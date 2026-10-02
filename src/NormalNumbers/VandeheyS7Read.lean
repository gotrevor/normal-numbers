/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RD: reading one input digit prices the lag exactly

`VandeheyS7Lag.deficit_telescope_le` reduced the clock rate to a per-step inequality

    deficit (s (n+1)) ≤ deficit (s n) + ξ n - (emission gain).

This module supplies the `ξ n`, unconditionally and with two-sided constants.  Reading the input
digit `a` restricts the state's domain from `[0,1]` to the digit cell `[1/(a+1), 1/a]`, whose length
is `1/(a(a+1))`; the two-sided derivative bound of `VandeheyS7Pull` (`expand_le` / `contract_le`,
themselves `mob_sub` plus `d ≤ c·t + d ≤ c + d`) then squeezes the new width between
`width / (K·a(a+1))` and `K·width / (a(a+1))`, `K = distortion`.  In lag form:

    deficit(after reading a)  ≤  deficit(before) + log (a(a+1)) + log distortion,

which is the `ξ n ≍ 2 log a_{n+1}` of `deficit_telescope_le` — and hence the precise reason
handoff idea 3 bites: the clock rate needs `(1/p) Σ log a` bounded, and CF-normality does not
supply that.  The matching lower bound `readWidth_ge` is what makes the estimate lossless: the
lag cannot be *over*paid by a read, so no slack accumulates over the orbit.

Degenerate case: `a = 1` gives factor `1/2`, the largest a read can be; `a → ∞` is the burst.
-/
import NormalNumbers.VandeheyS7Lag

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- The width of the state after reading the input digit `a`: the length of the image of the
digit cell `[1/(a+1), 1/a]`. -/
noncomputable def readWidth (s : MobState) (a : ℝ) : ℝ :=
  |s.mob (1 / a) - s.mob (1 / (a + 1))|

lemma one_div_sub_one_div (a : ℝ) (ha : 1 ≤ a) :
    1 / a - 1 / (a + 1) = 1 / (a * (a + 1)) := by
  have h0 : a ≠ 0 := by positivity
  have h1 : a + 1 ≠ 0 := by positivity
  field_simp
  try ring

/-- The exact formula for the post-read width. -/
theorem readWidth_eq (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    s.readWidth a = |s.a * s.d - s.b * s.c| * (1 / (a * (a + 1)))
      / ((s.c * (1 / a) + s.d) * (s.c * (1 / (a + 1)) + s.d)) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hu0 : (0:ℝ) ≤ 1 / (a + 1) := by positivity
  have hv0 : (0:ℝ) ≤ 1 / a := by positivity
  have hdenu : 0 < s.c * (1 / (a + 1)) + s.d := s.den_pos hu0
  have hdenv : 0 < s.c * (1 / a) + s.d := s.den_pos hv0
  have habs : |1 / a - 1 / (a + 1)| = 1 / (a * (a + 1)) := by
    rw [one_div_sub_one_div a ha, abs_of_pos (by positivity)]
  rw [readWidth, s.mob_sub hu0 hv0, abs_div, abs_of_pos (mul_pos hdenv hdenu), abs_mul, habs]

/-- The denominator product is squeezed between `d²` and `(c+d)²`. -/
theorem read_den_bounds (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    s.d * s.d ≤ (s.c * (1 / a) + s.d) * (s.c * (1 / (a + 1)) + s.d) ∧
    (s.c * (1 / a) + s.d) * (s.c * (1 / (a + 1)) + s.d) ≤ (s.c + s.d) * (s.c + s.d) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hu0 : (0:ℝ) ≤ 1 / (a + 1) := by positivity
  have hv0 : (0:ℝ) ≤ 1 / a := by positivity
  have hd : 0 < s.d := s.hd
  refine ⟨?_, ?_⟩
  · nlinarith [s.le_den hv0, s.le_den hu0]
  · have h1 : s.c * (1 / a) + s.d ≤ s.c + s.d := s.den_le (by rw [div_le_one ha0]; exact ha)
    have h2 : s.c * (1 / (a + 1)) + s.d ≤ s.c + s.d :=
      s.den_le (by rw [div_le_one (by positivity)]; linarith)
    exact mul_le_mul h1 h2 (le_of_lt (s.den_pos hu0)) (by linarith [s.hc])

/-- **The read is a two-sided contraction.**  Upper bound: the new width is at most
`distortion · width / (a(a+1))`, and the bound is attained at `c = 0`. -/
theorem readWidth_le (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    s.readWidth a ≤ s.distortion * s.width / (a * (a + 1)) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hd : 0 < s.d := s.hd
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  have hdet : (0:ℝ) ≤ |s.a * s.d - s.b * s.c| := abs_nonneg _
  have hRHS : s.distortion * s.width / (a * (a + 1))
      = |s.a * s.d - s.b * s.c| * (1 / (a * (a + 1))) / (s.d * s.d) := by
    rw [distortion, width_eq]
    field_simp
    try ring
  rw [readWidth_eq s ha, hRHS]
  have hlow := (s.read_den_bounds ha).1
  gcongr

/-- **And the matching lower bound**, so the read prices the lag with no slack. -/
theorem readWidth_ge (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    s.width / (s.distortion * (a * (a + 1))) ≤ s.readWidth a := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hd : 0 < s.d := s.hd
  have hcd : 0 < s.c + s.d := by linarith [s.hc]
  have hdet : (0:ℝ) ≤ |s.a * s.d - s.b * s.c| := abs_nonneg _
  have hLHS : s.width / (s.distortion * (a * (a + 1)))
      = |s.a * s.d - s.b * s.c| * (1 / (a * (a + 1))) / ((s.c + s.d) * (s.c + s.d)) := by
    rw [distortion, width_eq]
    field_simp
    try ring
  rw [readWidth_eq s ha, hLHS]
  have hup := (s.read_den_bounds ha).2
  have hdpos : (0:ℝ) < (s.c * (1 / a) + s.d) * (s.c * (1 / (a + 1)) + s.d) := by
    have hu0 : (0:ℝ) ≤ 1 / (a + 1) := by positivity
    have hv0 : (0:ℝ) ≤ 1 / a := by positivity
    exact mul_pos (s.den_pos hv0) (s.den_pos hu0)
  gcongr

/-! ## The lag form -/

/-- **The read's price on the lag.**  `deficit` after reading `a` exceeds the old `deficit` by at
most `log (a(a+1)) + log distortion`.  This is `ξ n` in `deficit_telescope_le`. -/
theorem deficit_read_le (s : MobState) {a : ℝ} (ha : 1 ≤ a) :
    - Real.log (s.readWidth a)
      ≤ s.deficit + Real.log (a * (a + 1)) + Real.log s.distortion := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hpos : (0:ℝ) < a * (a + 1) := by positivity
  have hK : 0 < s.distortion := s.distortion_pos
  have hw : 0 < s.width := s.width_pos
  have hlow : 0 < s.width / (s.distortion * (a * (a + 1))) := by positivity
  have hrw : 0 < s.readWidth a := lt_of_lt_of_le hlow (s.readWidth_ge ha)
  have hlog : Real.log (s.width / (s.distortion * (a * (a + 1)))) ≤ Real.log (s.readWidth a) :=
    Real.log_le_log hlow (s.readWidth_ge ha)
  have hexp : Real.log (s.width / (s.distortion * (a * (a + 1))))
      = Real.log s.width - Real.log s.distortion - Real.log (a * (a + 1)) := by
    rw [Real.log_div hw.ne' (by positivity), Real.log_mul hK.ne' hpos.ne']
    ring
  rw [hexp] at hlog
  simp only [deficit]
  linarith

section Audit

#print axioms MobState.readWidth_le
#print axioms MobState.readWidth_ge
#print axioms MobState.deficit_read_le

end Audit

end MobState

end NormalNumbers.VandeheyS7
