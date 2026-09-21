import Mathlib

/-!
# The square sieve remainder fits the frozen error rate

Use t=log x.  The actual epsilon window supplies epsilon>1/log t.
These estimates justify using a square remainder instead of a divisor sum.
-/

namespace NormalNumbers.PrimeModel

/-- A remainder x^(-1/8) is smaller than the frozen sieve error factor. -/
theorem square_remainder_absorbed (t ε k : ℝ)
    (ht : 1 < t) (hk : 1 ≤ k) (hε : 1 / Real.log t < ε) :
    Real.exp (-t / 8) ≤ Real.exp (-1 / (8 * k^2 * ε)) := by
  have hlog : 0 < Real.log t := Real.log_pos ht
  have he0 : 0 < ε := lt_trans (one_div_pos.mpr hlog) hε
  have hlogt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
    linarith
  have hprod : 1 < ε * Real.log t := (div_lt_iff₀ hlog).mp hε
  have hte : 1 ≤ t * ε := by
    have := mul_le_mul_of_nonneg_right hlogt he0.le
    nlinarith
  have hk2 : 1 ≤ k^2 := by nlinarith
  have ht0 : 0 < t := by linarith
  have hmajor : 1 ≤ t * (k^2 * ε) := by
    have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg ht0.le he0.le)
    nlinarith
  apply Real.exp_le_exp.mpr
  have hden : 0 < 8 * k^2 * ε := by positivity
  have hdiv : 1 / (8 * k^2 * ε) ≤ t / 8 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  simpa only [neg_div] using neg_le_neg hdiv

/-- Outside the small-epsilon Brun regime, an absolute constant suffices. -/
theorem brun_large_epsilon_absorbed (k ε : ℝ)
    (hk : 1 ≤ k) (hε : 1 / (7680 * k) < ε) :
    1 ≤ Real.exp 960 * Real.exp (-1 / (8 * k^2 * ε)) := by
  have hk0 : 0 < k := by linarith
  have hden : 0 < 7680 * k := by positivity
  have he0 : 0 < ε := lt_trans (one_div_pos.mpr hden) hε
  have hp : 1 < ε * (7680 * k) := (div_lt_iff₀ hden).mp hε
  have hp2 : 1 ≤ 7680 * k^2 * ε := by
    have := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 7680*k*ε)
    nlinarith
  have hd : 1 / (8*k^2*ε) ≤ 960 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*k^2*ε)).mpr
    nlinarith
  rw [← Real.exp_add]
  apply Real.one_le_exp
  simp only [neg_div]
  linarith

/-- info: 'NormalNumbers.PrimeModel.square_remainder_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_remainder_absorbed

/-- info: 'NormalNumbers.PrimeModel.brun_large_epsilon_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brun_large_epsilon_absorbed

end NormalNumbers.PrimeModel
