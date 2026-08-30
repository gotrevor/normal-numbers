/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LegendreShifted
import NormalNumbers.LcmUptoGrowth

/-!
# Irrationality of `log 2`

The classical Legendre-integral argument, assembled from bricks the repo
already owns: `legendre_log_two_small` produces a **nonzero** integer
combination `P + Q·log 2` with `|P + Q·log 2| ≤ lcm(1..n)·(1/5)ⁿ`, and
`lcmUpto_mul_geom_tendsto_zero` (valid since `4·(1/5) < 1`) sends that bound
to zero.  A rational `log 2 = num/den` would force every nonzero such
combination to have absolute value at least `1/den` — contradiction.

Consumed by the adder-wing endgame (`AdderEndgame.lean`): an eventually
periodic binary digit stream for `log 2` would make it rational.
-/

namespace NormalNumbers

open Filter Legendre

/-- **`log 2` is irrational.** -/
theorem irrational_log_two : Irrational (Real.log 2) := by
  rintro ⟨r, hr⟩
  have hden : (0:ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  -- a threshold below which no nonzero rational with denominator `r.den` fits
  have hlim := lcmUpto_mul_geom_tendsto_zero (c := (1/5 : ℝ)) (by norm_num)
    (by norm_num)
  have hpos : (0:ℝ) < 1 / r.den := by positivity
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hpos).exists
  obtain ⟨P, Q, hne, hle⟩ := legendre_log_two_small n
  rw [← hr] at hne hle
  -- P + Q·r = (P·den + Q·num)/den with a nonzero integer numerator
  set k : ℤ := P * r.den + Q * r.num with hk
  have hval : (P:ℝ) + (Q:ℝ) * (r:ℝ) = (k:ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def, hk]
    push_cast
    field_simp
  have hk0 : k ≠ 0 := by
    intro h0
    apply hne
    rw [hval, h0]
    simp
  have habs : (1:ℝ) / r.den ≤ |(P:ℝ) + (Q:ℝ) * (r:ℝ)| := by
    rw [hval, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
    exact_mod_cast Int.one_le_abs hk0
  linarith [hle.trans_lt hn]

end NormalNumbers
