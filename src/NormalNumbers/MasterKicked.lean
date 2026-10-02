/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterConjectures
import NormalNumbers.EquidistTransfer

/-!
# Hypothesis A as a machine: kicked series ⇒ normality

`hypA_isNormal_of_kicked`: if `x = Σ_{n≥1} r(n)/bⁿ` with `r(n) = p(n)/q(n)` satisfying the shape
conditions of Hypothesis A, `x` irrational, and the scaled tail `bⁿ(x − sₙ) → 0` (either sign),
then Hypothesis A makes `x` normal in base `b`.  The planted theorems `hypA_lnTwo` and
`hypA_pi_base16` are instances; the two-sided tail (`equidistributed_of_fract_perturb_abs`)
admits mixed-sign kicks such as the π² formula.
-/

namespace NormalNumbers.MasterConjectures

open Polynomial Filter NormalNumbers

/-- The Bailey–Crandall orbit is the fractional part of the scaled kicked partial sum. -/
theorem bcOrbit_eq_kicked (p q : ℤ[X]) (b : ℕ) (hb : 0 < b) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, 1 ≤ n → ((p.eval (n : ℤ) : ℤ) : ℝ) / ((q.eval (n : ℤ) : ℤ) : ℝ) = r n)
    (n : ℕ) : bcOrbit p q b n = Int.fract ((b : ℝ) ^ n * kickedPartial b r n) := by
  induction n with
  | zero => simp [bcOrbit, kickedPartial]
  | succ n ih =>
    rw [bcOrbit, ih, hr (n + 1) (by omega)]
    set t := (b : ℝ) ^ n * kickedPartial b r n
    have : (b : ℝ) * Int.fract t + r (n + 1) = (b * t + r (n + 1)) + ((-(b * ⌊t⌋)) : ℤ) := by
      rw [Int.fract]; push_cast; ring
    rw [this, Int.fract_add_intCast]
    congr 1
    have hbR : (b : ℝ) ≠ 0 := by positivity
    simp only [t, kickedPartial, Finset.sum_range_succ]
    field_simp
    ring

/-- **The Hypothesis A machine.** -/
theorem hypA_isNormal_of_kicked (hA : BaileyCrandallHypA) (p q : ℤ[X]) (b : ℕ) (hb : 2 ≤ b)
    (hp : p ≠ 0) (hdeg : p.natDegree < q.natDegree) (hq : ∀ n : ℕ, 1 ≤ n → q.eval (n : ℤ) ≠ 0)
    (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, 1 ≤ n → ((p.eval (n : ℤ) : ℤ) : ℝ) / ((q.eval (n : ℤ) : ℤ) : ℝ) = r n)
    (x : ℝ) (hirr : Irrational x)
    (htail : Tendsto (fun n : ℕ => (b : ℝ) ^ n * (x - kickedPartial b r n)) atTop (nhds 0)) :
    IsNormal b x := by
  have horb : orbit b x = fun n => Int.fract (bcOrbit p q b n
      + (b : ℝ) ^ n * (x - kickedPartial b r n)) := by
    funext n
    rw [orbit_eq_fract_add_tail b x (kickedPartial b r n) n, bcOrbit_eq_kicked p q b (by omega) r hr]
  rcases hA p q b hp hdeg hq hb with hfa | heq
  · exfalso
    have hpert := hasFiniteAttractor_perturb _ _ hfa htail
    rw [← horb] at hpert
    exact not_irrational_of_hasFiniteAttractor_base b hb x hpert hirr
  · rw [isNormal_iff_equidistributed_orbit b hb, horb]
    refine equidistributed_of_fract_perturb_abs _ _ heq (fun n => ?_) htail
    rw [bcOrbit_eq_kicked p q b (by omega) r hr]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

end NormalNumbers.MasterConjectures
