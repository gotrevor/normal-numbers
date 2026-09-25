import NormalNumbers.ElliottPrimePower
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The arithmetic bridge: the slice is `−ζ'/ζ` up to `O(1)` (lap 110)

`logWeightedSlice v X Y w` is the log-weighted prime sum at abscissa `s = (1+δ+w) + iv`; mathlib's
`L ↗Λ s = −ζ'/ζ(s)` is the same sum over all prime powers, untruncated.  This file identifies the
slice with a partial sum of `L ↗Λ`, term by term — the point being that the campaign's
`archimedeanTwist v p = p^{iv}` conjugated is exactly the `p^{-iv}` hidden in `p^{-s}`.

The two error terms (primes past `Y`, prime powers with `j ≥ 2`) are `ElliottDamped.logTail_le`
(lap 105) and `ElliottPrimePower.sum_pairs_le` (lap 109); assembling them is the next lap.
-/

open Finset ArithmeticFunction

namespace NormalNumbers.ElliottBridge

open NormalNumbers.ElliottDamped NormalNumbers.ElliottPrimePower
open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious

noncomputable section

/-- The abscissa of the `w`-slice: `s = (1 + δ + w) + iv` with `δ = 1/log X`. -/
noncomputable def sliceAbscissa (X : ℕ) (w v : ℝ) : ℂ :=
  ((1 + (Real.log (X : ℝ))⁻¹ + w : ℝ) : ℂ) + Complex.I * (v : ℂ)

theorem sliceAbscissa_re {X : ℕ} (w v : ℝ) :
    (sliceAbscissa X w v).re = 1 + (Real.log (X : ℝ))⁻¹ + w := by
  simp only [sliceAbscissa, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  ring

theorem sliceAbscissa_im {X : ℕ} (w v : ℝ) : (sliceAbscissa X w v).im = v := by
  simp only [sliceAbscissa, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re]
  ring

/-- The conjugated Archimedean twist is `p^{-iv}` in exponential form. -/
theorem conj_archimedeanTwist {p : ℕ} (hp : 0 < p) (v : ℝ) :
    (starRingEnd ℂ) (archimedeanTwist v p)
      = Complex.exp (-(Complex.I * (v : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))) := by
  rw [archimedeanTwist_eq_exp hp v, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **THE TERM IDENTITY.**  At `s = σ + iv` with `σ` real, the `p`-th term of `L ↗Λ` is exactly the
`p`-th summand of the slice. -/
theorem term_eq_slice_summand {p : ℕ} (hp : p.Prime) (σ v : ℝ) :
    LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + Complex.I * (v : ℂ)) p
      = (starRingEnd ℂ) (archimedeanTwist v p)
          * (((Real.log (p : ℝ)) * (p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  rw [LSeries.term_of_ne_zero (by omega : p ≠ 0)]
  rw [vonMangoldt_apply_prime hp]
  -- split `p^{-s}` into its real and Archimedean parts
  have hsplit : ((p : ℕ) : ℂ) ^ ((σ : ℂ) + Complex.I * (v : ℂ))
      = (((p : ℝ) ^ σ : ℝ) : ℂ) * Complex.exp (Complex.I * (v : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))
      := by
    rw [Complex.cpow_add _ _ hpC]
    congr 1
    · rw [Complex.ofReal_cpow hpR.le]
      norm_cast
    · rw [Complex.cpow_def_of_ne_zero hpC]
      congr 1
      rw [← Complex.natCast_log]
      ring
  rw [hsplit, conj_archimedeanTwist hp0 v]
  have hne : Complex.exp (Complex.I * (v : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hpow : (((p : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hpR.le]
  rw [Complex.exp_neg]
  field_simp
  rw [Complex.ofReal_cpow hpR.le (-σ)]
  push_cast
  rw [Complex.cpow_neg]
  field_simp

/-- **THE SLICE IS A PARTIAL SUM OF `L ↗Λ`.**  Exactly, with no error: the truncation and the
prime powers are the *missing* terms, bounded in the next lap. -/
theorem slice_eq_sum_term (v : ℝ) (X Y : ℕ) (w : ℝ) :
    logWeightedSlice v X Y w
      = ∑ p ∈ primesUpTo Y,
          LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) (sliceAbscissa X w v) p := by
  classical
  rw [logWeightedSlice]
  refine (Finset.sum_congr rfl ?_).symm
  intro p hp
  have hpp : p.Prime := (mem_primesUpTo.mp hp).1
  have hterm := term_eq_slice_summand hpp (1 + (Real.log (X : ℝ))⁻¹ + w) v
  rw [show sliceAbscissa X w v
      = ((1 + (Real.log (X : ℝ))⁻¹ + w : ℝ) : ℂ) + Complex.I * (v : ℂ) from rfl]
  rw [hterm]
  congr 2
  rw [show -(1 : ℝ) - (Real.log (X : ℝ))⁻¹ - w = -(1 + (Real.log (X : ℝ))⁻¹ + w) by ring]

end

end NormalNumbers.ElliottBridge
