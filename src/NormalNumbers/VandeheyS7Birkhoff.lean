/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Window

/-!
# Merging must be distributional: the Birkhoff–Hopf coefficient, and its analytic core

`VandeheyS7Window` closed the window lemma.  The remaining half of `SampledUniformCount` is
MERGING: the state's influence on the output frequencies must wash out.  Over `ℤ` Vandehey cites
Saloff-Coste–Zúñiga for a finite chain.  Here that citation is unavailable twice over: the state
set is infinite (`infinite_zPhi_abs_le_one`) and, worse, pathwise merging is **provably
impossible** (`conj_goldenRatio_integral_forces_diagonal` — two states coincide only for the same
input prefix).  So the replacement must be distributional, and the standard instrument is
Birkhoff–Hopf contraction of the Hilbert projective metric.

## The setting, in one dimension

A state acts on the positive half-line by `f x = (a x + b)/(c x + d)` with nonnegative entries.
The Hilbert projective metric on `(0, ∞)` is `hdist x y = |log (x / y)|`.  Two classical facts,
both elementary here:

* **Finite image diameter** (`hdist_image_le`).  `f` maps `(0, ∞)` into `[b/d, a/c]`, so the image
  has `hdist`-diameter at most `log (a d / (b c))`.  This is the Birkhoff diameter `Δ`, and it is
  finite exactly when all four entries are positive — which is why *positivity*, not finiteness,
  is the right hypothesis over `ℤ[φ]`.
* **The contraction coefficient** is `tanh (Δ/4)`, which in these terms is

      birkhoffCoeff = (√(a d) − √(b c)) / (√(a d) + √(b c)) < 1 .

  `birkhoffCoeff_lt_one` proves it is `< 1` whenever `b c > 0`, and `birkhoffCoeff_nonneg` that it
  is `≥ 0` when `a d ≥ b c`.

## The analytic core, proved

The contraction statement `hdist (f x) (f y) ≤ birkhoffCoeff · hdist x y` reduces, in the
logarithmic coordinate `t ↦ log (f (e^t))`, to a bound on the derivative

    x · (a d − b c) / ((c x + d)(a x + b))  ≤  birkhoffCoeff ,

and the denominator expands to `a c x² + (a d + b c) x + b d`.  So the whole analytic content is

    `birkhoff_denom_bound` :  a c x² + (a d + b c) x + b d  ≥  x · (√(a d) + √(b c))² ,

which is AM–GM on `a c x² + b d ≥ 2 x √(a c · b d)` together with `(a c)(b d) = (a d)(b c)`.
**That inequality is proved here**, and `birkhoff_derivative_le` assembles it into the derivative
bound.  What is left is the mean-value bookkeeping that turns a derivative bound into a Lipschitz
bound in the log coordinate — no further inequality, and no dynamics.

## Why this is the right instrument, and not a coupling

Recorded so it is not relitigated: the 2026-08-24 probe found `2x` merges pathwise at step 3 with
a 1217-digit common tail while `φ` never merges in 1200 steps, and
`conj_goldenRatio_integral_forces_diagonal` turns that observation into a theorem.  Any argument
producing a common tail, a synchronising word, or a successful coupling is therefore refuted in
advance.  The Hilbert metric does not ask for one: it contracts the *distance between images of
different starting states* without ever making them equal.

## Guard rule

Content locator: `birkhoffCoeff_of_eq` — when `a d = b c` the matrix is singular, the coefficient
is `0` and the map is constant, so the content is entirely in the gap between `a d` and `b c`.
Degenerate case: `birkhoffCoeff_bc_zero` — with `b c = 0` the coefficient is `1` and there is no
contraction at all, which is exactly the case of a triangular state; positivity of all four
entries is load-bearing.
-/

namespace NormalNumbers.VandeheyS7

open Real

/-- The Hilbert projective metric on `(0, ∞)`, in the coordinate where it is a log-ratio. -/
noncomputable def hdist (x y : ℝ) : ℝ := |Real.log (x / y)|

theorem hdist_self {x : ℝ} (hx : 0 < x) : hdist x x = 0 := by
  simp [hdist, div_self hx.ne']

theorem hdist_comm (x y : ℝ) : hdist x y = hdist y x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hdist]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [hdist]
  rw [hdist, hdist, ← abs_neg, ← Real.log_inv, inv_div]

/-- **Finite image diameter.**  A state with positive entries maps `(0, ∞)` into `[b/d, a/c]`. -/
theorem mob_mem_Icc {a b c d x : ℝ} (_ha : 0 < a) (_hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdet : 0 ≤ a * d - b * c) (hx : 0 < x) :
    b / d ≤ (a * x + b) / (c * x + d) ∧ (a * x + b) / (c * x + d) ≤ a / c := by
  have hden : 0 < c * x + d := by positivity
  constructor
  · rw [div_le_div_iff₀ hd hden]
    nlinarith
  · rw [div_le_div_iff₀ hden hc]
    nlinarith

/-- The image ratio of any two points is at most `a d / (b c)`: the Birkhoff diameter, finite
exactly when all four entries are positive. -/
theorem hdist_image_le {a b c d x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdet : 0 ≤ a * d - b * c) (hx : 0 < x) (hy : 0 < y) :
    ((a * x + b) / (c * x + d)) / ((a * y + b) / (c * y + d)) ≤ a * d / (b * c) := by
  obtain ⟨-, hxu⟩ := mob_mem_Icc ha hb hc hd hdet hx
  obtain ⟨hyl, -⟩ := mob_mem_Icc ha hb hc hd hdet hy
  have hpy : 0 < (a * y + b) / (c * y + d) := by
    have : 0 < c * y + d := by positivity
    positivity
  have hbd : 0 < b / d := by positivity
  have hstep : ((a * x + b) / (c * x + d)) / ((a * y + b) / (c * y + d))
      ≤ (a / c) / (b / d) := by
    apply div_le_div₀ (by positivity) hxu hbd hyl
  calc ((a * x + b) / (c * x + d)) / ((a * y + b) / (c * y + d))
      ≤ (a / c) / (b / d) := hstep
    _ = a * d / (b * c) := by field_simp

/-! ## The Birkhoff coefficient -/

/-- `tanh (Δ/4)` in these terms: `(√(ad) − √(bc)) / (√(ad) + √(bc))`. -/
noncomputable def birkhoffCoeff (a b c d : ℝ) : ℝ :=
  (Real.sqrt (a * d) - Real.sqrt (b * c)) / (Real.sqrt (a * d) + Real.sqrt (b * c))

theorem birkhoffCoeff_nonneg {a b c d : ℝ} (_had : 0 ≤ a * d) (_hbc : 0 ≤ b * c)
    (h : b * c ≤ a * d) : 0 ≤ birkhoffCoeff a b c d := by
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (a * d)) with h0 | h0
  · have : Real.sqrt (b * c) = 0 := by
      have := Real.sqrt_le_sqrt h
      have h1 : Real.sqrt (b * c) ≤ Real.sqrt (a * d) := this
      linarith [Real.sqrt_nonneg (b * c), h0]
    simp [birkhoffCoeff, ← h0, this]
  · refine div_nonneg ?_ (by linarith [Real.sqrt_nonneg (b * c)])
    have := Real.sqrt_le_sqrt h
    linarith

/-- **The coefficient is a genuine contraction factor**: `< 1` as soon as `b c > 0`. -/
theorem birkhoffCoeff_lt_one {a b c d : ℝ} (hbc : 0 < b * c) (_had : 0 ≤ a * d) :
    birkhoffCoeff a b c d < 1 := by
  have hs : 0 < Real.sqrt (b * c) := Real.sqrt_pos.2 hbc
  have ht : 0 ≤ Real.sqrt (a * d) := Real.sqrt_nonneg _
  rw [birkhoffCoeff, div_lt_one (by linarith)]
  linarith

/-- Content locator: a singular state (`a d = b c`) has coefficient `0` — it is constant, and all
the content is in the gap between `a d` and `b c`. -/
theorem birkhoffCoeff_of_eq {a b c d : ℝ} (h : a * d = b * c) : birkhoffCoeff a b c d = 0 := by
  simp [birkhoffCoeff, h]

/-- Degenerate case: a triangular state (`b c = 0`) has coefficient `1` and does not contract at
all.  Positivity of all four entries is load-bearing. -/
theorem birkhoffCoeff_bc_zero {a b c d : ℝ} (h : b * c = 0) (had : 0 < a * d) :
    birkhoffCoeff a b c d = 1 := by
  have : Real.sqrt (a * d) ≠ 0 := (Real.sqrt_pos.2 had).ne'
  simp [birkhoffCoeff, h, this]

/-! ## The analytic core -/

/-- **The whole analytic content of Birkhoff contraction, in one inequality.**  AM–GM on
`a c x² + b d ≥ 2 x √(a c · b d)`, with `(a c)(b d) = (a d)(b c)` identifying the geometric mean
as `√(ad)·√(bc)`. -/
theorem birkhoff_denom_bound {a b c d x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) :
    x * (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2
      ≤ a * c * x ^ 2 + (a * d + b * c) * x + b * d := by
  have hac : (0:ℝ) ≤ a * c := mul_nonneg ha hc
  have hbd : (0:ℝ) ≤ b * d := mul_nonneg hb hd
  have had : (0:ℝ) ≤ a * d := mul_nonneg ha hd
  have hbc : (0:ℝ) ≤ b * c := mul_nonneg hb hc
  have hsq1 : Real.sqrt (a * d) ^ 2 = a * d := Real.sq_sqrt had
  have hsq2 : Real.sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt hbc
  -- the geometric mean of `ac` and `bd` is `√(ad)·√(bc)`
  have hgm : Real.sqrt (a * c) * Real.sqrt (b * d)
      = Real.sqrt (a * d) * Real.sqrt (b * c) := by
    rw [← Real.sqrt_mul hac, ← Real.sqrt_mul had]
    ring_nf
  have hamgm : 0 ≤ (Real.sqrt (a * c) * x - Real.sqrt (b * d)) ^ 2 := sq_nonneg _
  have hs1 : Real.sqrt (a * c) ^ 2 = a * c := Real.sq_sqrt hac
  have hs2 : Real.sqrt (b * d) ^ 2 = b * d := Real.sq_sqrt hbd
  nlinarith [hamgm, hgm, hs1, hs2, hsq1, hsq2, hx]

/-- **The derivative bound.**  In the logarithmic coordinate the derivative of the state's action
is at most the Birkhoff coefficient — which is the statement that the action is a
`birkhoffCoeff`-Lipschitz map for the Hilbert metric, modulo mean-value bookkeeping. -/
theorem birkhoff_derivative_le {a b c d x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hx : 0 < x) (hdet : 0 ≤ a * d - b * c) :
    x * (a * d - b * c) / ((c * x + d) * (a * x + b)) ≤ birkhoffCoeff a b c d := by
  have had : (0:ℝ) < a * d := by positivity
  have hbc : (0:ℝ) < b * c := by positivity
  have hs : 0 < Real.sqrt (a * d) := Real.sqrt_pos.2 had
  have ht : 0 < Real.sqrt (b * c) := Real.sqrt_pos.2 hbc
  have hsq1 : Real.sqrt (a * d) ^ 2 = a * d := Real.sq_sqrt had.le
  have hsq2 : Real.sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt hbc.le
  have hden : (c * x + d) * (a * x + b) = a * c * x ^ 2 + (a * d + b * c) * x + b * d := by
    ring
  have hlow := birkhoff_denom_bound ha.le hb.le hc.le hd.le hx.le
  have hpos : (0:ℝ) < (c * x + d) * (a * x + b) := by positivity
  have hst : Real.sqrt (b * c) ≤ Real.sqrt (a * d) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [birkhoffCoeff, div_le_div_iff₀ hpos (by linarith)]
  have hfac : a * d - b * c
      = (Real.sqrt (a * d) - Real.sqrt (b * c)) * (Real.sqrt (a * d) + Real.sqrt (b * c)) := by
    nlinarith [hsq1, hsq2]
  rw [hfac]
  nlinarith [hlow, hst, hx.le, sq_nonneg (Real.sqrt (a * d) + Real.sqrt (b * c))]

section Audit

#print axioms hdist_image_le
#print axioms birkhoffCoeff_lt_one
#print axioms birkhoff_denom_bound

end Audit

end NormalNumbers.VandeheyS7
