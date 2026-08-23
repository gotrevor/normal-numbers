/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Continued fraction definitions (Track B / expedition B5′)

The Gauss map, CF digits of a real, continuants, finite CF values, cylinder
sets, the Gauss measure, and the one-parameter conditional-density family
`h_t(y) = (1+t)/(1+ty)²` that powers the W3 mixing argument.

Conventions:
* Digits are read through iterates of the Gauss map:
  `cfDigit x n = ⌊(gaussMap^[n] x)⁻¹⌋₊`.  Total functions; on rationals the
  orbit hits `0` and the digit reads the junk value `0`, so "genuine digit"
  is exactly "digit ≥ 1" — lemmas carry `∀ a ∈ w, 1 ≤ a` hypotheses.
* `cfK` is the continuant `K(a₁,…,aₙ)`: for `x = [0; a₁, a₂, …]` the `n`-th
  convergent is `pₙ/qₙ` with `qₙ = cfK (a₁…aₙ)` and `pₙ = cfK (a₂…aₙ)`.
* Provenance: Becher–Yuhjtman, *On absolutely normal and continued fraction
  normal numbers*, IMRN 2019 (arXiv:1704.03622), §1.1 — see
  `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md` and `KHINCHIN.md`.
-/

namespace NormalNumbers

/-- The Gauss map `x ↦ 1/x mod 1` on `(0,1)`, sending `0` to `0`.
Junk values outside `[0,1)`. -/
noncomputable def gaussMap (x : ℝ) : ℝ :=
  if x = 0 then 0 else Int.fract x⁻¹

/-- The `n`-th CF partial quotient (0-indexed) of `x ∈ (0,1)`:
`aₙ₊₁ = ⌊1/(Tⁿx)⌋`.  Junk value `0` when the orbit hits `0` (rationals) or
leaves `(0,1)`; a genuine digit is always `≥ 1`. -/
noncomputable def cfDigit (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(gaussMap^[n] x)⁻¹⌋₊

/-- The continuant `K(a₁,…,aₙ)`: `K() = 1`, `K(a) = a`,
`K(a,b,…) = a·K(b,…) + K(…)`.  For `x = [0; a₁, a₂, …]` the convergent
denominators are `qₙ = cfK [a₁,…,aₙ]`. -/
def cfK : List ℕ → ℕ
  | [] => 1
  | [a] => a
  | a :: b :: l => a * cfK (b :: l) + cfK l

/-- Convergent numerator: `pₙ = K(a₂,…,aₙ)`. -/
def cfP (w : List ℕ) : ℕ := cfK (w.drop 1)

/-- The value of the finite continued fraction `[0; a₁, …, aₙ]`, as a
rational: `cfVal [] = 0`, `cfVal (a :: l) = 1/(a + cfVal l)`.  Junk on
words containing a `0` digit. -/
def cfVal : List ℕ → ℚ
  | [] => 0
  | a :: l => 1 / (a + cfVal l)

/-- The CF cylinder of the word `w`: reals in `(0,1)` whose first
`w.length` CF digits spell `w`. -/
noncomputable def cfCylinder (w : List ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 | ∀ i < w.length, cfDigit x i = w.getD i 0}

/-- The Gauss measure `dγ = dx/((1+x) log 2)` on `(0,1)` — the
`gaussMap`-invariant probability measure. -/
noncomputable def gaussMeasure : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity
    fun x => ENNReal.ofReal (((1 + x) * Real.log 2)⁻¹)

/-- The inverse-branch map of the cylinder `w`: `y ↦ [0; a₁, …, aₙ + y]`
in lowest terms, i.e. `(pₙ + pₙ₋₁·y)/(qₙ + qₙ₋₁·y)`.  Sends `[0,1]` onto
the closure of `cfCylinder w`; its image of `y = Tⁿx` recovers `x`. -/
noncomputable def cylMap (w : List ℕ) (y : ℝ) : ℝ :=
  ((cfP w : ℝ) + (cfP w.dropLast : ℝ) * y) /
    ((cfK w : ℝ) + (cfK w.dropLast : ℝ) * y)

/-- The conditional-density family: `h_t(y) = (1+t)/(1+t·y)²`.  For
`t = qₙ₋₁/qₙ`, this is the density (w.r.t. Lebesgue) of `Tⁿx` given
`x ∈ cfCylinder w`, uniformly in `[1/2, 2]` — the engine of the W3
mixing/Chebyshev argument. -/
noncomputable def tailDensity (t : ℝ) (y : ℝ) : ℝ :=
  (1 + t) / (1 + t * y) ^ 2

end NormalNumbers
