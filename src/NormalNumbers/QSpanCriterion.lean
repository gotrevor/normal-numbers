/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.QSpanNormal

/-!
# What the digits of a rational combination can look like

Campaign `KICKOFF-2026-10-05-qspan.md`.  The digits of `(a x + c y)/q` are read off from the joint
digit stream of `(x, y)` through bounded carries and a finite remainder, and by Wall
(`isNormal_rat_mul_add`) the divisor `q` never matters for normality.  Frozen here:

* `span_jointDim_budget`: a normal combination forces joint finite-state dimension `≥ 1/2`
  (entropy `log b` out of `2 log b`).  Implies `QSpan.span_dimension_budget` by subadditivity.
* `isNormal_span_of_jointNormal`: a jointly normal pair has every nonzero combination normal.
* `ae_isNormal_combo_iff`: for independent i.i.d. digits, `a x + c y` is a.e. normal iff every
  nonzero frequency `h` meets a zero of a digit polynomial, `φ_X(a h / bⁱ) · φ_Y(c h / bⁱ) = 0`
  for some `i ≥ 1` (the stationary law of `bⁿ(a x + c y) mod 1` has Fourier coefficients
  `∏ᵢ φ_X(a h/bⁱ) φ_Y(c h/bⁱ)`; a.e. orbits are generic for it).  Otherwise a.e. not normal.
* `ae_not_qSpanNormal_fiveDigits` with `ae_jointDim_fiveDigits`: digits uniform in `{0,…,4}`
  give joint dimension `log 25 / log 100 ≈ 0.70 > 1/2`, yet no combination is normal: `h = 5^N`
  defeats every `(a, c)`.  So the entropy budget is necessary, not sufficient.

Evidence: `experiments/qspan_digit_probe.py` (exact `ν̂` product and empirical coefficients;
`4x + 5y` has `|ν̂(25)| ≈ 0.0113` measured, `≈ 0.012` by hand).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace NormalNumbers.QSpanCriterion

open QSpan FiniteState

/-- The joint base-`b` digit stream of `(x, y)`, letters `Fin (b * b)`. -/
noncomputable def digitPair (b : ℕ) (hb : 0 < b) (x y : ℝ) : ℕ → Fin (b * b) :=
  fun i => finProdFinEquiv (digitSeq b hb x i, digitSeq b hb y i)

/-- **Joint entropy budget.**  Confidence 85%.  English proof: `QSpan.span_dimension_budget`,
stopped before the subadditivity step. -/
theorem span_jointDim_budget (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) (c₁ c₂ : ℚ)
    (hz : IsNormal b ((c₁ : ℝ) * x + c₂ * y)) :
    1 / 2 ≤ fsDim (digitPair b (by omega) x y) := by
  sorry

/-- **Jointly normal ⇒ the whole span is normal.**  Confidence 95%.  English proof: joint
normality is equidistribution of `(bⁿx, bⁿy)` in `𝕋²` (b-adic boxes); `bⁿ(a x + c y) mod 1` is the
image under `(u, v) ↦ a u + c v`, which pushes Lebesgue to Lebesgue for `(a, c) ≠ 0`; rational
coefficients by Wall. -/
theorem isNormal_span_of_jointNormal (b : ℕ) (hb : 2 ≤ b) (x y : ℝ)
    (hJ : IsNormalSequence (b * b) (fun i => (digitPair b (by omega) x y i : ℕ)))
    (c₁ c₂ : ℚ) (hne : c₁ ≠ 0 ∨ c₂ ≠ 0) : IsNormal b ((c₁ : ℝ) * x + c₂ * y) := by
  sorry

/-- Independent uniform letters of `Fin m × Fin m`. -/
noncomputable def pairs (m : ℕ) [NeZero m] : Measure (ℕ → Fin m × Fin m) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype (Fin m × Fin m)).toMeasure)

/-- The real with base-`b` digits `dX (ω i).1`. -/
noncomputable def realX {m : ℕ} (b : ℕ) (dX : Fin m → ℕ) (ω : ℕ → Fin m × Fin m) : ℝ :=
  ∑' i, (dX (ω i).1 : ℝ) / (b : ℝ) ^ (i + 1)

/-- The real with base-`b` digits `dY (ω i).2`. -/
noncomputable def realY {m : ℕ} (b : ℕ) (dY : Fin m → ℕ) (ω : ℕ → Fin m × Fin m) : ℝ :=
  ∑' i, (dY (ω i).2 : ℝ) / (b : ℝ) ^ (i + 1)

/-- Digit polynomial `φ(t) = (1/m) Σ_j e(t · d j)`. -/
noncomputable def digitPoly {m : ℕ} (d : Fin m → ℕ) (t : ℝ) : ℂ :=
  (∑ j, Complex.exp (2 * Real.pi * Complex.I * (t * d j))) / m

/-- **The Fourier-zero criterion.**  Confidence 80%.  English proof in the module doc: the
residue-free stationary law of `bⁿ(a x + c y) mod 1` is the law of `a X + c Y mod 1` with `X, Y`
independent self-similar; its `h`-th coefficient is the convergent product
`∏_{i ≥ 1} φ_X(a h / bⁱ) φ_Y(c h / bⁱ)`; the shift is Bernoulli, so a.e. orbits are generic for
it (Birkhoff on the digit shift, `frac(bⁿ z)` a continuous-a.e. function of the future digits and
the bounded carry); normal iff generic for Lebesgue iff every nonzero coefficient vanishes. -/
theorem ae_isNormal_combo_iff (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ) (hac : a ≠ 0 ∨ c ≠ 0) :
    (∀ᵐ ω ∂pairs m, IsNormal b (a * realX b dX ω + c * realY b dY ω)) ↔
      ∀ h : ℤ, h ≠ 0 → ∃ i : ℕ, 1 ≤ i ∧
        digitPoly dX (a * h / (b : ℝ) ^ i) * digitPoly dY (c * h / (b : ℝ) ^ i) = 0 := by
  sorry

/-- The 0–1 law beside the criterion: if the a.e. statement fails, a.e. point is not normal.
Confidence 85% (same proof: a.e. orbits are generic for one fixed law). -/
theorem ae_not_isNormal_combo_of_not (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ)
    (hbad : ∃ h : ℤ, h ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i →
        digitPoly dX (a * h / (b : ℝ) ^ i) * digitPoly dY (c * h / (b : ℝ) ^ i) ≠ 0) :
    ∀ᵐ ω ∂pairs m, ¬ IsNormal b (a * realX b dX ω + c * realY b dY ω) := by
  sorry

/-- Digits `0, …, 4`. -/
def five : Fin 5 → ℕ := fun j => j

/-- **Necessary, not sufficient: enough joint entropy, no normal combination.**  Confidence 85%.
English proof: by Wall reduce to integer `(a, c) ≠ 0`; take `h = 5^N` with `N > v₅(a), v₅(c)`
(or the one nonzero coefficient's valuation).  `φ_five(t) = 0` iff `5t ∈ ℤ`, `t ∉ ℤ`; at
`t = a 5^N / 10ⁱ` this needs `i = v₅(a 5^N) + 1 ≤ v₂(a)`, false for large `N`.  So no factor
vanishes; `ae_not_isNormal_combo_of_not`, countably many `(a, c)`. -/
theorem ae_not_qSpanNormal_fiveDigits :
    ∀ᵐ ω ∂pairs 5, ¬ QSpanNormal 10 (realX 10 five ω) (realY 10 five ω) := by
  sorry

/-- The same pair has joint finite-state dimension above the budget `1/2`
(`log 25 / log 100 ≈ 0.70`).  Confidence 85% (Bernoulli entropy rate; the digits of `realX` are
the letters, no `9`-tails since digits are `≤ 4`). -/
theorem ae_jointDim_fiveDigits :
    ∀ᵐ ω ∂pairs 5, 1 / 2 < fsDim (digitPair 10 (by norm_num) (realX 10 five ω) (realY 10 five ω)) := by
  sorry

end NormalNumbers.QSpanCriterion
