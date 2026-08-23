/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFCylinder

/-!
# W2 — digit laws + the Markov length substitute (scaffold)

Work package W2 of expedition B5′ (`KHINCHIN.md`): the single-digit law, the
relative-order-`n` partition calculus, the Gauss/Lebesgue two-sided
comparison, and the elementary substitute for B–Y Lemma 5 (Morita/Vallée
CLT) — `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md`,
"Efficiency-free substitute".  Stated here and left `sorry` for the campaign.

Statement plan (provenance in each docstring):
* `volume_digit_cylinder` — `|I_{[k]}| = 1/(k(k+1))` (Lebesgue digit law).
* `cfCylinder_disjoint` — same-length distinct words have disjoint cylinders.
* `volume_eq_tsum_extensions` — genuine `n`-digit extensions partition a
  genuine cylinder up to a null set; measures add exactly.
* `gaussMeasure_le_volume`, `volume_le_gaussMeasure` — the density window
  `1/(2 log 2) ≤ 1/((1+x) log 2) ≤ 1/log 2` as a two-sided measure
  comparison.
* `gaussMeasure_univ` — `γ` is a probability measure.
* `cfK_le_prod` — `K(a₁…aₙ) ≤ ∏(aᵢ+1)`, so `log qₙ ≤ Σ log(aᵢ+1)`.
* `tsum_mul_log_cfK_le` — conditional expected log-continuant grows at most
  linearly: `Σ_u |I_{wu}|·log K(u) ≤ C·n·|I_w|`.
* `half_mass_long_extensions` — **the Lemma-5 substitute** (Markov): at
  least half the mass of a genuine cylinder lies in extensions with
  `K(u) ≤ e^{Cn}`, i.e. relative length `≥ e^{-2Cn}/2`.
* `volume_append_mul_fib_le` — the free deterministic upper bound: every
  relative-order-`n` extension shrinks length by `≥ fib(n+1)²/2`.

Hand-checked anchors (frozen with the statements, per the planted-scaffold
doctrine): `K(3)·(K(3)+K()) = 12` matches `|I_{[3]}| = |(1/4, 1/3]| = 1/12`;
`K(1,2,3) = 10 ≤ 24 = 2·3·4`; `[1,2] ∈ genWords 2` while `[1,0] ∉`
(digit `0` is the junk marker, `CFDefs.lean` conventions).
-/

namespace NormalNumbers

open MeasureTheory

/-- The genuine digit words of length `n`: every digit `≥ 1` (digit `0` is
the junk marker for rationals/out-of-range, see `CFDefs.lean`).  The
cylinders `cfCylinder (w ++ u)`, `u ∈ genWords n`, partition `cfCylinder w`
up to a null set. -/
def genWords (n : ℕ) : Set (List ℕ) := {u | u.length = n ∧ ∀ a ∈ u, 1 ≤ a}

/-! ## Anchors (kernel-checked) -/

example : cfK [3] * (cfK [3] + cfK ([3].dropLast)) = 12 := by decide
example : cfK [1, 2, 3] ≤ (([1, 2, 3] : List ℕ).map (· + 1)).prod := by decide
example : ([1, 2] : List ℕ) ∈ genWords 2 := ⟨rfl, by decide⟩
example : ([1, 0] : List ℕ) ∉ genWords 2 := by
  intro h
  exact absurd (h.2 0 (by simp)) (by decide)

/-! ## Digit law and partition calculus -/

/-- **Single-digit cylinder length** (the Lebesgue precursor of Gauss–Kuzmin):
`|I_{[k]}| = 1/(k(k+1))`, i.e. `P(a₁ = k) = 1/(k(k+1))` under Lebesgue.
Specializes `volume_cfCylinder` (`cfK [k] = k`, `cfK [] = 1`).
Anchor: `k = 3` gives `1/12 = |(1/4, 1/3]|`. -/
theorem volume_digit_cylinder (k : ℕ) (hk : 1 ≤ k) :
    volume (cfCylinder [k]) =
      ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  sorry

/-- Distinct words of the same length read incompatible digits, so their
cylinders are disjoint.  No digit-positivity needed. -/
theorem cfCylinder_disjoint {w w' : List ℕ} (hlen : w.length = w'.length)
    (hne : w ≠ w') : Disjoint (cfCylinder w) (cfCylinder w') := by
  sorry

/-- **Relative-order-`n` partition**: the genuine `n`-digit extensions of a
genuine cylinder exhaust it up to a null set (irrationals have genuine
digits; the rational junk is countable), and they are pairwise disjoint, so
the measures add exactly.  This identity turns the distortion pair (B–Y
Lemma 3.2, W1) into a conditional-probability calculus. -/
theorem volume_eq_tsum_extensions (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) (n : ℕ) :
    volume (cfCylinder w) =
      ∑' u : genWords n, volume (cfCylinder (w ++ (u : List ℕ))) := by
  sorry

/-! ## Gauss measure vs Lebesgue -/

/-- Upper comparison: the Gauss density is at most `1/log 2`, so
`γ(s) ≤ (1/log 2)·|s|`. -/
theorem gaussMeasure_le_volume (s : Set ℝ) (hs : MeasurableSet s) :
    gaussMeasure s ≤ ENNReal.ofReal (Real.log 2)⁻¹ * volume s := by
  sorry

/-- Lower comparison on `(0,1)`: the Gauss density is at least
`1/(2 log 2)` there, so `(1/(2 log 2))·|s| ≤ γ(s)`. -/
theorem volume_le_gaussMeasure (s : Set ℝ) (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (2 * Real.log 2)⁻¹ * volume s ≤ gaussMeasure s := by
  sorry

/-- `γ` is a probability measure:
`γ(0,1) = (1/log 2)·∫₀¹ dx/(1+x) = log 2/log 2 = 1`. -/
theorem gaussMeasure_univ : gaussMeasure Set.univ = 1 := by
  sorry

/-! ## The Markov substitute for B–Y Lemma 5 -/

/-- The continuant is at most the product of (digit + 1):
`K(a₁…aₙ) ≤ ∏(aᵢ+1)`, hence `log qₙ ≤ Σ log(aᵢ+1)` — the elementary
observable replacing B–Y Lemma 4's CLT.  No positivity hypothesis needed. -/
theorem cfK_le_prod (w : List ℕ) : cfK w ≤ (w.map (· + 1)).prod := by
  sorry

/-- **Conditional expected log-continuant is linear in `n`**: for some
constant `C` and every genuine base cylinder,
`Σ_u |I_{wu}|·log K(u) ≤ C·n·|I_w|` over genuine words `u` of length `n`.
Route: `cfK_le_prod` + per-digit marginals via `volume_eq_tsum_extensions`,
`volume_cylinder_append_le`, `volume_digit_cylinder`, and summability of
`Σₖ log(k+1)/(k(k+1))`. -/
theorem tsum_mul_log_cfK_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      ∑' u : genWords n,
          volume (cfCylinder (w ++ (u : List ℕ))) *
            ENNReal.ofReal (Real.log (cfK (u : List ℕ))) ≤
        ENNReal.ofReal (C * n) * volume (cfCylinder w) := by
  sorry

/-- **The Lemma-5 substitute** (B–Y Lemma 5 without Morita/Vallée, worse
constants, no complexity claim): for some `C`, at least half the mass of any
genuine cylinder lies in genuine relative-order-`n` extensions with
`K(u) ≤ e^{Cn}` — whose relative length is therefore `≥ e^{-2Cn}/2` by the
volume formula and distortion.  Markov's inequality on
`tsum_mul_log_cfK_le` with threshold `e^{Cn}`. -/
theorem half_mass_long_extensions :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      volume (cfCylinder w) ≤
        2 * ∑' u : genWords n,
          (if (cfK (u : List ℕ) : ℝ) ≤ Real.exp (C * n)
            then volume (cfCylinder (w ++ (u : List ℕ))) else 0) := by
  sorry

/-- **Deterministic relative-length upper bound** (the free half of Lemma 5):
every genuine relative-order-`n` extension shrinks a cylinder by at least
`fib(n+1)²/2` — from `volume_cylinder_append_le`, `volume_cfCylinder`, and
`fib_le_cfK` (W1).  Multiplicative form to stay division-free in `ℝ≥0∞`. -/
theorem volume_append_mul_fib_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder (w ++ u)) * (Nat.fib (u.length + 1) : ENNReal) ^ 2 ≤
      2 * volume (cfCylinder w) := by
  sorry

end NormalNumbers
