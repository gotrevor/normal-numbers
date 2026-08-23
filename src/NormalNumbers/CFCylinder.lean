/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDefs

/-!
# W1 — the CF cylinder toolkit (scaffold)

Work package W1 of expedition B5′ (`KHINCHIN.md`): the elementary continuant
and cylinder-measure algebra of Becher–Yuhjtman §1.1, stated here and left
`sorry` for the campaign.  NB we prove the Euler gluing identity by list
induction instead of B–Y's `α_{r,s}`/`Ω_{r,s}` subset combinatorics (their
Prop 2) — same content, far friendlier induction; these are internal
lemmas, not paper-pinned statements.

Statement plan (provenance in each docstring):
* `cfK_append` — Euler's continuant gluing identity.
* `cfK_drop_one_le`, `cfK_dropLast_le` — monotonicity under digit removal.
* `cfK_mul_le_append`, `cfK_append_le` — quasi-multiplicativity
  `q(a)q(b) ≤ q(ab) ≤ 2q(a)q(b)` (B–Y Lemma 3.1).
* `fib_le_cfK` — Fibonacci lower bound `qₙ ≥ fib (n+1)` (deterministic
  cylinder-length upper bound; replaces the lower half of B–Y Lemma 5).
* `cfVal_eq_div` — `[0;a₁…aₙ] = pₙ/qₙ`.
* `volume_cfCylinder` — `|I_w| = 1/(qₙ(qₙ + qₙ₋₁))`.
* `volume_cylinder_append_le`, `le_volume_cylinder_append` — bounded
  distortion `|I_a||I_b|/2 ≤ |I_{ab}| ≤ 2|I_a||I_b|` (B–Y Lemma 3.2).
* `tailDensity_mem_Icc`, `cylMap_denom_ratio_le` — the `[1/2, 2]` density
  window and the branch-derivative ratio bound (gateway to W3).

Hand-checked anchors (frozen with the statements, per the planted-scaffold
doctrine): `K(1,2,3) = 10` with `[0;1,2,3] = 7/10`; `K(2) · (K(2) + K()) = 6`
matches `|I_{[2]}| = |(1/3, 1/2]| = 1/6`; the gluing anchor
`K(1,2,3,4) = K(1,2)K(3,4) + K(1)K(4) = 39 + 4 = 43`.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Anchors (kernel-checked) -/

example : cfK [1, 2, 3] = 10 := by decide
example : cfVal [1, 2, 3] = 7 / 10 := by norm_num [cfVal]
example : cfK [2] * (cfK [2] + cfK ([2].dropLast)) = 6 := by decide
example : cfK ([1, 2] ++ [3, 4]) =
    cfK [1, 2] * cfK [3, 4] + cfK [1] * cfK [4] := by decide

/-! ## Continuant algebra -/

/-- **Euler's gluing identity** (B–Y Prop 2.3, list form): for nonempty `w`
and `u`, `K(wu) = K(w)K(u) + K(w⁻)K(u⁻)` where `w⁻` drops the last digit of
`w` and `u⁻` drops the first digit of `u`.  A polynomial identity — no
digit-positivity needed. -/
theorem cfK_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ []) :
    cfK (w ++ u) = cfK w * cfK u + cfK w.dropLast * cfK (u.drop 1) := by
  sorry

/-- Dropping the first digit does not increase the continuant (digits ≥ 1). -/
theorem cfK_drop_one_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfK (w.drop 1) ≤ cfK w := by
  sorry

/-- Dropping the last digit does not increase the continuant (digits ≥ 1). -/
theorem cfK_dropLast_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfK w.dropLast ≤ cfK w := by
  sorry

/-- Quasi-multiplicativity, lower half (B–Y Lemma 3.1):
`q(w)·q(u) ≤ q(wu)`. -/
theorem cfK_mul_le_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    cfK w * cfK u ≤ cfK (w ++ u) := by
  sorry

/-- Quasi-multiplicativity, upper half (B–Y Lemma 3.1):
`q(wu) ≤ 2·q(w)·q(u)`. -/
theorem cfK_append_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    cfK (w ++ u) ≤ 2 * (cfK w * cfK u) := by
  sorry

/-- Fibonacci lower bound: `qₙ ≥ fib (n+1)` for genuine digit words.  Gives
the deterministic cylinder-length upper bound `|I_w| ≤ φ^{-2(n-1)}` that
replaces the lower half of B–Y Lemma 5 in the efficiency-free construction. -/
theorem fib_le_cfK (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    Nat.fib (w.length + 1) ≤ cfK w := by
  sorry

/-! ## Finite CF values and cylinder measure -/

/-- `[0; a₁, …, aₙ] = pₙ/qₙ` in the continuant normal form. -/
theorem cfVal_eq_div (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfVal w = (cfP w : ℚ) / (cfK w : ℚ) := by
  sorry

/-- **Cylinder length** (B–Y §1.1): `|I_w| = 1/(qₙ(qₙ + qₙ₋₁))`.
Anchor: `w = [2]` gives `1/6 = |(1/3, 1/2]|`.  The definitional cylinder
differs from the open interval only on a countable (null) junk set. -/
theorem volume_cfCylinder (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    volume (cfCylinder w) =
      ENNReal.ofReal (1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)))) := by
  sorry

/-- **Bounded distortion, upper half** (B–Y Lemma 3.2):
`|I_{wu}| ≤ 2·|I_w|·|I_u|`. -/
theorem volume_cylinder_append_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder (w ++ u)) ≤
      2 * (volume (cfCylinder w) * volume (cfCylinder u)) := by
  sorry

/-- **Bounded distortion, lower half** (B–Y Lemma 3.2):
`|I_w|·|I_u| ≤ 2·|I_{wu}|`. -/
theorem le_volume_cylinder_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder w) * volume (cfCylinder u) ≤
      2 * volume (cfCylinder (w ++ u)) := by
  sorry

/-! ## The density window (gateway to W3) -/

/-- The conditional-density family is trapped in `[1/2, 2]` on the unit
square: `1/(1+t) ≤ h_t(y) ≤ 1+t` for `t, y ∈ [0,1]`. -/
theorem tailDensity_mem_Icc {t y : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    tailDensity t y ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  sorry

/-- Branch-derivative ratio bound: the denominators `qₙ + qₙ₋₁·y` of
`cylMap w` at any two points of `[0,1]` differ by a factor at most `2`
(so the derivative ratio is at most `4`) — bounded distortion of a single
inverse branch. -/
theorem cylMap_denom_ratio_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a)
    {y y' : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (hy' : y' ∈ Set.Icc (0 : ℝ) 1) :
    (cfK w : ℝ) + (cfK w.dropLast : ℝ) * y ≤
      2 * ((cfK w : ℝ) + (cfK w.dropLast : ℝ) * y') := by
  sorry

end NormalNumbers
