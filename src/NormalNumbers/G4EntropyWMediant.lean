/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOcc

/-!
# The mediant lemma — schedule-free

The mid-band squeeze splits a read prefix `[0, n)` at a band cutoff `T = fTW i` into a *history*
of length `T` and an *increment* of length `s = n − T`.  The history's word count `G` and the
increment's word count `D` are each controlled relative to their own length, and what is needed is
control of the **mediant** `(G + D)/(T + s)`.

Everything here is pure real arithmetic; nothing refers to the schedule.  The identity that makes
it work is

> `(G + D) − r·(T + s) = (G − r·T) + (D − r·s)`,

so the two deviations simply add, and dividing by `T + s` gives the bound.  The three forms:

* `mediant_abs_le` — the primitive: absolute deviations `A` and `B` give `(A + B)/(T + s)`;
* `mediant_abs_le_max` — relative deviations `e₁`, `e₂` give `max e₁ e₂` (no loss at all);
* `mediant_abs_le_trivial` — the **ungated branch**, where nothing at all is known about the
  increment beyond `0 ≤ D ≤ s`: the bound degrades to `e₁ + s/T`, which is useful exactly when the
  increment is a vanishing fraction of the history.
-/

namespace NormalNumbers.G4.Sched

/-- **The mediant primitive.**  Absolute deviations add. -/
theorem mediant_abs_le {G D T s r A B : ℝ} (hT : 0 < T) (hs : 0 ≤ s)
    (hG : |G - r * T| ≤ A) (hD : |D - r * s| ≤ B) :
    |(G + D) / (T + s) - r| ≤ (A + B) / (T + s) := by
  have hTs : (0 : ℝ) < T + s := by linarith
  have key : (G + D) / (T + s) - r = ((G - r * T) + (D - r * s)) / (T + s) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hTs]
  have habs : |(G - r * T) + (D - r * s)| ≤ A + B :=
    (abs_add_le _ _).trans (by linarith)
  exact div_le_div_of_nonneg_right habs hTs.le

/-- **The mediant of two relatively-controlled counts.**  If the history is within `e₁` and the
increment within `e₂` (each relative to its own length), the whole prefix is within `max e₁ e₂` —
the mediant never leaves the interval spanned by the two ratios. -/
theorem mediant_abs_le_max {G D T s r e₁ e₂ : ℝ} (hT : 0 < T) (hs : 0 ≤ s)
    (hG : |G - r * T| ≤ e₁ * T) (hD : |D - r * s| ≤ e₂ * s) :
    |(G + D) / (T + s) - r| ≤ max e₁ e₂ := by
  have hTs : (0 : ℝ) < T + s := by linarith
  refine (mediant_abs_le hT hs hG hD).trans ?_
  rw [div_le_iff₀ hTs]
  have h1 : e₁ * T ≤ max e₁ e₂ * T := by
    have := le_max_left e₁ e₂
    nlinarith
  have h2 : e₂ * s ≤ max e₁ e₂ * s := by
    have := le_max_right e₁ e₂
    nlinarith
  nlinarith

/-- **The ungated branch.**  When the increment carries no certificate at all — only the trivial
`0 ≤ D ≤ s` — the prefix ratio still stays within `e₁ + s/T` of `r`.  This is exactly what the
head of a band needs: `s/T` is tiny because the ungated head is a vanishing fraction of the
history. -/
theorem mediant_abs_le_trivial {G D T s r e₁ : ℝ} (hT : 0 < T) (hs : 0 ≤ s)
    (he₁ : 0 ≤ e₁) (hG : |G - r * T| ≤ e₁ * T)
    (hD0 : 0 ≤ D) (hDs : D ≤ s) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(G + D) / (T + s) - r| ≤ e₁ + s / T := by
  have hTs : (0 : ℝ) < T + s := by linarith
  have hD : |D - r * s| ≤ s := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  refine (mediant_abs_le hT hs hG hD).trans ?_
  rw [div_le_iff₀ hTs]
  have h1 : e₁ * T ≤ e₁ * (T + s) := by nlinarith
  have h2 : s ≤ (s / T) * (T + s) := by
    have hsT : s / T * T = s := by field_simp
    nlinarith [div_nonneg hs hT.le, mul_nonneg (div_nonneg hs hT.le) hs]
  nlinarith

end NormalNumbers.G4.Sched
