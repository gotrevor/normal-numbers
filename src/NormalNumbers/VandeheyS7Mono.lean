/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Anchor
import NormalNumbers.VandeheyS7Distortion

/-!
# S7-M: the state is monotone, so its tail-cell pullbacks are anchored

Lap 65's anchored hit principle needs one structural input: that the transducer state's pullback of
an output event "the point is `< r`" is downward- or upward-closed in `(0,1)`.  That is exactly
monotonicity of the state's Möbius action, and this module proves it from the algebra, with no
calculus:

* `mob_sub_mob` — the exact difference formula
  `s.mob t₂ − s.mob t₁ = (ad − bc)(t₂ − t₁) / ((c t₂ + d)(c t₁ + d))`, valid for `0 ≤ t₁, t₂`
  because the denominators are positive there (`den_pos`).
* `mob_strictMonoOn` / `mob_strictAntiOn` — hence strict monotonicity on `[0,∞)`, with the sense
  given by the sign of the determinant (which is nonzero by the structure's own field `hdet`).
* `downwardClosed_mob_lt` / `upwardClosed_mob_lt` — hence the sublevel set `{t ∈ (0,1) | s.mob t <
  r}` is downward-closed when `ad − bc > 0` and upward-closed when `ad − bc < 0`.
* `anchored_mob_lt` — the two cases packaged: **every** state's tail-cell pullback is anchored to
  an endpoint.

With `subset_Ioc_of_downwardClosed` this turns a *measure* bound on the pullback into containment
in a fixed interval, which is what `AnchoredPullback` (lap 66) asks for and what
`not_gappedHitPrinciple` forbids for interior targets.

## Guard rule

Content locator: `hdet` is what excludes the degenerate constant map, for which the sublevel set is
`∅` or all of `(0,1)` — both of which are in fact still anchored, so the theorem is not sharp
there, only the *strict* monotonicity is.  Degenerate case: `c = 0` makes the map affine and the
formula reduces to `a(t₂ − t₁)/d²`, the right answer.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

namespace MobState

/-- **The exact difference formula.**  No derivatives. -/
theorem mob_sub_mob (s : MobState) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) :
    s.mob t₂ - s.mob t₁
      = (s.a * s.d - s.b * s.c) * (t₂ - t₁) / ((s.c * t₂ + s.d) * (s.c * t₁ + s.d)) := by
  have hd₁ : 0 < s.c * t₁ + s.d := s.den_pos h₁
  have hd₂ : 0 < s.c * t₂ + s.d := s.den_pos h₂
  rw [mob, mob, div_sub_div _ _ hd₂.ne' hd₁.ne']
  congr 1
  ring

/-- Strict monotonicity on `[0,∞)` when the determinant is positive. -/
theorem mob_lt_mob_of_det_pos (s : MobState) (hdet : 0 < s.a * s.d - s.b * s.c)
    {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (hlt : t₁ < t₂) : s.mob t₁ < s.mob t₂ := by
  have hd₁ : 0 < s.c * t₁ + s.d := s.den_pos h₁
  have hd₂ : 0 < s.c * t₂ + s.d := s.den_pos h₂
  have h := mob_sub_mob s h₁ h₂
  have hpos : 0 < (s.a * s.d - s.b * s.c) * (t₂ - t₁)
      / ((s.c * t₂ + s.d) * (s.c * t₁ + s.d)) := by
    apply div_pos (mul_pos hdet (by linarith)) (mul_pos hd₂ hd₁)
  linarith [h, hpos]

/-- Strict antitonicity on `[0,∞)` when the determinant is negative. -/
theorem mob_lt_mob_of_det_neg (s : MobState) (hdet : s.a * s.d - s.b * s.c < 0)
    {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (hlt : t₁ < t₂) : s.mob t₂ < s.mob t₁ := by
  have hd₁ : 0 < s.c * t₁ + s.d := s.den_pos h₁
  have hd₂ : 0 < s.c * t₂ + s.d := s.den_pos h₂
  have h := mob_sub_mob s h₁ h₂
  have hneg : (s.a * s.d - s.b * s.c) * (t₂ - t₁)
      / ((s.c * t₂ + s.d) * (s.c * t₁ + s.d)) < 0 := by
    apply div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdet (by linarith)) (mul_pos hd₂ hd₁)
  linarith [h, hneg]

/-- The sublevel set is downward-closed in `(0,1)` when the determinant is positive. -/
theorem downwardClosed_mob_lt (s : MobState) (hdet : 0 < s.a * s.d - s.b * s.c) (r : ℝ) :
    ∀ t ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r}, ∀ t' : ℝ, 0 < t' → t' < t →
      t' ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r} := by
  rintro t ⟨⟨ht0, ht1⟩, htr⟩ t' ht'0 ht'
  refine ⟨⟨ht'0, by linarith⟩, ?_⟩
  have := mob_lt_mob_of_det_pos s hdet ht'0.le ht0.le ht'
  linarith

/-- The sublevel set is upward-closed in `(0,1)` when the determinant is negative. -/
theorem upwardClosed_mob_lt (s : MobState) (hdet : s.a * s.d - s.b * s.c < 0) (r : ℝ) :
    ∀ t ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r}, ∀ t' : ℝ, t' < 1 → t < t' →
      t' ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r} := by
  rintro t ⟨⟨ht0, ht1⟩, htr⟩ t' ht'1 ht'
  refine ⟨⟨by linarith, ht'1⟩, ?_⟩
  have := mob_lt_mob_of_det_neg s hdet ht0.le (by linarith : (0:ℝ) ≤ t') ht'
  linarith

/-- **Every state's tail-cell pullback is anchored.**  The two cases, packaged. -/
theorem anchored_mob_lt (s : MobState) (r : ℝ) :
    (∀ t ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r}, ∀ t' : ℝ, 0 < t' → t' < t →
        t' ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r}) ∨
    (∀ t ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r}, ∀ t' : ℝ, t' < 1 → t < t' →
        t' ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r}) := by
  rcases lt_trichotomy (s.a * s.d - s.b * s.c) 0 with h | h | h
  · exact Or.inr (upwardClosed_mob_lt s h r)
  · exact absurd h s.hdet
  · exact Or.inl (downwardClosed_mob_lt s h r)

end MobState

section Audit

#print axioms MobState.mob_sub_mob
#print axioms MobState.anchored_mob_lt

end Audit

end NormalNumbers.VandeheyS7
