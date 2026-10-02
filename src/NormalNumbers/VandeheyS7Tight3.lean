/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Anchor
import NormalNumbers.VandeheyS7Reduction

/-!
# S7-T3: `ImageTight` reduces to an ANCHORED pullback

Lap 65 proved the anchored hit principle.  This module cashes it: the chain's second hypothesis
`ImageTight` follows from a transducer statement **strictly weaker than `WindowedPullback`** —
weaker in exactly the place that matters.

## The hypothesis

`AnchoredPullback q r₀ Λ`: for a CF-normal input `x` and a threshold `T`, the image orbit's visits
to the tail cell `cellSet [] T` are — up to frequency `ε` — matched by input times at which the
input orbit lies **below its own lower threshold or above its own upper one**, with both
thresholds within `Λ/T` of the respective endpoint.

Compare `WindowedPullback`, which must name an interval *determined by the last `k` input digits*.
`AnchoredPullback` names no window, allows the thresholds to depend on `n` in any way whatsoever,
and constrains only their *size*.  That is legitimate precisely because the target is anchored: by
`subset_Ioc_of_downwardClosed` the state's monotone pullback of `(0,1/T)` is downward-closed, so a
length bound already pins it inside a fixed interval, and `not_gappedHitPrinciple` — which forbids
this freedom for interior targets — does not apply.

The size `Λ/T` is what bounded distortion supplies: the state's pullback of an output set of
diameter `1/T` has diameter `≤ distortion · (1/T) / (image width)`.

## The theorem

`imageTight_of_anchoredPullback` : `AnchoredPullback q r₀ Λ → ImageTight (fract (q x + r₀))` for
every CF-normal `x`.  So the §7 chain's second obligation is no longer an assumption about the
image: it is a statement about the machine, of the soft kind.

## Guard rule

Content locator: the hypothesis' content is entirely in the *size* `Λ/T` of the thresholds — at
`c = 1` the anchored principle gives `2/log 2 > 1`, i.e. nothing — so a witness must genuinely
shrink the pullback as `T` grows, which is the bounded-distortion statement.  Degenerate case:
`Λ = 0` forces the pullback to be empty, which would make the image have no large digits at all;
the theorem is still true there, vacuously strong.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The anchored transducer hypothesis.**  See the module docstring. -/
def AnchoredPullback (q r₀ Λ : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ T : ℕ, 1 ≤ T → ∀ ε : ℝ, 0 < ε →
    ∃ (u v : ℕ → ℝ) (c : ℝ),
      0 ≤ c ∧ c ≤ Λ / (T : ℝ) ∧ c ≤ 1 ∧
      (∀ n, u n ≤ c) ∧ (∀ n, 1 - c ≤ v n) ∧
      ∀ᶠ p : ℕ in atTop,
        blockCount (cellSet [] T) p (Int.fract (q * x + r₀))
          ≤ anchoredHitCount u v p (Int.fract x) + ε * p

/-- **The reduction.**  An anchored pullback gives the chain's second hypothesis. -/
theorem imageTight_of_anchoredPullback {q r₀ Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h : AnchoredPullback q r₀ Λ) {x : ℝ} (hx : IsCFNormal (Int.fract x)) :
    ImageTight (Int.fract (q * x + r₀)) := by
  classical
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the input is an irrational of `(0,1)`
  have hirr : Irrational (Int.fract x) := by
    by_contra hc
    exact NormalNumbers.Literature.not_isCFNormal_of_not_irrational hc hx
  have hne : Int.fract x ≠ 0 := by
    intro hzero
    exact hirr ⟨0, by rw [hzero]; norm_num⟩
  have hmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hne), Int.fract_lt_one x⟩
  intro ε hε
  -- choose the threshold so the anchored bound is below `ε/2`
  obtain ⟨T, hT2, hTbig⟩ : ∃ T : ℕ, 2 ≤ T ∧ 2 * (Λ / (T:ℝ)) / Real.log 2 < ε / 4 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (max (8 * Λ / (ε * Real.log 2)) 2)
    have hN2 : (2:ℝ) < (N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    refine ⟨N, by exact_mod_cast hN2.le, ?_⟩
    have h1 : 8 * Λ / (ε * Real.log 2) < (N:ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    have hLN : Λ / (N:ℝ) < ε * Real.log 2 / 8 := by
      rw [div_lt_div_iff₀ hNpos (by norm_num : (0:ℝ) < 8)]
      nlinarith [h1]
    rw [div_lt_div_iff₀ hlog (by norm_num : (0:ℝ) < 4)]
    nlinarith [hLN, hlog]
  have hT1 : 1 ≤ T := by omega
  obtain ⟨u, v, c, hc0, hcT, hc1, hu, hv, hcmp⟩ := h x hx T hT1 (ε / 4) (by linarith)
  refine ⟨T, hT2, ?_⟩
  have hanch := anchoredHitFreq_le hirr hmem hx hc0 hc1 hu hv
    (show (0:ℝ) < ε / 4 by linarith)
  filter_upwards [hcmp, hanch, eventually_gt_atTop 0] with p hp hpa hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  -- transfer the comparison to frequencies
  have hdiv : blockCount (cellSet [] T) p (Int.fract (q * x + r₀)) / (p:ℝ)
      ≤ anchoredHitCount u v p (Int.fract x) / (p:ℝ) + ε / 4 := by
    have h2 : blockCount (cellSet [] T) p (Int.fract (q * x + r₀)) / (p:ℝ)
        ≤ (anchoredHitCount u v p (Int.fract x) + ε / 4 * (p:ℝ)) / (p:ℝ) := by
      gcongr <;> try exact hp
    have h3 : (anchoredHitCount u v p (Int.fract x) + ε / 4 * (p:ℝ)) / (p:ℝ)
        = anchoredHitCount u v p (Int.fract x) / (p:ℝ) + ε / 4 := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hsmall : 2 * c / Real.log 2 ≤ 2 * (Λ / (T:ℝ)) / Real.log 2 := by
    gcongr
  linarith [hdiv, hpa, hsmall, hTbig]

section Audit

#print axioms imageTight_of_anchoredPullback

end Audit

end NormalNumbers.VandeheyS7
