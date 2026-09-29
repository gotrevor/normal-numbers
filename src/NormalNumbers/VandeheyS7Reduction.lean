/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7HitIoo
import NormalNumbers.VandeheyS7Reduce
import NormalNumbers.VandeheySmith
import NormalNumbers.VandeheyS7Chain

/-!
# S7-R: the crux reduces to ONE transducer statement

With `windowHit_Ioo_le` (lap 55) the ergodic side of Vandehey §7 Problem 1 is finished.  This
module draws the consequence: the crux `OrbitWordBound` follows from a single hypothesis about
the machine, `WindowedPullback`, and nothing else.

## The hypothesis

`WindowedPullback q r₀ Λ` says: for a CF-normal input `x` and an image word `w`, the image
orbit's visits to `I_w` are — up to an exceptional set of frequency `ε` — matched by input times
at which the input orbit lies in an interval **determined by the last `k` input digits** and of
length at most `Λ γ(I_w)`.

That is exactly what the transducer supplies once its state is approximately a window function:
the interval is `(F v)⁻¹(I_w)` for the state `F v` attached to the window `v` (lengths bounded by
`distortion · γ(I_w)/η` per lap 49's `sub_le_of_image_le`), the exceptional times are the
`δ`-collar plus the bad positions of lap 48, and the clock matching input times to output
positions is the `rate ≈ 1` statement of `VandeheyS7Clock`.

## The theorem

`orbitWordBound_of_windowedPullback` : `WindowedPullback q r₀ Λ → OrbitWordBound q r₀
((1+8log2)/log2 · Λ)`.  Combined with `VandeheyS7Chain`, every remaining line of §7 Problem 1
runs through `WindowedPullback` and the cited `GaussACRigidity`.

## Guard rule

Content locator: the hypothesis is not vacuous — its conclusion at `V = ∅` would force the image
word count to be `o(p)`, which is false for `w` of positive mass, so a witness must produce real
windows.  Degenerate case: at `Λ` huge the interval constraint is free but the *predictability*
(one interval per window, `k` fixed before `p → ∞`) is the whole content.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The transducer hypothesis**, isolated.  See the module docstring. -/
def WindowedPullback (q r₀ Λ : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (k : ℕ) (V : Finset (List ℕ)) (A B : List ℕ → ℝ),
        (∀ v ∈ V, v.length = k) ∧ (∀ v ∈ V, v ≠ []) ∧ (∀ v ∈ V, ∀ e ∈ v, 1 ≤ e) ∧
        (∀ v ∈ V, 0 ≤ A v ∧ A v ≤ B v ∧ B v ≤ 1 ∧
          B v - A v ≤ Λ * (gaussMeasure (cfCylinder w)).toReal) ∧
        (∀ᶠ p : ℕ in atTop,
          blockCount (cfCylinder w) p (Int.fract (q * x + r₀))
            ≤ (∑ v ∈ V, blockCount (cfCylinder v ∩
                (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p (Int.fract x)) + ε * p)

/-- **The reduction.**  The ergodic side is finished: the crux is now one statement about the
machine. -/
theorem orbitWordBound_of_windowedPullback {q r₀ Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h : WindowedPullback q r₀ Λ) :
    OrbitWordBound q r₀ ((1 + 8 * Real.log 2) / Real.log 2 * Λ) := by
  classical
  intro x hx w hwpos ε hε
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
  obtain ⟨k, V, A, B, hVlen, hVne, hVpos, hAB, hcmp⟩ := h x hx w hwpos (ε / 2) (by linarith)
  have hL0 : 0 ≤ Λ * (gaussMeasure (cfCylinder w)).toReal := by positivity
  have hwin := windowHit_Ioo_le hirr hmem hx V hVlen hVne hVpos A B
    (fun v hv => ⟨(hAB v hv).1, (hAB v hv).2.1, (hAB v hv).2.2.1⟩)
    (fun v hv => (hAB v hv).2.2.2) hL0 (show (0:ℝ) < ε / 4 by linarith)
  filter_upwards [hcmp, hwin, eventually_gt_atTop 0] with p hp hpw hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  rw [div_le_iff₀ hppos] at hpw ⊢
  have hkey : (∑ v ∈ V, blockCount (cfCylinder v ∩
      (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p (Int.fract x))
      ≤ ((1 + 8 * Real.log 2) * (Λ * (gaussMeasure (cfCylinder w)).toReal / Real.log 2)
          + ε / 4) * p := hpw
  have hfinal : ((1 + 8 * Real.log 2) * (Λ * (gaussMeasure (cfCylinder w)).toReal / Real.log 2))
      = (1 + 8 * Real.log 2) / Real.log 2 * Λ * (gaussMeasure (cfCylinder w)).toReal := by
    field_simp
  rw [hfinal] at hkey
  nlinarith [hppos, hp, hkey]

/-! ## The end-to-end statements -/

/-- **`x ↦ φx`, from the transducer hypothesis.**  Every remaining line of §7 Problem 1 for the
multiplicative instance runs through `WindowedPullback`, the cited `GaussACRigidity`, and
tightness of the image. -/
theorem vandeheyS7_mul_phi_of_windowedPullback {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hrig : GaussACRigidity ((1 + 8 * Real.log 2) / Real.log 2 * Λ * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (Real.goldenRatio * x + 0)))
    (hwp : WindowedPullback Real.goldenRatio 0 Λ) : vandeheyS7_mul_phi := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine vandeheyS7_mul_phi_of_orbitWordBound ?_ hrig htight
    (orbitWordBound_of_windowedPullback hΛ hwp)
  positivity

/-- **`x ↦ x + φ`, likewise.** -/
theorem vandeheyS7_add_phi_of_windowedPullback {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hrig : GaussACRigidity ((1 + 8 * Real.log 2) / Real.log 2 * Λ * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (1 * x + Real.goldenRatio)))
    (hwp : WindowedPullback 1 Real.goldenRatio Λ) : vandeheyS7_add_phi := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine vandeheyS7_add_phi_of_orbitWordBound ?_ hrig htight
    (orbitWordBound_of_windowedPullback hΛ hwp)
  positivity


section Audit

#print axioms orbitWordBound_of_windowedPullback
#print axioms vandeheyS7_mul_phi_of_windowedPullback
#print axioms vandeheyS7_add_phi_of_windowedPullback

end Audit

end NormalNumbers.VandeheyS7
