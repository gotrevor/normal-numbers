/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Good
import NormalNumbers.VandeheyOutputFreq
import NormalNumbers.VandeheyS7Tight2

/-!
# S7-W: the predictable-hit principle HOLDS for window predictors on a CF-normal point

`VandeheyS7Predict.not_predictableHitPrinciple` refutes the soft principle "predictable + small +
correct marginals ⇒ few hits" for arbitrary sequences.  This module proves the *positive*
counterpart, which is what the transducer route actually needs: when the predictor reads a
**finite window** of the input digits and the point is genuinely CF-normal, the hit frequency IS
bounded by an absolute constant times the target's Gauss mass.

    freq{ n : x_n…x_{n+k−1} = v  and  x_{n+k}… ∈ I_{u(v)} }  ≤  8 log 2 · max_v γ(I_{u(v)}) .

Two ingredients, both already in the repo:

* **quasi-multiplicativity** (`gaussMeasure_append_le`, new here): `γ(I_{v++u}) ≤ 8 log 2 ·
  γ(I_v) γ(I_u)`, from Bourgain–Yoccoz-style `volume_cylinder_append_le` and the two-sided
  Gauss-density window;
* **CF-normality itself**: the hit set for the window `v` is the cylinder `I_{v ++ u(v)}`, whose
  frequency is exactly `γ(I_{v++u(v)})` (`blockCount_freq_of_isCFNormal`), and the masses `γ(I_v)`
  over a same-length family sum to at most `1` (`sum_gaussMeasure_le_one_of_length`).

## Why this matters for the crux

The crux's target `s_n⁻¹(I_w)` is predictable but **not** a window function
(`no_window_function`).  What this module establishes is that the *only* obstruction left on the
distortion route is the approximation of the state by a finite window: if the state at time `n`
were determined, to accuracy `ε`, by the last `k` input digits, the theorem below would give
`OrbitWordBound` with the absolute constant `8 log 2` — no `1/η` factor, no tail rate, no
bootstrap.  Uniform loss of memory (`hdist_runWord_le`, rate `(3−2√2)^{k/2}`) is the mechanism
that would supply that approximation; the open point is that it controls the image DIAMETER while
the target needs its LOCATION.

## Guard rule

Content locator: `gaussMeasure_append_le` at `v = u` is the quasi-Bernoulli statement itself;
`windowHit_le` at `k = 0` (the one-element family `V = {[]}`) degenerates to the plain cylinder
frequency, so all its content is in the *uniformity over the window*.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers NormalNumbers.VandeheyOut

open scoped ENNReal

/-! ## Quasi-multiplicativity of the Gauss measure on cylinders -/

private lemma log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma volume_cfCylinder_ne_top (w : List ℕ) : volume (cfCylinder w) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (cfCylinder_subset_Ioo w))
  rw [Real.volume_Ioo]
  simp

/-- Gauss mass is at most `1/log 2` times Lebesgue measure, in real form. -/
theorem gaussMeasure_toReal_le (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s ≠ ⊤) :
    (gaussMeasure s).toReal ≤ (Real.log 2)⁻¹ * (volume s).toReal := by
  have h := gaussMeasure_le_volume s hs
  have hne : ENNReal.ofReal (Real.log 2)⁻¹ * volume s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have := ENNReal.toReal_le_toReal (measure_ne_top gaussMeasure s) hne |>.2 h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

/-- Lebesgue measure is at most `2 log 2` times Gauss mass on `(0,1)`, in real form. -/
theorem volume_toReal_le (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioo (0:ℝ) 1)
    (hfin : volume s ≠ ⊤) :
    (volume s).toReal ≤ 2 * Real.log 2 * (gaussMeasure s).toReal := by
  have h := volume_le_gaussMeasure s hs hsub
  have hne : ENNReal.ofReal (2 * Real.log 2)⁻¹ * volume s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have h' := ENNReal.toReal_le_toReal hne (measure_ne_top gaussMeasure s) |>.2 h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
  have h2 : (0:ℝ) < 2 * Real.log 2 := by linarith [log_two_pos]
  rw [inv_mul_le_iff₀ h2] at h'
  linarith

/-- **Quasi-multiplicativity.**  `γ(I_{v++u}) ≤ 8 log 2 · γ(I_v) · γ(I_u)`. -/
theorem gaussMeasure_append_le (v u : List ℕ) (hv : v ≠ []) (hu : u ≠ [])
    (hvpos : ∀ a ∈ v, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    (gaussMeasure (cfCylinder (v ++ u))).toReal ≤
      8 * Real.log 2 * ((gaussMeasure (cfCylinder v)).toReal *
        (gaussMeasure (cfCylinder u)).toReal) := by
  have hlog := log_two_pos
  have hvol := volume_cylinder_append_le v u hv hu hvpos hupos
  have hvolR : (volume (cfCylinder (v ++ u))).toReal ≤
      2 * ((volume (cfCylinder v)).toReal * (volume (cfCylinder u)).toReal) := by
    have hne : (2:ℝ≥0∞) * (volume (cfCylinder v) * volume (cfCylinder u)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp)
        (ENNReal.mul_ne_top (volume_cfCylinder_ne_top v) (volume_cfCylinder_ne_top u))
    have := ENNReal.toReal_le_toReal (volume_cfCylinder_ne_top (v ++ u)) hne |>.2 hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  have h1 := gaussMeasure_toReal_le (cfCylinder (v ++ u)) (measurableSet_cfCylinder _)
    (volume_cfCylinder_ne_top _)
  have h2 := volume_toReal_le (cfCylinder v) (measurableSet_cfCylinder _)
    (cfCylinder_subset_Ioo v) (volume_cfCylinder_ne_top _)
  have h3 := volume_toReal_le (cfCylinder u) (measurableSet_cfCylinder _)
    (cfCylinder_subset_Ioo u) (volume_cfCylinder_ne_top _)
  have hv0 : (0:ℝ) ≤ (volume (cfCylinder v)).toReal := ENNReal.toReal_nonneg
  have hu0 : (0:ℝ) ≤ (volume (cfCylinder u)).toReal := ENNReal.toReal_nonneg
  have hg0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
  have hgu0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder u)).toReal := ENNReal.toReal_nonneg
  have hprod : (volume (cfCylinder v)).toReal * (volume (cfCylinder u)).toReal
      ≤ (2 * Real.log 2 * (gaussMeasure (cfCylinder v)).toReal) *
        (2 * Real.log 2 * (gaussMeasure (cfCylinder u)).toReal) :=
    mul_le_mul h2 h3 hu0 (by positivity)
  have hfinal : (gaussMeasure (cfCylinder (v ++ u))).toReal
      ≤ (Real.log 2)⁻¹ * (2 * ((2 * Real.log 2 * (gaussMeasure (cfCylinder v)).toReal) *
          (2 * Real.log 2 * (gaussMeasure (cfCylinder u)).toReal))) := by
    refine h1.trans ?_
    have hinv : (0:ℝ) ≤ (Real.log 2)⁻¹ := by positivity
    have := hvolR.trans (by nlinarith : (2:ℝ) * ((volume (cfCylinder v)).toReal *
      (volume (cfCylinder u)).toReal) ≤ 2 * ((2 * Real.log 2 *
        (gaussMeasure (cfCylinder v)).toReal) * (2 * Real.log 2 *
          (gaussMeasure (cfCylinder u)).toReal)))
    exact mul_le_mul_of_nonneg_left this hinv
  have hrw : (Real.log 2)⁻¹ * (2 * ((2 * Real.log 2 * (gaussMeasure (cfCylinder v)).toReal) *
      (2 * Real.log 2 * (gaussMeasure (cfCylinder u)).toReal)))
      = 8 * Real.log 2 * ((gaussMeasure (cfCylinder v)).toReal *
        (gaussMeasure (cfCylinder u)).toReal) := by
    field_simp
    ring
  linarith [hrw ▸ hfinal]

/-! ## The window-hit theorem -/

/-- **The predictable-hit principle for window predictors.**  For a CF-normal `x`, a finite family
`V` of length-`k` windows and a target word `u v` attached to each, the total visit frequency of
the hit cylinders `I_{v ++ u v}` is eventually at most `8 log 2 · m + ε`, where `m` bounds the
targets' Gauss masses.  The constant is ABSOLUTE: no dependence on `k`, on `V`, or on the
targets' position. -/
theorem windowHit_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {k : ℕ} (V : Finset (List ℕ))
    (hVlen : ∀ v ∈ V, v.length = k) (hVne : ∀ v ∈ V, v ≠ [])
    (hVpos : ∀ v ∈ V, ∀ a ∈ v, 1 ≤ a)
    (u : List ℕ → List ℕ) (hune : ∀ v ∈ V, u v ≠ []) (hupos : ∀ v ∈ V, ∀ a ∈ u v, 1 ≤ a)
    {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ v ∈ V, (gaussMeasure (cfCylinder (u v))).toReal ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      (∑ v ∈ V, blockCount (cfCylinder (v ++ u v)) p x) / (p:ℝ) ≤ 8 * Real.log 2 * m + ε := by
  classical
  have horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1 :=
    fun j => (irrational_orbit x hirr hmem j).2
  -- each hit cylinder has the right frequency
  have hfreq : ∀ v ∈ V, Tendsto (fun p => blockCount (cfCylinder (v ++ u v)) p x / (p:ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder (v ++ u v))).toReal) := by
    intro v hv
    refine blockCount_freq_of_isCFNormal horb hx _ (by simp [hVne v hv]) ?_
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hVpos v hv a h
    · exact hupos v hv a h
  have hsum : Tendsto (fun p => (∑ v ∈ V, blockCount (cfCylinder (v ++ u v)) p x) / (p:ℝ)) atTop
      (nhds (∑ v ∈ V, (gaussMeasure (cfCylinder (v ++ u v))).toReal)) := by
    have := tendsto_finsetSum V (fun v hv => hfreq v hv)
    simpa [Finset.sum_div] using this
  -- and the masses are small
  have hmass : (∑ v ∈ V, (gaussMeasure (cfCylinder (v ++ u v))).toReal) ≤ 8 * Real.log 2 * m := by
    have hstep : ∀ v ∈ V, (gaussMeasure (cfCylinder (v ++ u v))).toReal ≤
        8 * Real.log 2 * m * (gaussMeasure (cfCylinder v)).toReal := by
      intro v hv
      have h := gaussMeasure_append_le v (u v) (hVne v hv) (hune v hv) (hVpos v hv) (hupos v hv)
      have hg0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
      have hlog := log_two_pos
      have hmul : (gaussMeasure (cfCylinder v)).toReal *
          (gaussMeasure (cfCylinder (u v))).toReal
          ≤ (gaussMeasure (cfCylinder v)).toReal * m :=
        mul_le_mul_of_nonneg_left (hm v hv) hg0
      have hscale := mul_le_mul_of_nonneg_left hmul
        (by positivity : (0:ℝ) ≤ 8 * Real.log 2)
      calc (gaussMeasure (cfCylinder (v ++ u v))).toReal
          ≤ 8 * Real.log 2 * ((gaussMeasure (cfCylinder v)).toReal *
              (gaussMeasure (cfCylinder (u v))).toReal) := h
        _ ≤ 8 * Real.log 2 * ((gaussMeasure (cfCylinder v)).toReal * m) := hscale
        _ = 8 * Real.log 2 * m * (gaussMeasure (cfCylinder v)).toReal := by ring
    calc (∑ v ∈ V, (gaussMeasure (cfCylinder (v ++ u v))).toReal)
        ≤ ∑ v ∈ V, 8 * Real.log 2 * m * (gaussMeasure (cfCylinder v)).toReal :=
          Finset.sum_le_sum hstep
      _ = 8 * Real.log 2 * m * ∑ v ∈ V, (gaussMeasure (cfCylinder v)).toReal := by
          rw [Finset.mul_sum]
      _ ≤ 8 * Real.log 2 * m * 1 := by
          have hle := sum_gaussMeasure_le_one_of_length (m := k) V hVlen
          have hc : (0:ℝ) ≤ 8 * Real.log 2 * m := by
            have := log_two_pos; positivity
          exact mul_le_mul_of_nonneg_left hle hc
      _ = 8 * Real.log 2 * m := by ring
  filter_upwards [hsum.eventually (eventually_lt_nhds
    (show (∑ v ∈ V, (gaussMeasure (cfCylinder (v ++ u v))).toReal) <
      (∑ v ∈ V, (gaussMeasure (cfCylinder (v ++ u v))).toReal) + ε by linarith))] with p hp
  linarith

section Audit

#print axioms gaussMeasure_append_le
#print axioms windowHit_le

end Audit

end NormalNumbers.VandeheyS7
