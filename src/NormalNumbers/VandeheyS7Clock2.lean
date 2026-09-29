/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Mono
import NormalNumbers.VandeheyS7Tight3

/-!
# S7-C2: `AnchoredPullback` from a state clock

Laps 65–69 supplied every analytic ingredient of `AnchoredPullback`: the anchored hit principle,
the state's monotonicity, and the size bound `D·r/η`.  What remains is bookkeeping — matching
output positions to input times.  This module isolates exactly that, as `StateClock`, and proves
the reduction.

## The hypothesis

`StateClock q r₀ η K`: for a CF-normal input and a threshold `T`, there is a sequence of states
`s n` of image width `≥ η` and distortion `≤ K` such that the image orbit's visits to the tail cell
`cellSet [] T` are, up to frequency `ε`, matched by input times `n` at which
`Gⁿx` lies in the sublevel set `{t : s n .mob t < 1/T}`.

No location claim, no window, no measure: just "the output point at the matched time is the state
applied to the input point".  That is the defining property of a transducer.

## The theorem

`anchoredPullback_of_stateClock : StateClock q r₀ η K → AnchoredPullback q r₀ (2*K/η)`, hence
with lap 66 `ImageTight` for the image.  The thresholds are produced by `exists_thresholds`, which
converts lap 69's containment into the pair `(u,v)` that `anchoredHitCount` consumes.

## Guard rule

Content locator: `exists_thresholds` is where the anchoring is spent — for a target that is not
anchored no pair `(u,v)` exists, which is the content of `not_gappedHitPrinciple`.  Degenerate
case: when `2K/(Tη) ≥ 1` the thresholds degenerate to `u = 1`, `v = 0` and the bound is the trivial
`1`, as it must be.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

namespace MobState

/-- **Thresholds from the containment.**  Lap 69's anchored interval, in the `(u,v)` form
`anchoredHitCount` consumes. -/
theorem exists_thresholds (s : MobState) {r η c : ℝ} (hη : 0 < η) (hJ : η ≤ s.width)
    (hr : 0 ≤ r) (hc : s.distortion * (r / η) < c) :
    ∃ u v : ℝ, u ≤ c ∧ 1 - c ≤ v ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 → s.mob t < r → (t < u ∨ v < t) := by
  have hc0 : 0 ≤ c := by
    have : 0 ≤ s.distortion * (r / η) := by
      have := s.distortion_pos
      positivity
    linarith
  rcases mob_sublevel_subset s hη hJ hr with hleft | hright
  · refine ⟨c, 1, le_rfl, by linarith, ?_⟩
    intro t ht htr
    have := hleft (show t ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r} from ⟨ht, htr⟩)
    exact Or.inl (lt_of_le_of_lt this.2 hc)
  · refine ⟨0, 1 - c, hc0, le_rfl, ?_⟩
    intro t ht htr
    have := hright (show t ∈ {t | t ∈ Set.Ioo (0:ℝ) 1 ∧ s.mob t < r} from ⟨ht, htr⟩)
    exact Or.inr (by linarith [this.1])

end MobState

/-- **The clock hypothesis**, isolated: pure bookkeeping between output positions and input
times. -/
def StateClock (q r₀ η K : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ T : ℕ, 1 ≤ T → ∀ ε : ℝ, 0 < ε →
    ∃ s : ℕ → MobState,
      (∀ n, η ≤ (s n).width) ∧ (∀ n, (s n).distortion ≤ K) ∧
      ∀ᶠ p : ℕ in atTop,
        blockCount (cellSet [] T) p (Int.fract (q * x + r₀))
          ≤ ((Finset.range p).filter
              (fun n => (s n).mob (gaussMap^[n] (Int.fract x)) < 1 / (T:ℝ))).card + ε * p

/-- **The reduction.**  A state clock gives an anchored pullback, hence `ImageTight`. -/
theorem anchoredPullback_of_stateClock {q r₀ η K : ℝ} (hη : 0 < η) (hK : 0 < K)
    (h : StateClock q r₀ η K) : AnchoredPullback q r₀ (2 * K / η) := by
  classical
  intro x hx T hT ε hε
  obtain ⟨s, hwidth, hdist, hcmp⟩ := h x hx T hT ε hε
  have hT0 : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  set c₀ : ℝ := 2 * K / η / (T:ℝ) with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  set c : ℝ := min 1 c₀ with hcdef
  have hc0 : 0 ≤ c := le_min (by norm_num) hc₀pos.le
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcT : c ≤ 2 * K / η / (T:ℝ) := min_le_right _ _
  -- thresholds, state by state
  have hex : ∀ n : ℕ, ∃ u v : ℝ, u ≤ c ∧ 1 - c ≤ v ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 → (s n).mob t < 1 / (T:ℝ) → (t < u ∨ v < t) := by
    intro n
    rcases eq_or_lt_of_le hc1 with hone | hlt
    · exact ⟨1, 0, by linarith, by linarith, fun t ht _ => Or.inl (by linarith [ht.2])⟩
    · -- here `c = c₀` and the size bound applies
      have hcc : c = c₀ := by
        rcases min_cases 1 c₀ with ⟨h1, -⟩ | ⟨h1, -⟩
        · exfalso; rw [hcdef, h1] at hlt; linarith
        · rw [hcdef, h1]
      refine MobState.exists_thresholds (s n) hη (hwidth n) (by positivity) ?_
      have hd : (s n).distortion * (1 / (T:ℝ) / η) ≤ K * (1 / (T:ℝ) / η) := by
        have : (0:ℝ) ≤ 1 / (T:ℝ) / η := by positivity
        exact mul_le_mul_of_nonneg_right (hdist n) this
      have hlt2 : K * (1 / (T:ℝ) / η) < c₀ := by
        rw [hc₀]
        have e1 : K * (1 / (T:ℝ) / η) = K / ((T:ℝ) * η) := by field_simp
        have e2 : 2 * K / η / (T:ℝ) = 2 * K / ((T:ℝ) * η) := by
          field_simp
          try ring
        rw [e1, e2, div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < (T:ℝ) * η)]
        linarith
      rw [hcc]
      linarith
  choose u v hu hv hcover using hex
  refine ⟨u, v, c, hc0, hcT, hc1, hu, hv, ?_⟩
  filter_upwards [hcmp] with p hp
  refine le_trans hp ?_
  have hsub : ((Finset.range p).filter
      (fun n => (s n).mob (gaussMap^[n] (Int.fract x)) < 1 / (T:ℝ))).card
      ≤ ((Finset.range p).filter
        (fun n => gaussMap^[n] (Int.fract x) < u n ∨ v n < gaussMap^[n] (Int.fract x))).card := by
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have hirr : Irrational (Int.fract x) := by
      by_contra hcc
      exact NormalNumbers.Literature.not_isCFNormal_of_not_irrational hcc hx
    have hne : Int.fract x ≠ 0 := fun hzero => hirr ⟨0, by rw [hzero]; norm_num⟩
    have hmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hne), Int.fract_lt_one x⟩
    exact hcover n _ (irrational_orbit (Int.fract x) hirr hmem n).2 hn.2
  have : (((Finset.range p).filter
      (fun n => (s n).mob (gaussMap^[n] (Int.fract x)) < 1 / (T:ℝ))).card : ℝ)
      ≤ anchoredHitCount u v p (Int.fract x) := by
    rw [anchoredHitCount]
    exact_mod_cast hsub
  linarith

section Audit

#print axioms MobState.exists_thresholds
#print axioms anchoredPullback_of_stateClock

end Audit

end NormalNumbers.VandeheyS7
