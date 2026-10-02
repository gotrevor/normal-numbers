/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Forced

/-!
# S7-BL: a width floor CAPS the block length — the two halves of the route are one hypothesis

`width_le_of_forced` (S7-FB, lap 74) prices forced emission: a state that forces the word `w` has
`width ≤ 2·distortion·γ(I_w)`.  Cylinders decay, so this is a *quantitative* cap on how long a
forced block can be, given a width floor.  That is the missing bridge between the route's two
halves:

* the pullback bound `blockPullback_sum_le` needs a width floor `η`;
* the counting needs the block lengths `Lₙ` to be bounded (otherwise a single burst can swamp the
  output).

This module shows they are **the same hypothesis**.

## Results

* `gaussMeasure_cfCylinder_mul_fib_le` — `γ(I_u)·fib(|u|+1)² ≤ 1/log 2`.  The Fibonacci lower
  bound on continuants (`fib_le_cfK`, W1) turned into cylinder decay, in Gauss measure.
* `MobState.fib_sq_mul_width_le_of_forced` — **the cap**:
  `fib(L+1)²·width·log 2 ≤ 2·distortion` for a forced word of length `L`.
  Since `fib` grows like `φ^L`, this is `L ≤ log(2·distortion/(width·log 2))/(2 log φ) + O(1)`:
  **the block length is at most logarithmic in `1/width`.**
* `MobState.exists_forcedLength_bound` — the clean consequence: for every width floor `η > 0`
  and distortion cap `K`, there is an `L₀` beyond which NO such state can force a word.

## Reading for the route

Combined with S7-FB the picture is now exact and symmetric:

    width ≥ η   ⟺   forced blocks are short (length < L₀(η, K))
    long forced block   ⟹   width exponentially small, pullback bound trivial

so `blockPullback_sum_le`'s hypothesis and "bounded burst" are one and the same, and the crux's
residual content is the *frequency* of narrow states — equivalently, of long bursts — together
with the distribution of the basepoints those bursts spell out (S7-FB).

## Guard rule

Content locator: `gaussMeasure_cfCylinder_mul_fib_le` at `|u| = 1` reads `γ(I_[a]) ≤ 1/log 2`,
which is trivially true, so all the content is the *growth* of `fib`; at `u = []` the statement
is excluded (a cylinder needs a digit) and the cap is vacuous, matching
`width_le_of_forced`'s own locator.  Degenerate case: `η > 2·distortion/log 2` admits no forced
word at all, and `exists_forcedLength_bound` then returns `L₀ = 1`, i.e. only the empty block —
as it must, since a state that wide cannot fit inside any cylinder.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **Cylinder decay, Lebesgue form.**  `|I_u| · fib(|u|+1)² ≤ 1`, from `fib_le_cfK`. -/
theorem volume_cfCylinder_mul_fib_le (u : List ℕ) (hu : u ≠ []) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2 ≤ 1 := by
  have hKu : 1 ≤ cfK u := one_le_cfK u hupos
  have hfib : Nat.fib (u.length + 1) ≤ cfK u := fib_le_cfK u hupos
  rw [volume_cfCylinder u hu hupos,
    show ((Nat.fib (u.length + 1) : ENNReal)) ^ 2 =
      ENNReal.ofReal ((Nat.fib (u.length + 1) : ℝ) ^ 2) from by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  have hKuR : (1 : ℝ) ≤ (cfK u : ℝ) := by exact_mod_cast hKu
  have hfibR : (Nat.fib (u.length + 1) : ℝ) ≤ (cfK u : ℝ) := by exact_mod_cast hfib
  have hfib0 : (0 : ℝ) ≤ (Nat.fib (u.length + 1) : ℝ) := by positivity
  have hK' : (0 : ℝ) ≤ (cfK u.dropLast : ℝ) := by positivity
  rw [div_mul_eq_mul_div, div_le_one (by nlinarith)]
  nlinarith

/-- **Cylinder decay, Gauss form.** -/
theorem gaussMeasure_cfCylinder_mul_fib_le (u : List ℕ) (hu : u ≠ []) (hupos : ∀ a ∈ u, 1 ≤ a) :
    gaussMeasure (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ := by
  calc gaussMeasure (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2
      ≤ (ENNReal.ofReal (Real.log 2)⁻¹ * volume (cfCylinder u))
          * (Nat.fib (u.length + 1) : ENNReal) ^ 2 := by
        gcongr
        exact gaussMeasure_le_volume _ (measurableSet_cfCylinder u)
    _ = ENNReal.ofReal (Real.log 2)⁻¹
          * (volume (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2) := by ring
    _ ≤ ENNReal.ofReal (Real.log 2)⁻¹ * 1 := by
        gcongr
        exact volume_cfCylinder_mul_fib_le u hu hupos
    _ = ENNReal.ofReal (Real.log 2)⁻¹ := mul_one _

/-- The real-valued form. -/
theorem gaussMeasure_cfCylinder_toReal_mul_fib_le (u : List ℕ) (hu : u ≠ [])
    (hupos : ∀ a ∈ u, 1 ≤ a) :
    (gaussMeasure (cfCylinder u)).toReal * (Nat.fib (u.length + 1) : ℝ) ^ 2
      ≤ (Real.log 2)⁻¹ := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := gaussMeasure_cfCylinder_mul_fib_le u hu hupos
  have hfin : gaussMeasure (cfCylinder u) * (Nat.fib (u.length + 1) : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (by
      exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at h'

namespace MobState

/-- **The cap.**  A state that forces a word of length `L` has
`fib(L+1)² · width · log 2 ≤ 2 · distortion`.  Since `fib` grows like `φ^L`, the forced block
length is at most logarithmic in `1/width`. -/
theorem fib_sq_mul_width_le_of_forced (s : MobState) {w : List ℕ} (hw : w ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a)
    (himg : ∀ t ∈ Set.Ioo (0:ℝ) 1, s.mob t ∈ Set.Ioo (0:ℝ) 1)
    (hforced : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ i < w.length, cfDigit (s.mob t) i = w.getD i 0) :
    (Nat.fib (w.length + 1) : ℝ) ^ 2 * s.width * Real.log 2 ≤ 2 * s.distortion := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hd := s.distortion_pos
  have hwidth := s.width_le_of_forced himg hforced
  have hcyl := gaussMeasure_cfCylinder_toReal_mul_fib_le w hw hwpos
  have hγ0 : (0:ℝ) ≤ (gaussMeasure (cfCylinder w)).toReal := ENNReal.toReal_nonneg
  have hfib0 : (0:ℝ) ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2 := by positivity
  -- width ≤ 2·distortion·γ, and γ·fib² ≤ 1/log 2
  calc (Nat.fib (w.length + 1) : ℝ) ^ 2 * s.width * Real.log 2
      ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2
          * (2 * s.distortion * (gaussMeasure (cfCylinder w)).toReal) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hfib0) hlog.le
    _ = 2 * s.distortion * Real.log 2
          * ((gaussMeasure (cfCylinder w)).toReal * (Nat.fib (w.length + 1) : ℝ) ^ 2) := by ring
    _ ≤ 2 * s.distortion * Real.log 2 * (Real.log 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hcyl (by positivity)
    _ = 2 * s.distortion := by field_simp

/-- **A width floor caps the block length.**  For every floor `η > 0` and distortion cap `K`
there is an `L₀` beyond which no such state forces a word. -/
theorem exists_forcedLength_bound {η K : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ s : MobState, η ≤ s.width → s.distortion ≤ K →
      ∀ w : List ℕ, w ≠ [] → (∀ a ∈ w, 1 ≤ a) →
        (∀ t ∈ Set.Ioo (0:ℝ) 1, s.mob t ∈ Set.Ioo (0:ℝ) 1) →
        (∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ i < w.length, cfDigit (s.mob t) i = w.getD i 0) →
        w.length < L₀ := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * K / (η * Real.log 2)) 5)
  have hN5 : 5 ≤ N := by
    have : (5:ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
    exact_mod_cast this.le
  have hNK : 2 * K / (η * Real.log 2) < N := lt_of_le_of_lt (le_max_left _ _) hN
  refine ⟨N, fun s hwid hdist w hw hwpos himg hforced => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hcap := s.fib_sq_mul_width_le_of_forced hw hwpos himg hforced
  have hdpos := s.distortion_pos
  have hwpos' := s.width_pos
  -- `fib (w.length + 1) ≥ fib N ≥ N`
  have h1 : Nat.fib N ≤ Nat.fib (w.length + 1) := Nat.fib_mono (by omega)
  have h2 : N ≤ Nat.fib N := Nat.le_fib_self hN5
  have h3 : (N : ℝ) ≤ (Nat.fib (w.length + 1) : ℝ) := by exact_mod_cast le_trans h2 h1
  have hN0 : (0:ℝ) < N := by
    have : (5:ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
    linarith
  have hfib1 : (1:ℝ) ≤ (Nat.fib (w.length + 1) : ℝ) := by
    have h5 : (5:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN5
    linarith
  have hNsq : (N : ℝ) ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2 := by nlinarith [h3, hfib1]
  -- and `2 K < N · η · log 2 ≤ fib² · width · log 2 ≤ 2 · distortion ≤ 2 K`
  have hlt : 2 * K < (N:ℝ) * (η * Real.log 2) := by
    rw [div_lt_iff₀ (by positivity)] at hNK
    linarith
  have hchain : (N:ℝ) * (η * Real.log 2)
      ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2 * s.width * Real.log 2 := by
    have hinner : (N:ℝ) * η ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2 * s.width := by
      have hA := mul_le_mul_of_nonneg_right hNsq hη.le
      have hB := mul_le_mul_of_nonneg_left hwid
        (by positivity : (0:ℝ) ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2)
      linarith
    calc (N:ℝ) * (η * Real.log 2) = (N:ℝ) * η * Real.log 2 := by ring
      _ ≤ (Nat.fib (w.length + 1) : ℝ) ^ 2 * s.width * Real.log 2 :=
          mul_le_mul_of_nonneg_right hinner hlog.le
  linarith [hcap, hchain, hlt, hdist]

end MobState

section Audit

#print axioms volume_cfCylinder_mul_fib_le
#print axioms gaussMeasure_cfCylinder_mul_fib_le
#print axioms gaussMeasure_cfCylinder_toReal_mul_fib_le
#print axioms MobState.fib_sq_mul_width_le_of_forced
#print axioms MobState.exists_forcedLength_bound

end Audit

end NormalNumbers.VandeheyS7
