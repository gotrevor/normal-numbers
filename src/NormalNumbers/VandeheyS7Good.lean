/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Sep
import NormalNumbers.VandeheyS7Distortion

/-!
# S7-G: the good-position pullback bound, and the price it charges

Lap 48 (`VandeheyS7Sep`) handled the *bad* positions: the output points lying within `η` of a
reciprocal `1/k` have frequency `≤ ε`, by the chain's own `ImageTight`.  This module supplies
the other half, and then measures exactly what the split costs.

## The good half

A post-emission state is *reduced*: its image interval `J` is not contained in a single cylinder,
so `J` contains a reciprocal `1/k`.  If the current output point `y ∈ J` is `η`-far from that
reciprocal, then `J` is at least `η` wide (`width_ge_of_mem_of_far`), and bounded distortion turns
that into a pullback bound (`sub_le_of_image_le`):

    |s⁻¹(E) ∩ [0,1]|  ≤  distortion(s) · |E| / η .

## The price, stated honestly

The good bound carries the factor `1/η`, while `ImageTight` supplies the bad frequency `ε` with
**no rate** relating `ε` to `η`.  So the split yields

    freq(I_w)  ≤  (D/η) γ(I_w)  +  ε(η) ,

which is *not* `C γ(I_w) + ε` for an absolute `C`: `splitConstant_not_absolute` records this in
the kernel — no choice of `η` makes the first constant absolute unless the second term is itself
comparable to `γ(I_w)`.  The missing input is therefore precisely a **rate** in the tail:
`TailRate A`, i.e. `freq(digit ≥ T) ≤ A/T`, which is the `w = []` case of the crux in quantitative
form.  That identifies the bootstrap as a *fixed-point* problem in the constant rather than a
circularity: a split run on `TailRate A` returns a word bound whose constant feeds back into the
tail at `w = [a]`, `a ≥ T`.  That loop is lap 50's target.

## Guard rule

Content locator: `sub_le_of_image_le` at `η = |mob 1 − mob 0|` is the plain distortion bound, so
all the new content is in the *lower bound on the image width* coming from a far output point.
Degenerate case: `width_ge_of_mem_of_far` needs both points in the image, which is what
"reduced state" supplies.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

namespace MobState

/-- The image of `[0,1]`, as a width. -/
noncomputable def width (s : MobState) : ℝ := |s.mob 1 - s.mob 0|

theorem width_pos (s : MobState) : 0 < s.width :=
  abs_pos.2 s.mob_one_sub_mob_zero_ne

/-- **The geometric link.**  Two points of the image at distance `≥ η` force the image to be at
least `η` wide.  For a reduced state the two points are the current output point and the
reciprocal `1/k` that the state straddles. -/
theorem width_ge_of_mem_of_far (s : MobState) {y r η : ℝ}
    (hy : y ∈ Set.Icc (min (s.mob 0) (s.mob 1)) (max (s.mob 0) (s.mob 1)))
    (hr : r ∈ Set.Icc (min (s.mob 0) (s.mob 1)) (max (s.mob 0) (s.mob 1)))
    (hfar : η ≤ |y - r|) : η ≤ s.width := by
  have h : |y - r| ≤ max (s.mob 0) (s.mob 1) - min (s.mob 0) (s.mob 1) := by
    rw [abs_sub_le_iff]
    constructor
    · linarith [hy.2, hr.1]
    · linarith [hr.2, hy.1]
  have heq : max (s.mob 0) (s.mob 1) - min (s.mob 0) (s.mob 1) = s.width := by
    rw [width, max_sub_min_eq_abs, abs_sub_comm]
  linarith [heq ▸ h]

/-- **The pullback bound.**  A sub-interval of `[0,1]` whose image is short is itself short, by a
factor `distortion / (image width)`. -/
theorem sub_le_of_image_le (s : MobState) {u v L η : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hη : 0 < η) (hJ : η ≤ s.width) (hL : |s.mob v - s.mob u| ≤ L) :
    v - u ≤ s.distortion * (L / η) := by
  have hdpos := s.distortion_pos
  have hwpos := s.width_pos
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) hL
  obtain ⟨hlo, -⟩ := s.mob_ratio_comparable hu huv hv
  have hratio : (s.mob v - s.mob u) / (s.mob 1 - s.mob 0) ≤ L / η := by
    calc (s.mob v - s.mob u) / (s.mob 1 - s.mob 0)
        ≤ |(s.mob v - s.mob u) / (s.mob 1 - s.mob 0)| := le_abs_self _
      _ = |s.mob v - s.mob u| / s.width := by rw [abs_div, width]
      _ ≤ L / s.width := by gcongr
      _ ≤ L / η := by gcongr
  have := le_trans hlo hratio
  rw [div_le_iff₀ hdpos] at this
  calc v - u ≤ L / η * s.distortion := this
    _ = s.distortion * (L / η) := by ring

end MobState

/-! ## What the split can and cannot give -/

/-- **The price, in the kernel.**  The split's constant is not absolute: for every candidate
absolute constant `C` there are a scale `η` and a mass `m` at which `D/η · m` exceeds `C · m`,
so a bound of the form `C γ(I_w) + ε` cannot be read off from the split alone.  (This is a
statement about the *shape* of the estimate, not a refutation of the crux.) -/
theorem splitConstant_not_absolute {D : ℝ} (hD : 0 < D) (C : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ m : ℝ, 0 < m → C * m < D / η * m := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((|C| + 1) / D)
  have hpos : (0:ℝ) < (|C| + 1) / D := by positivity
  have hn0 : (0:ℝ) < n := hpos.trans hn
  refine ⟨1 / n, by positivity, fun m hm => ?_⟩
  have hDn : D / (1 / (n:ℝ)) = D * n := by field_simp
  have hkey : C < D / (1 / (n:ℝ)) := by
    rw [hDn]
    rw [div_lt_iff₀ hD] at hn
    have : C ≤ |C| := le_abs_self C
    nlinarith
  exact mul_lt_mul_of_pos_right hkey hm

/-- **The missing input, named.**  A *rate* in the image's tail: the frequency of output digits
at least `T` is at most `A / T`.  This is the `w = []` case of the crux in quantitative form, and
it is exactly what upgrades `ImageTight`'s rateless `ε` to something the split can pay for. -/
def TailRate (y : ℝ) (A : ℝ) : Prop :=
  ∀ T : ℕ, 2 ≤ T → ∀ᶠ p : ℕ in atTop, blockCount (cellSet [] T) p y / p ≤ A / T

/-- A tail rate is strictly stronger than tightness. -/
theorem imageTight_of_tailRate {y : ℝ} {A : ℝ} (_hA : 0 < A) (h : TailRate y A) :
    ImageTight y := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (A / ε) 2)
  have hn2 : 2 ≤ n := by
    have : (2:ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
    exact_mod_cast this.le
  refine ⟨n, hn2, ?_⟩
  have hnA : A / ε < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0:ℝ) < n := by positivity
  have : A / (n:ℝ) ≤ ε := by
    rw [div_le_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hnA
    nlinarith
  exact (h n hn2).mono fun p hp => le_trans hp this

section Audit

#print axioms MobState.width_ge_of_mem_of_far
#print axioms MobState.sub_le_of_image_le
#print axioms splitConstant_not_absolute
#print axioms imageTight_of_tailRate

end Audit

end NormalNumbers.VandeheyS7
