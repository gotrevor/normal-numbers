/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SeparatingTest
import NormalNumbers.PrimeLambertFour

/-!
# G4 disjunctivity: the dependency graph A–E as named propositions, and the wiring theorem

Brief: `~/personal/claude/knowledge/core/projects/normal-numbers-g4-disjunctivity-fable-handoff-2026-09-14.md`
(§4), draft `docs/prime-lambert-disjunctivity-draft.md` (§§4–9), fixed-base extension
`docs/prime-lambert-disjunctivity-fixed-base.md` (§5).

## Objects

* `Torus r = Fin r → UnitAddCircle` with Haar (`volume`, a probability measure);
  `torusChar q y = ∏ᵥ e(qᵥ yᵥ)` the characters; `fourierBox r D` the box `‖q‖∞ ≤ D`.
* `dAv y z = r⁻¹ ∑ᵥ dist(yᵥ, zᵥ)`, the **average coordinate torus distance** (draft §5); the
  brief's hard constraint is that this, not the product sup metric, is the metric of the test.
* `orbitClosure` — the closure in `UnitAddCircle` of the multiply-by-four orbit of `G₄`.
* A `Frame` packages one outer scale's data: grid size `K < J`, the integer tensor matrix
  `A : Matrix (Fin r) (Fin H) ℤ`, the coprime multipliers/offsets `d, t` giving the shifts
  `ρ_{α,j} = j d_α − t_α`, the sample progression `P`, the fixed translates `θ` (transport
  constant) and `γ` (frozen-prime vector), the small-prime vector `S n`, the resolution `η`, the
  tube fraction `ε`, and the Jackson degree `D`.
* `Frame.image = A(orbitClosureᴴ) + θ − γ` (the set `E` of draft §9) and
  `Frame.Ffull n = A · (∑_{j ≥ 1} 4⁻ʲ ω(n + ρ_{α,j}))_α − γ`, the exact transported vector.

## The named inputs (brief §4)

* `PropA` (exact affine transport, draft (4.3)): `Ffull n ∈ image` for every sample point.
* `PropB δ₁` (zonotope tube, draft (5.1)): Haar volume of the `εη`-tube around `image` in `dAv`
  is at most `δ₁`.
* `PropC δ₃` (uniform joint small-prime Fourier control, draft (8.1)): every nonzero character
  in the box has sample average of norm at most `δ₃`.
* `PropD δ₂` (three-range remainders + far tail, draft (7.3)): the sample average of
  `dAv(S n, Ffull n)` is at most `δ₂ · εη`.
* `PropJackson κ Λ` (product Jackson smoothing, draft (9.2)): a trigonometric polynomial with
  frequencies in the box approximates the clipped test within `κ` with nontrivial Fourier mass
  at most `Λ`.

## Proved here

* `finite_contradiction`: A ∧ B ∧ C ∧ D ∧ Jackson with budget `δ₁ + δ₂ + 2κ + Λδ₃ < 1` is
  impossible (draft §9).  This is the lap-1 checkpoint: a **conditional** wiring theorem.
* `isDisjunctive_four_of_frames`: if every omitted interval produces such a frame
  (`SeparatingFrameExists`), then `G₄` is disjunctive in base four, and hence in base two.

Nothing here proves any of A–E; the parameter schedule (§5 of the brief) that is supposed to
produce the frames lives in a separate module once the inputs are proved.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-! ### The torus, its characters, and the average metric -/

/-- The `r`-dimensional torus `(ℝ/ℤ)^r`. -/
abbrev Torus (r : ℕ) := Fin r → UnitAddCircle

instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

instance (r : ℕ) : IsProbabilityMeasure (volume : Measure (Torus r)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin r => (volume : Measure UnitAddCircle)))

/-- The character `y ↦ e(q · y)` on the torus. -/
noncomputable def torusChar {r : ℕ} (q : Fin r → ℤ) (y : Torus r) : ℂ :=
  ∏ ν, fourier (q ν) (y ν)

/-- The Fourier box `‖q‖∞ ≤ D`. -/
noncomputable def fourierBox (r D : ℕ) : Finset (Fin r → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(D : ℤ)) D

lemma mem_fourierBox {r D : ℕ} {q : Fin r → ℤ} :
    q ∈ fourierBox r D ↔ ∀ ν, |q ν| ≤ D := by
  simp [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

lemma zero_mem_fourierBox (r D : ℕ) : (0 : Fin r → ℤ) ∈ fourierBox r D := by
  rw [mem_fourierBox]; intro ν; simp

@[simp] lemma torusChar_zero {r : ℕ} (y : Torus r) : torusChar (0 : Fin r → ℤ) y = 1 := by
  simp [torusChar]

lemma continuous_torusChar {r : ℕ} (q : Fin r → ℤ) : Continuous (torusChar q) := by
  unfold torusChar; fun_prop

lemma norm_torusChar_le {r : ℕ} (q : Fin r → ℤ) (y : Torus r) : ‖torusChar q y‖ ≤ 1 := by
  unfold torusChar
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun ν _ => ?_)
  rw [fourier_apply]
  exact (Circle.norm_coe _).le

lemma integrable_torusChar {r : ℕ} (q : Fin r → ℤ) : Integrable (torusChar q) volume :=
  Integrable.of_bound (continuous_torusChar q).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_torusChar_le q))

/-- A nontrivial one-dimensional character integrates to zero. -/
lemma integral_fourier_eq_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x : UnitAddCircle, fourier n x = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  rw [Pi.single_apply, if_neg (Ne.symm hn)] at h
  unfold fourierCoeff at h
  simpa [fourier_zero, AddCircle.integral_haarAddCircle] using h

/-- **Orthogonality**: a nontrivial torus character integrates to zero against Haar. -/
theorem integral_torusChar_eq_zero {r : ℕ} {q : Fin r → ℤ} (hq : q ≠ 0) :
    ∫ y : Torus r, torusChar q y = 0 := by
  obtain ⟨ν₀, hν₀⟩ : ∃ ν, q ν ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (funext h)
  unfold torusChar
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (fun ν (x : UnitAddCircle) => fourier (q ν) x)]
  exact Finset.prod_eq_zero (Finset.mem_univ ν₀) (integral_fourier_eq_zero hν₀)

/-- The average coordinate torus distance `r⁻¹ ∑ᵥ dist(yᵥ, zᵥ)`. -/
noncomputable def dAv {r : ℕ} (y z : Torus r) : ℝ := (∑ ν, dist (y ν) (z ν)) / r

lemma dAv_nonneg {r : ℕ} (y z : Torus r) : 0 ≤ dAv y z := by
  unfold dAv
  exact div_nonneg (Finset.sum_nonneg fun _ _ => dist_nonneg) (Nat.cast_nonneg r)

lemma dAv_triangle {r : ℕ} (x y z : Torus r) : dAv x z ≤ dAv x y + dAv y z := by
  unfold dAv
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg r)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun ν _ => dist_triangle _ _ _

/-- The average metric is dominated by the product sup metric. -/
lemma dAv_le_dist {r : ℕ} (y z : Torus r) : dAv y z ≤ dist y z := by
  unfold dAv
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  calc (∑ ν, dist (y ν) (z ν)) / r ≤ (∑ _ν : Fin r, dist y z) / r := by
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg r)
        exact Finset.sum_le_sum fun ν _ => dist_le_pi_dist y z ν
    _ = dist y z := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
        field_simp

/-- Average distance from a point to a set. -/
noncomputable def dAvSet {r : ℕ} (y : Torus r) (E : Set (Torus r)) : ℝ := sInf (dAv y '' E)

lemma dAvSet_bddBelow {r : ℕ} (y : Torus r) (E : Set (Torus r)) : BddBelow (dAv y '' E) :=
  ⟨0, by rintro _ ⟨z, _, rfl⟩; exact dAv_nonneg y z⟩

lemma dAvSet_le {r : ℕ} {y z : Torus r} {E : Set (Torus r)} (hz : z ∈ E) :
    dAvSet y E ≤ dAv y z :=
  csInf_le (dAvSet_bddBelow y E) (Set.mem_image_of_mem _ hz)

lemma dAvSet_nonneg {r : ℕ} (y : Torus r) (E : Set (Torus r)) : 0 ≤ dAvSet y E := by
  unfold dAvSet
  rcases E.eq_empty_or_nonempty with h | h
  · simp [h]
  · exact le_csInf (h.image _) (by rintro _ ⟨z, _, rfl⟩; exact dAv_nonneg y z)

lemma dAvSet_sub_le {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) (y y' : Torus r) :
    dAvSet y E - dAv y y' ≤ dAvSet y' E := by
  unfold dAvSet
  refine le_csInf (hE.image _) ?_
  rintro _ ⟨z, hz, rfl⟩
  have := dAvSet_le (y := y) hz
  have := dAv_triangle y y' z
  unfold dAvSet at *
  linarith

/-- `y ↦ dAvSet y E` is `1`-Lipschitz for the product sup metric. -/
lemma lipschitz_dAvSet {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) :
    LipschitzWith 1 (fun y : Torus r => dAvSet y E) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_le_iff]
  have h1 := dAvSet_sub_le hE y y'
  have h2 := dAvSet_sub_le hE y' y
  have h3 := dAv_le_dist y y'
  have h4 := dAv_le_dist y' y
  rw [dist_comm] at h4
  constructor <;> linarith

lemma continuous_dAvSet {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) :
    Continuous (fun y : Torus r => dAvSet y E) :=
  (lipschitz_dAvSet hE).continuous

/-- The clipped normalized distance test `min(1, dAv(y, E)/ρ)` (draft (9.1)). -/
noncomputable def clipTest {r : ℕ} (E : Set (Torus r)) (ρ : ℝ) (y : Torus r) : ℝ :=
  min 1 (dAvSet y E / ρ)

lemma clipTest_nonneg {r : ℕ} (E : Set (Torus r)) {ρ : ℝ} (hρ : 0 < ρ) (y : Torus r) :
    0 ≤ clipTest E ρ y :=
  le_min zero_le_one (div_nonneg (dAvSet_nonneg y E) hρ.le)

lemma clipTest_le_one {r : ℕ} (E : Set (Torus r)) (ρ : ℝ) (y : Torus r) :
    clipTest E ρ y ≤ 1 := min_le_left _ _

lemma clipTest_le_dAv {r : ℕ} {E : Set (Torus r)} {ρ : ℝ} (hρ : 0 < ρ) {y z : Torus r}
    (hz : z ∈ E) : clipTest E ρ y ≤ dAv y z / ρ :=
  (min_le_right _ _).trans (div_le_div_of_nonneg_right (dAvSet_le hz) hρ.le)

lemma clipTest_eq_one {r : ℕ} {E : Set (Torus r)} {ρ : ℝ} (hρ : 0 < ρ) {y : Torus r}
    (hy : ρ < dAvSet y E) : clipTest E ρ y = 1 := by
  unfold clipTest
  rw [min_eq_left]
  rw [le_div_iff₀ hρ, one_mul]
  exact hy.le

lemma continuous_clipTest {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) (ρ : ℝ) :
    Continuous (clipTest E ρ) :=
  continuous_const.min ((continuous_dAvSet hE).div_const ρ)

lemma integrable_clipTest {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (clipTest E ρ) (volume : Measure (Torus r)) :=
  Integrable.of_bound (continuous_clipTest hE ρ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (clipTest_nonneg E hρ y)]
      exact clipTest_le_one E ρ y)

/-- The `ρ`-tube around `E` in the average metric. -/
def tube {r : ℕ} (E : Set (Torus r)) (ρ : ℝ) : Set (Torus r) := {y | dAvSet y E ≤ ρ}

lemma measurableSet_tube {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty) (ρ : ℝ) :
    MeasurableSet (tube E ρ) :=
  (isClosed_le (continuous_dAvSet hE) continuous_const).measurableSet

/-- **Haar side of the test** (draft §9): a small tube forces a large Haar average. -/
theorem one_sub_tube_le_integral_clipTest {r : ℕ} {E : Set (Torus r)} (hE : E.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) :
    1 - (volume (tube E ρ)).toReal ≤ ∫ y, clipTest E ρ y := by
  have hmeas := measurableSet_tube hE ρ
  have hind : ∫ y, (tube E ρ)ᶜ.indicator (1 : Torus r → ℝ) y = (volume (tube E ρ)ᶜ).toReal :=
    integral_indicator_one hmeas.compl
  have hcompl : (volume (tube E ρ)ᶜ).toReal = 1 - (volume (tube E ρ)).toReal := by
    rw [measure_compl hmeas (measure_ne_top _ _), measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [← hcompl, ← hind]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hmeas.compl)
    (integrable_clipTest hE hρ) fun y => ?_
  by_cases hy : y ∈ tube E ρ
  · simp only [Set.indicator, Set.mem_compl_iff, hy, not_true_eq_false, if_false]
    exact clipTest_nonneg E hρ y
  · simp only [Set.indicator, Set.mem_compl_iff, hy, not_false_eq_true, if_true, Pi.one_apply]
    rw [clipTest_eq_one hρ]
    simpa [tube] using hy

/-! ### The arithmetic objects -/

/-- The closure of the multiply-by-`b` orbit of `∑ ω(n)/bⁿ` in the circle.  At `b = 4` this is
the base-four orbit closure of `G₄` (`primeLambertFour = primeLambertAtBase 4` by definition). -/
noncomputable def orbitClosure (bb : ℕ) : Set UnitAddCircle :=
  closure (Set.range fun n : ℕ => ((orbit bb (primeLambertAtBase bb) n : ℝ) : UnitAddCircle))

lemma orbitClosure_nonempty (bb : ℕ) : (orbitClosure bb).Nonempty :=
  (Set.range_nonempty _).closure

/-- An integer matrix acting on a torus vector: `(A x)_ν = ∑_α A_{να} • x_α`. -/
noncomputable def mulVecT {r H : ℕ} (A : Matrix (Fin r) (Fin H) ℤ) (x : Fin H → UnitAddCircle) :
    Torus r :=
  fun ν => ∑ α, A ν α • x α

/-- One outer scale's worth of data for the candidate proof.  See the module docstring. -/
structure Frame where
  /-- the integer base `b ≥ 2` of the constant `∑ ω(n)/bⁿ` under test -/
  bse : ℕ
  hbse : 2 ≤ bse
  /-- number of cancelled layers -/
  K : ℕ
  /-- truncation depth of the retained layers -/
  J : ℕ
  /-- number of output coordinates (`r = s^K`) -/
  r : ℕ
  /-- number of grid atoms (`H = (s+1)^K`) -/
  H : ℕ
  /-- the tensor adjacent-difference matrix `D_s^{⊗K}` -/
  A : Matrix (Fin r) (Fin H) ℤ
  /-- pairwise coprime multipliers `d_α` -/
  d : Fin H → ℕ
  /-- offsets `t_α` -/
  t : Fin H → ℕ
  ht : ∀ α, t α < d α
  /-- the sample progression -/
  P : Finset ℕ
  hP : P.Nonempty
  /-- transport translate `θ` -/
  θ : Torus r
  /-- frozen-prime translate `γ` -/
  γ : Torus r
  /-- the small-prime vector `S(n)` -/
  S : ℕ → Torus r
  /-- spatial resolution `η` -/
  η : ℝ
  hη : 0 < η
  /-- tube fraction `ε` -/
  ε : ℝ
  hε : 0 < ε
  /-- Jackson degree `D` -/
  D : ℕ

namespace Frame

variable (fr : Frame)

/-- The surviving shift `ρ_{α,j} = j d_α − t_α`. -/
def shift (α : Fin fr.H) (j : ℕ) : ℕ := j * fr.d α - fr.t α

/-- The image set `E = A(Cᴴ) + θ − γ` of draft §9. -/
def image : Set (Torus fr.r) :=
  {y | ∃ x : Fin fr.H → UnitAddCircle, (∀ α, x α ∈ orbitClosure fr.bse) ∧
    y = mulVecT fr.A x + fr.θ - fr.γ}

lemma image_nonempty : fr.image.Nonempty := by
  obtain ⟨c, hc⟩ := orbitClosure_nonempty fr.bse
  exact ⟨_, fun _ => c, fun _ => hc, rfl⟩

/-- The exact transported vector `(A · (∑_{j ≥ 1} b⁻ʲ ω(n + ρ_{α,j}))_α) − γ` (draft (4.2)–(4.3)),
read modulo one. -/
noncomputable def Ffull (n : ℕ) : Torus fr.r :=
  fun ν =>
    (((∑ α, (fr.A ν α : ℝ)
        * ∑' j : ℕ, omegaR (n + fr.shift α (j + 1)) / (fr.bse : ℝ) ^ (j + 1) : ℝ) :
        UnitAddCircle)) - fr.γ ν

/-- The resolution of the test: `εη`. -/
noncomputable def res : ℝ := fr.ε * fr.η

lemma res_pos : 0 < fr.res := mul_pos fr.hε fr.hη

/-- The clipped separating test `f` of draft (9.1). -/
noncomputable def test : Torus fr.r → ℝ := clipTest fr.image fr.res

/-! ### The named inputs A–E -/

/-- **A** (exact affine Lambert transport, draft (4.3)): on the sample progression, the exact
transported vector lies in `A(Cᴴ) + θ − γ`. -/
def PropA : Prop := ∀ n ∈ fr.P, fr.Ffull n ∈ fr.image

/-- **B** (zonotope tube volume, draft (5.1)): the `εη`-tube around the image, in the average
metric, has Haar volume at most `δ₁`. -/
def PropB (δ₁ : ℝ) : Prop := (volume (tube fr.image fr.res)).toReal ≤ δ₁

/-- **C** (uniform joint small-prime Fourier control, draft (8.1)): every nonzero character in
the Fourier box has sample average of norm at most `δ₃`, simultaneously. -/
def PropC (δ₃ : ℝ) : Prop :=
  ∀ q ∈ fourierBox fr.r fr.D, q ≠ 0 → ‖sampleAvg fr.P fr.S (torusChar q)‖ ≤ δ₃

/-- **D** (three-range remainders and far tail, draft (7.3)): the sample average of the average
coordinate distance between the small-prime vector and the exact transported vector is at most
`δ₂ · εη`. -/
def PropD (δ₂ : ℝ) : Prop :=
  (fr.P.card : ℝ)⁻¹ * ∑ n ∈ fr.P, dAv (fr.S n) (fr.Ffull n) ≤ δ₂ * fr.res

/-- **Jackson** (draft (9.2)): a trigonometric polynomial with frequencies in the box
approximates the clipped test uniformly within `κ`, with nontrivial Fourier mass at most `Λ`
(the draft's `Λ = (2D+1)^r`). -/
def PropJackson (κ Λ : ℝ) : Prop :=
  ∃ c : (Fin fr.r → ℤ) → ℂ,
    (∀ y, ‖(∑ q ∈ fourierBox fr.r fr.D, c q * torusChar q y) - (fr.test y : ℂ)‖ ≤ κ) ∧
    ∑ q ∈ (fourierBox fr.r fr.D).erase 0, ‖c q‖ ≤ Λ

/-- Sample side of the test (draft (7.3) ⇒ `𝔼 f(S) = o(1)`): A and D give the bound. -/
theorem sampleAvg_test_le {δ₂ : ℝ} (hA : fr.PropA) (hD : fr.PropD δ₂) :
    sampleAvg fr.P fr.S fr.test ≤ δ₂ := by
  have hres := fr.res_pos
  unfold sampleAvg
  rw [smul_eq_mul]
  calc (fr.P.card : ℝ)⁻¹ * ∑ n ∈ fr.P, fr.test (fr.S n)
      ≤ (fr.P.card : ℝ)⁻¹ * ∑ n ∈ fr.P, dAv (fr.S n) (fr.Ffull n) / fr.res := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity)
        exact clipTest_le_dAv hres (hA n hn)
    _ = ((fr.P.card : ℝ)⁻¹ * ∑ n ∈ fr.P, dAv (fr.S n) (fr.Ffull n)) / fr.res := by
        rw [← Finset.sum_div, mul_div_assoc]
    _ ≤ (δ₂ * fr.res) / fr.res := div_le_div_of_nonneg_right hD hres.le
    _ = δ₂ := by field_simp

/-- Haar side of the test (draft (5.1) ⇒ `∫ f = 1 − o(1)`): B gives the bound. -/
theorem one_sub_le_integral_test {δ₁ : ℝ} (hB : fr.PropB δ₁) :
    1 - δ₁ ≤ ∫ y, fr.test y := by
  have := one_sub_tube_le_integral_clipTest fr.image_nonempty fr.res_pos
  unfold PropB at hB
  unfold test
  linarith

/-- **The finite separating-test contradiction** (draft §9, brief §4E), conditional on the named
inputs A–D and Jackson smoothing, with the explicit budget `δ₁ + δ₂ + 2κ + Λδ₃ < 1`. -/
theorem finite_contradiction {δ₁ δ₂ δ₃ κ Λ : ℝ}
    (hA : fr.PropA) (hB : fr.PropB δ₁) (hC : fr.PropC δ₃) (hD : fr.PropD δ₂)
    (hJ : fr.PropJackson κ Λ) (hδ₃ : 0 ≤ δ₃)
    (h_closed : δ₁ + δ₂ + 2 * κ + Λ * δ₃ < 1) : False := by
  obtain ⟨c, h_approx, h_budget⟩ := hJ
  exact separating_test_contradiction (μ := (volume : Measure (Torus fr.r)))
    (fourierBox fr.r fr.D) 0 (zero_mem_fourierBox _ _) torusChar
    torusChar_zero (fun q _ => integrable_torusChar q)
    (fun q _ hq => integral_torusChar_eq_zero hq)
    fr.P fr.hP fr.S fr.test (integrable_clipTest fr.image_nonempty fr.res_pos)
    c κ h_approx (fr.one_sub_le_integral_test hB) (fr.sampleAvg_test_le hA hD)
    hC h_budget hδ₃ h_closed

end Frame

/-- **The candidate's global hypothesis.**  Every interval omitted by the base-four orbit of `G₄`
yields one frame whose inputs A–D and Jackson smoothing hold with a closed budget.  The
parameter schedule of brief §5 is what is supposed to produce it; the omitted interval enters
through `orbitClosure` inside `PropB` (the dimension deficit of draft (4.4)). -/
def SeparatingFrameExists (bb : ℕ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    (∀ n, orbit bb (primeLambertAtBase bb) n ∉ Set.Ico a c) →
    ∃ (fr : Frame) (δ₁ δ₂ δ₃ κ Λ : ℝ),
      fr.PropA ∧ fr.PropB δ₁ ∧ fr.PropC δ₃ ∧ fr.PropD δ₂ ∧ fr.PropJackson κ Λ ∧
      0 ≤ δ₃ ∧ δ₁ + δ₂ + 2 * κ + Λ * δ₃ < 1

/-- **Conditional headline (base four).**  Not the endpoint: `SeparatingFrameExists` is the
unproved candidate content. -/
theorem isDisjunctive_of_frames {bb : ℕ} (h : SeparatingFrameExists bb) :
    IsDisjunctive bb (primeLambertAtBase bb) := by
  intro a c ha hac hc
  by_contra hno
  push Not at hno
  obtain ⟨fr, δ₁, δ₂, δ₃, κ, Λ, hA, hB, hC, hD, hJ, hδ₃, hbud⟩ := h a c ha hac hc hno
  exact fr.finite_contradiction hA hB hC hD hJ hδ₃ hbud

/-- **Conditional headline at base four** — the `b = 4` instance of `isDisjunctive_of_frames`
(`primeLambertFour = primeLambertAtBase 4` by definition). -/
theorem isDisjunctive_four_of_frames (h : SeparatingFrameExists 4) :
    IsDisjunctive 4 primeLambertFour :=
  isDisjunctive_of_frames h

/-- **Conditional headline (base two).** -/
theorem isDisjunctive_two_of_frames (h : SeparatingFrameExists 4) :
    IsDisjunctive 2 primeLambertFour :=
  isDisjunctive_two_of_four (isDisjunctive_four_of_frames h)

end NormalNumbers.G4
