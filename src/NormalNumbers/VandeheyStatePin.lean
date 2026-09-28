/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyRenyi
import NormalNumbers.CFPsiPin
import NormalNumbers.VandeheyWeightTV

/-!
# The state-refined transfer operator — the crux of Vandehey 2017 Theorem 1.1

`PENDING_WORK.md` (2026-09-27) names the remaining crux of Theorem 1.1 exactly: the class at
time `n` must become asymptotically uniform **jointly with the digit window at time `n`**, and
those two blocks are *adjacent*, so no amount of ψ-mixing with a gap can separate them
(`classStep_bijective`: nothing is ever forgotten).  The standard device that handles adjacency
is to carry the tail parameter as part of the state, i.e. to work with the **state-refined
horizon integral**

> `F_n(d, s)(τ) = ∫_{y ∈ (0,1) : Tⁿ y ∈ A, runState δ d (W_n y) = s} h_τ(y) dy`,

where `h_τ` is `tailDensity τ` and `W_n y` is the length-`n` digit word of `y`.  Three facts
are proved here, unconditionally and for an arbitrary finite-state automaton `δ`:

* `stateHorizonIntegral_succ` — **the refined recursion**
  `F_{n+1}(d, s) = ∑_{a ≥ 1} w_τ(a)·F_n(δ d a, s)(τ_a)`, i.e. `F_{n+1} = stateStepOp F_n`.
  This is `CFRecursion.horizonIntegral_succ` with the automaton bookkeeping threaded through:
  the first digit both consumes a branch of the tail-parameter chain *and* advances the
  automaton, and the two commute because the automaton reads the digit and the branch map
  reproduces it (`mem_cfCylinder_singleton`).
* `sum_stateHorizonIntegral` — summing over the target state recovers the unrefined
  `horizonIntegral`.  So the refined family is a *disintegration* of `G_n`, and the pin below
  is exactly the statement that the disintegration is asymptotically uniform.
* `stateHorizonIntegral_nonneg`, `stateHorizonIntegral_le` — the cone the operator preserves.

The one open obligation, `stateHorizonIntegral_pin`, is the crux itself.  It is stated with the
two hypotheses the class automaton supplies (`VandeheyClass.exists_word_reach` refined to
`Doeblin.exists_classWord_three`, and `VandeheyRenewal.classStep_bijective`), and its `N = 1`
case is `CFPsiPin.horizonIntegral_pin_geom`.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut

namespace VandeheyState

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The digit word peels from the left -/

/-- `W_{n+1}(y) = a₀(y) :: W_n(T y)`.  Unconditional: `cfDigit_succ` needs no irrationality. -/
lemma cfWord_succ_cons (y : ℝ) (n : ℕ) :
    cfWord y (n + 1) = cfDigit y 0 :: cfWord (gaussMap y) n := by
  simp only [cfWord, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons.injEq,
    true_and]
  exact List.map_congr_left fun k _ => (cfDigit_succ y k)

/-- The automaton run over `W_{n+1}(y)` eats the first digit and continues at `T y`. -/
lemma runState_cfWord_succ (δ : S → ℕ → S) (d : S) (y : ℝ) (n : ℕ) :
    runState δ d (cfWord y (n + 1))
      = runState δ (δ d (cfDigit y 0)) (cfWord (gaussMap y) n) := by
  rw [cfWord_succ_cons, runState_cons]

/-! ## Measurability of the state event -/

/-- `{y : runState δ d (W_n y) = s}` is measurable.  Induction on `n`, splitting over the
(finitely many) intermediate states and the (countably many) values of the last digit. -/
lemma measurableSet_stateEq (δ : S → ℕ → S) (d : S) (n : ℕ) :
    ∀ s : S, MeasurableSet {y : ℝ | runState δ d (cfWord y n) = s} := by
  induction n with
  | zero =>
      intro s
      simp only [cfWord, List.range_zero, List.map_nil, runState_nil]
      by_cases h : d = s
      · simp only [h, eq_self_iff_true, Set.setOf_true]
        exact MeasurableSet.univ
      · simp only [h, Set.setOf_false]
        exact MeasurableSet.empty
  | succ n ih =>
      intro s
      have hsplit : {y : ℝ | runState δ d (cfWord y (n + 1)) = s}
          = ⋃ p : S × ℕ, (if δ p.1 p.2 = s then
              ({y : ℝ | runState δ d (cfWord y n) = p.1}
                ∩ {y : ℝ | cfDigit y n = p.2}) else (∅ : Set ℝ)) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hy
          refine ⟨(runState δ d (cfWord y n), cfDigit y n), ?_⟩
          have hstep : runState δ d (cfWord y (n + 1))
              = δ (runState δ d (cfWord y n)) (cfDigit y n) := by
            rw [show n + 1 = n + 1 from rfl, cfWord, List.range_succ, List.map_append]
            simp [runState, cfWord, List.foldl_append]
          rw [if_pos (by rw [← hstep]; exact hy)]
          exact ⟨rfl, rfl⟩
        · rintro ⟨p, hp⟩
          by_cases hc : δ p.1 p.2 = s
          · rw [if_pos hc] at hp
            obtain ⟨h1, h2⟩ := hp
            simp only [Set.mem_setOf_eq] at h1 h2
            have hstep : runState δ d (cfWord y (n + 1))
                = δ (runState δ d (cfWord y n)) (cfDigit y n) := by
              rw [cfWord, List.range_succ, List.map_append]
              simp [runState, cfWord, List.foldl_append]
            rw [hstep, h1, h2]; exact hc
          · rw [if_neg hc] at hp; exact absurd hp (Set.notMem_empty y)
      rw [hsplit]
      refine MeasurableSet.iUnion fun p => ?_
      by_cases hc : δ p.1 p.2 = s
      · rw [if_pos hc]
        exact (ih p.1).inter (measurable_cfDigit n (measurableSet_singleton p.2))
      · rw [if_neg hc]; exact MeasurableSet.empty

/-! ## The state-refined horizon set and integral -/

/-- The state-refined horizon set: points of `(0,1)` whose first `n` digits drive `δ` from `d`
to `s` and whose `n`-th iterate lands in `A`. -/
def stateHorizonSet (δ : S → ℕ → S) (A : Set ℝ) (n : ℕ) (d s : S) : Set ℝ :=
  horizonSet A n ∩ {y : ℝ | runState δ d (cfWord y n) = s}

lemma measurableSet_stateHorizonSet {A : Set ℝ} (hA : MeasurableSet A)
    (δ : S → ℕ → S) (n : ℕ) (d s : S) :
    MeasurableSet (stateHorizonSet δ A n d s) :=
  (measurableSet_horizonSet hA n).inter (measurableSet_stateEq δ d n s)

lemma stateHorizonSet_subset (δ : S → ℕ → S) (A : Set ℝ) (n : ℕ) (d s : S) :
    stateHorizonSet δ A n d s ⊆ Set.Ioo (0 : ℝ) 1 :=
  fun _ hy => horizonSet_subset A n hy.1

/-- `F_n(d,s)(τ) = ∫_{stateHorizonSet} h_τ`. -/
noncomputable def stateHorizonIntegral (δ : S → ℕ → S) (A : Set ℝ) (n : ℕ) (d s : S)
    (τ : ℝ) : ℝ :=
  ∫ y in stateHorizonSet δ A n d s, tailDensity τ y

/-- The state-refined family step operator: the tail-parameter transfer operator with the
automaton advanced along the same digit. -/
noncomputable def stateStepOp (δ : S → ℕ → S) (Φ : S → ℝ → ℝ) (d : S) (τ : ℝ) : ℝ :=
  ∑' k : ℕ, stepWeight τ k * Φ (δ d (k + 1)) (stepPt τ k)

/-! ## The refined recursion -/

/-- The refined horizon set splits over the first digit, up to the rationals. -/
lemma stateHorizonSet_succ_ae (δ : S → ℕ → S) (A : Set ℝ) (n : ℕ) (d s : S) :
    (stateHorizonSet δ A (n + 1) d s : Set ℝ) =ᵐ[volume]
      ⋃ j : ℕ, (cfCylinder [j + 1]
        ∩ gaussMap ⁻¹' stateHorizonSet δ A n (δ d (j + 1)) s : Set ℝ) := by
  apply ae_eq_of_irrational_iff
  intro x hirr
  constructor
  · rintro ⟨⟨hx, hTA⟩, hst⟩
    rw [Set.mem_preimage] at hTA
    simp only [Set.mem_setOf_eq] at hst
    have horb := irrational_orbit x hirr hx 1
    simp only [Function.iterate_one] at horb
    have hd := one_le_cfDigit x hirr hx 0
    refine Set.mem_iUnion.mpr ⟨cfDigit x 0 - 1, ?_⟩
    have hd' : cfDigit x 0 - 1 + 1 = cfDigit x 0 := Nat.succ_pred_eq_of_pos hd
    refine ⟨by rw [hd']; exact mem_cfCylinder_singleton.mpr ⟨hx, rfl⟩, ?_⟩
    rw [Set.mem_preimage]
    refine ⟨⟨horb.2, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, ← Function.iterate_succ_apply]; exact hTA
    · simp only [Set.mem_setOf_eq, hd']
      rw [← runState_cfWord_succ]; exact hst
  · intro hx
    obtain ⟨j, hcyl, hTB⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxIoo, hdig⟩ := mem_cfCylinder_singleton.mp hcyl
    rw [Set.mem_preimage] at hTB
    obtain ⟨⟨hTIoo, hTA⟩, hst⟩ := hTB
    refine ⟨⟨hxIoo, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, Function.iterate_succ_apply]
      exact hTA
    · simp only [Set.mem_setOf_eq] at hst ⊢
      rw [runState_cfWord_succ, hdig]; exact hst

/-- **The refined recursion**: `F_{n+1}(d,s) = stateStepOp δ (F_n(·,s)) d` on `[0,1]`. -/
theorem stateHorizonIntegral_succ (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) (d s : S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    stateHorizonIntegral δ A (n + 1) d s τ
      = stateStepOp δ (fun d' => stateHorizonIntegral δ A n d' s) d τ := by
  set B : S → Set ℝ := fun d' => stateHorizonSet δ A n d' s with hB
  have hBmeas : ∀ d', MeasurableSet (B d') := fun d' =>
    measurableSet_stateHorizonSet hA δ n d' s
  have hB1 : ∀ d', B d' ⊆ Set.Ioo (0 : ℝ) 1 := fun d' =>
    stateHorizonSet_subset δ A n d' s
  set u : ℕ → Set ℝ :=
    fun j => (cfCylinder [j + 1] ∩ gaussMap ⁻¹' B (δ d (j + 1)) : Set ℝ) with hu
  have humeas : ∀ j, MeasurableSet (u j) := fun j =>
    (measurableSet_cfCylinder [j + 1]).inter (measurable_gaussMap (hBmeas _))
  have hudisj : Pairwise (Function.onFun Disjoint u) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
    have hi := (mem_cfCylinder_singleton.mp hxi).2
    have hj := (mem_cfCylinder_singleton.mp hxj).2
    exact hij (by omega)
  have hint : IntegrableOn (tailDensity τ) (⋃ j, u j) volume := by
    apply (integrableOn_tailDensity hτ.1).mono_set
    refine Set.iUnion_subset fun j x hx => ?_
    exact hx.1.1
  rw [stateHorizonIntegral, setIntegral_congr_set (stateHorizonSet_succ_ae δ A n d s),
    integral_iUnion humeas hudisj hint, stateStepOp]
  apply tsum_congr
  intro j
  have hj1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
  have hpiece : ∫ y in u j, tailDensity τ y =
      ∫ y in branchMap (j + 1) '' B (δ d (j + 1)), tailDensity τ y :=
    setIntegral_congr_set (branch_inter_ae (j + 1) hj1 _ (hB1 _))
  rw [hpiece, setIntegral_tailDensity_branch (j + 1) hj1 (hBmeas _) (hB1 _) hτ]
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [stepWeight, stepPt, stateHorizonIntegral, hcast]
  congr 1
  · congr 1
    ring
  · congr 2
    rw [one_div]

/-! ## The disintegration identity -/

/-- Summing the refined family over the target state recovers `G_n`. -/
theorem sum_stateHorizonIntegral (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) (d : S) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∑ s : S, stateHorizonIntegral δ A n d s τ = horizonIntegral A n τ := by
  classical
  have hcover : horizonSet A n = ⋃ s : S, stateHorizonSet δ A n d s := by
    ext y
    simp only [stateHorizonSet, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun hy => ⟨runState δ d (cfWord y n), hy, rfl⟩, fun ⟨_, hy, _⟩ => hy⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun s : S => stateHorizonSet δ A n d s) := by
    intro s s' hss
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨-, hy⟩ ⟨-, hy'⟩
    simp only [Set.mem_setOf_eq] at hy hy'
    exact hss (hy ▸ hy')
  have hint : IntegrableOn (tailDensity τ) (⋃ s : S, stateHorizonSet δ A n d s) volume := by
    apply (integrableOn_tailDensity hτ).mono_set
    exact Set.iUnion_subset fun s => stateHorizonSet_subset δ A n d s
  rw [horizonIntegral, hcover, integral_iUnion (fun s => measurableSet_stateHorizonSet hA δ n d s)
    hdisj hint, tsum_fintype]
  rfl

/-! ## The cone -/

lemma stateHorizonIntegral_nonneg (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) (d s : S) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ stateHorizonIntegral δ A n d s τ := by
  rw [stateHorizonIntegral]
  refine setIntegral_nonneg (measurableSet_stateHorizonSet hA δ n d s) fun y hy => ?_
  have hy0 := (stateHorizonSet_subset δ A n d s hy).1
  rw [tailDensity]
  positivity

/-- Each refined piece is dominated by the unrefined `G_n`. -/
lemma stateHorizonIntegral_le (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) (d s : S) {τ : ℝ} (hτ : 0 ≤ τ) :
    stateHorizonIntegral δ A n d s τ ≤ horizonIntegral A n τ := by
  classical
  rw [← sum_stateHorizonIntegral δ hA n d hτ]
  refine Finset.single_le_sum (f := fun s' => stateHorizonIntegral δ A n d s' τ)
    (fun s' _ => stateHorizonIntegral_nonneg δ hA n d s' hτ) (Finset.mem_univ s)

/-! ## A uniform bound -/

/-- `h_τ ≤ 2` on `[0,1]²`, and the refined horizon set sits inside `(0,1)`, so `F_n ≤ 2`. -/
lemma stateHorizonIntegral_le_two (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) (d s : S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    stateHorizonIntegral δ A n d s τ ≤ 2 := by
  have hsub := stateHorizonSet_subset δ A n d s
  have hmeas := measurableSet_stateHorizonSet hA δ n d s
  have hint : IntegrableOn (tailDensity τ) (stateHorizonSet δ A n d s) volume :=
    (integrableOn_tailDensity hτ.1).mono_set hsub
  have hbd : ∀ y ∈ stateHorizonSet δ A n d s, tailDensity τ y ≤ 2 := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hsub hy
    have hxy : (0 : ℝ) ≤ τ * y := mul_nonneg hτ.1 hy0.le
    have hden : (1 : ℝ) ≤ (1 + τ * y) ^ 2 := by nlinarith
    rw [tailDensity, div_le_iff₀ (by nlinarith)]
    nlinarith [hτ.2]
  have hvol : (volume (stateHorizonSet δ A n d s)).toReal ≤ 1 := by
    have h1 : volume (stateHorizonSet δ A n d s) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
      measure_mono hsub
    rw [Real.volume_Ioo] at h1
    have := ENNReal.toReal_le_toReal (by
        exact ne_top_of_le_ne_top (by simp) h1) (by simp) |>.mpr h1
    simpa using this
  have hfin : volume (stateHorizonSet δ A n d s) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (by simp)
  have : IsFiniteMeasure (volume.restrict (stateHorizonSet δ A n d s)) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hconst : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (stateHorizonSet δ A n d s) volume :=
    integrable_const 2
  calc stateHorizonIntegral δ A n d s τ
      ≤ ∫ _ in stateHorizonSet δ A n d s, (2 : ℝ) :=
        setIntegral_mono_on hint hconst hmeas hbd
    _ = (volume (stateHorizonSet δ A n d s)).toReal * 2 := by
        simp [integral_const, smul_eq_mul, measureReal_def]
    _ ≤ 2 := by nlinarith [ENNReal.toReal_nonneg (a := volume (stateHorizonSet δ A n d s))]

/-! ## The dual disintegration: summing over the INITIAL state -/

/-- **Summing over the initial state recovers `G_n` as well**, provided every digit step is a
bijection of the state space.  Together with `sum_stateHorizonIntegral` this says the refined
family is *doubly stochastic*: the uniform law on `S` is the only possible limit, and no
computation of a stationary vector is owed.

The proof is the exact discrete analogue of `VandeheyRenewal.sum_classKernel_col`: the refined
recursion advances the initial state by `d ↦ δ d a`, and summing a bijection's precomposition
over a finite type is a no-op, so `∑_d F_n(d,s)` obeys the *unrefined* recursion with the
unrefined initial condition. -/
theorem sum_over_initial_stateHorizonIntegral (δ : S → ℕ → S) {A : Set ℝ}
    (hA : MeasurableSet A) (hbij : ∀ a : ℕ, Function.Bijective (fun d : S => δ d a))
    (n : ℕ) (s : S) :
    ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
      ∑ d : S, stateHorizonIntegral δ A n d s τ = horizonIntegral A n τ := by
  classical
  induction n with
  | zero =>
      intro τ hτ
      have hpt : ∀ d : S, stateHorizonIntegral δ A 0 d s τ
          = if d = s then horizonIntegral A 0 τ else 0 := by
        intro d
        by_cases h : d = s
        · have hset : stateHorizonSet δ A 0 d s = horizonSet A 0 := by
            simp [stateHorizonSet, cfWord, runState_nil, h]
          rw [stateHorizonIntegral, hset, if_pos h, horizonIntegral]
        · have hset : stateHorizonSet δ A 0 d s = (∅ : Set ℝ) := by
            simp [stateHorizonSet, cfWord, runState_nil, h]
          rw [stateHorizonIntegral, hset, if_neg h, Measure.restrict_empty, integral_zero_measure]
      simp [hpt]
  | succ n ih =>
      intro τ hτ
      have hsummable : ∀ d : S,
          Summable (fun k : ℕ => stepWeight τ k *
            stateHorizonIntegral δ A n (δ d (k + 1)) s (stepPt τ k)) := by
        intro d
        refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
          ((summable_stepWeight hτ.1).mul_right 2)
        · exact mul_nonneg (stepWeight_nonneg hτ.1 k)
            (stateHorizonIntegral_nonneg δ hA n _ s (stepPt_mem_Icc hτ.1 k).1)
        · exact mul_le_mul_of_nonneg_left
            (stateHorizonIntegral_le_two δ hA n _ s (stepPt_mem_Icc hτ.1 k))
            (stepWeight_nonneg hτ.1 k)
      calc ∑ d : S, stateHorizonIntegral δ A (n + 1) d s τ
          = ∑ d : S, ∑' k : ℕ, stepWeight τ k *
              stateHorizonIntegral δ A n (δ d (k + 1)) s (stepPt τ k) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [stateHorizonIntegral_succ δ hA n d s hτ, stateStepOp]
        _ = ∑' k : ℕ, ∑ d : S, stepWeight τ k *
              stateHorizonIntegral δ A n (δ d (k + 1)) s (stepPt τ k) :=
            (Summable.tsum_finsetSum (fun d _ => hsummable d)).symm
        _ = ∑' k : ℕ, stepWeight τ k * horizonIntegral A n (stepPt τ k) := by
            refine tsum_congr fun k => ?_
            rw [← Finset.mul_sum]
            congr 1
            rw [← ih (stepPt_mem_Icc hτ.1 k)]
            exact (hbij (k + 1)).sum_comp
              (fun d' => stateHorizonIntegral δ A n d' s (stepPt τ k))
        _ = horizonIntegral A (n + 1) τ := by
            rw [horizonIntegral_succ A hA n hτ, stepOp]

/-! ## The operator on families, and its Doeblin minorization

The remaining content of `stateHorizonIntegral_pin` is an ergodicity statement for the operator
`stateStepOp` acting on families `Φ : S → ℝ → ℝ` over the product `S × [0,1]`.  This section
builds the invariant cone, the iteration, and the **Doeblin minorization**: a genuine digit word
`w` driving `d` to `t` forces `Lᵂ Φ (d, τ) ≥ wordWeight w · inf_τ Φ(t, τ)` with `wordWeight w > 0`
depending only on `w`.  No expansion of `L^{|w|}` over words is needed: each application of `L`
is a *nonnegative* `tsum`, so it dominates its `(a-1)`-st term, and the induction runs along `w`.
-/

/-- The cone of families bounded by `B` on `S × [0,1]`. -/
def InCone (B : ℝ) (Φ : S → ℝ → ℝ) : Prop :=
  ∀ d : S, ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Φ d τ ∧ Φ d τ ≤ B

/-- A `τ`-uniform lower bound for the branch weight: `w_τ(k) ≥ 1/((k+2)(k+3))` on `[0,1]`. -/
lemma stepWeight_ge {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    1 / (((k : ℝ) + 2) * ((k : ℝ) + 3)) ≤ stepWeight τ k := by
  obtain ⟨h0, h1⟩ := hτ
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [stepWeight, div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : ((k : ℝ) + 1 + τ) * ((k : ℝ) + 2 + τ) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 3) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hP : (0 : ℝ) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 3) := by positivity
  nlinarith [mul_nonneg h0 hP]

lemma summable_stateStep {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) (δ : S → ℕ → S)
    (d : S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun k : ℕ => stepWeight τ k * Φ (δ d (k + 1)) (stepPt τ k)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_stepWeight hτ.1).mul_right B)
  · exact mul_nonneg (stepWeight_nonneg hτ.1 k)
      (hΦ _ _ (stepPt_mem_Icc hτ.1 k)).1
  · exact mul_le_mul_of_nonneg_left (hΦ _ _ (stepPt_mem_Icc hτ.1 k)).2
      (stepWeight_nonneg hτ.1 k)

/-- `stateStepOp` preserves the cone: it is an average. -/
lemma stateStepOp_inCone {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) (δ : S → ℕ → S) :
    InCone B (stateStepOp δ Φ) := by
  intro d τ hτ
  have hsum := summable_stateStep hΦ δ d hτ
  constructor
  · exact tsum_nonneg fun k => mul_nonneg (stepWeight_nonneg hτ.1 k)
      (hΦ _ _ (stepPt_mem_Icc hτ.1 k)).1
  · calc stateStepOp δ Φ d τ ≤ ∑' k : ℕ, stepWeight τ k * B :=
          hsum.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
            (hΦ _ _ (stepPt_mem_Icc hτ.1 k)).2 (stepWeight_nonneg hτ.1 k))
            ((summable_stepWeight hτ.1).mul_right B)
      _ = B := by rw [tsum_mul_right, tsum_stepWeight hτ.1, one_mul]

/-- The `n`-fold operator.  `stateStepIter δ (n+1) Φ = stateStepOp δ (stateStepIter δ n Φ)`, so
the OUTERMOST application reads the FIRST digit — matching `stateHorizonIntegral_succ`. -/
noncomputable def stateStepIter (δ : S → ℕ → S) : ℕ → (S → ℝ → ℝ) → (S → ℝ → ℝ)
  | 0, Φ => Φ
  | n + 1, Φ => stateStepOp δ (stateStepIter δ n Φ)

lemma stateStepIter_inCone {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) (δ : S → ℕ → S) :
    ∀ n, InCone B (stateStepIter δ n Φ)
  | 0 => hΦ
  | n + 1 => stateStepOp_inCone (stateStepIter_inCone hΦ δ n) δ

/-- The refined horizon integral is the iterate of the operator applied to `F_0`. -/
theorem stateHorizonIntegral_iter (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (s : S) (n : ℕ) :
    ∀ (d : S) {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
      stateHorizonIntegral δ A n d s τ
        = stateStepIter δ n (fun d' τ' => stateHorizonIntegral δ A 0 d' s τ') d τ := by
  induction n with
  | zero => intro d τ _; rfl
  | succ n ih =>
      intro d τ hτ
      rw [stateHorizonIntegral_succ δ hA n d s hτ, stateStepIter, stateStepOp, stateStepOp]
      exact tsum_congr fun k => by rw [ih _ (stepPt_mem_Icc hτ.1 k)]

/-- The `τ`-uniform weight of a genuine digit word: `∏_{a ∈ w} 1/((a+1)(a+2))`. -/
noncomputable def wordWeight (w : List ℕ) : ℝ :=
  (w.map (fun a : ℕ => 1 / (((a : ℝ) + 1) * ((a : ℝ) + 2)))).prod

lemma wordWeight_pos {w : List ℕ} : 0 < wordWeight w := by
  rw [wordWeight]
  apply List.prod_pos
  intro y hy
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
  have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  positivity

/-- **The Doeblin minorization for the operator.**  If `w` is a genuine digit word driving `d`
to `runState δ d w`, and `Φ ≥ c` on that target state for all `τ ∈ [0,1]`, then `|w|` steps of
the operator started at `d` already see at least `wordWeight w · c`.

The proof needs no word expansion: `stateStepOp` is a `tsum` of nonnegative terms, so it
dominates the single term indexed by the first letter of `w`. -/
theorem stateStepIter_ge_word {B c : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) (δ : S → ℕ → S)
    (hc : 0 ≤ c) :
    ∀ (w : List ℕ), (∀ a ∈ w, 1 ≤ a) →
      ∀ (d : S), (∀ τ' ∈ Set.Icc (0 : ℝ) 1, c ≤ Φ (runState δ d w) τ') →
      ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
        wordWeight w * c ≤ stateStepIter δ w.length Φ d τ := by
  intro w
  induction w with
  | nil =>
      intro _ d hcd τ hτ
      simpa [wordWeight, stateStepIter] using hcd τ hτ
  | cons a v ih =>
      intro hpos d hcd τ hτ
      have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
      have hak : a - 1 + 1 = a := Nat.succ_pred_eq_of_pos ha
      have hvpos : ∀ b ∈ v, 1 ≤ b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
      have hcone := stateStepIter_inCone hΦ δ v.length
      -- the single term indexed by the first letter
      have hsum := summable_stateStep hcone δ d hτ
      have hterm : stepWeight τ (a - 1) * stateStepIter δ v.length Φ (δ d a) (stepPt τ (a - 1))
          ≤ stateStepOp δ (stateStepIter δ v.length Φ) d τ := by
        have := hsum.le_tsum (a - 1) (fun j _ => mul_nonneg (stepWeight_nonneg hτ.1 j)
          (hcone _ _ (stepPt_mem_Icc hτ.1 j)).1)
        rw [hak] at this
        exact this
      have hIH : wordWeight v * c
          ≤ stateStepIter δ v.length Φ (δ d a) (stepPt τ (a - 1)) := by
        refine ih hvpos (δ d a) (fun τ' hτ' => ?_) (stepPt_mem_Icc hτ.1 (a - 1))
        have : runState δ (δ d a) v = runState δ d (a :: v) := rfl
        rw [this]; exact hcd τ' hτ'
      have hw : wordWeight (a :: v) = 1 / (((a : ℝ) + 1) * ((a : ℝ) + 2)) * wordWeight v := by
        simp [wordWeight]
      have hlow : 1 / (((a : ℝ) + 1) * ((a : ℝ) + 2)) ≤ stepWeight τ (a - 1) := by
        have h := stepWeight_ge hτ (a - 1)
        have hcast : ((a - 1 : ℕ) : ℝ) + 2 = (a : ℝ) + 1 ∧ ((a - 1 : ℕ) : ℝ) + 3 = (a : ℝ) + 2 := by
          have : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
            have hc1 : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
              rw [show ((a - 1 : ℕ) : ℝ) + 1 = ((a - 1 + 1 : ℕ) : ℝ) by push_cast; ring, hak]
            linarith
          constructor <;> rw [this] <;> ring
        rw [hcast.1, hcast.2] at h
        exact h
      calc wordWeight (a :: v) * c
          = 1 / (((a : ℝ) + 1) * ((a : ℝ) + 2)) * (wordWeight v * c) := by rw [hw]; ring
        _ ≤ stepWeight τ (a - 1) * (stateStepIter δ v.length Φ (δ d a) (stepPt τ (a - 1))) := by
            apply mul_le_mul hlow hIH (mul_nonneg wordWeight_pos.le hc)
              (stepWeight_nonneg hτ.1 _)
        _ ≤ stateStepOp δ (stateStepIter δ v.length Φ) d τ := hterm
        _ = stateStepIter δ (a :: v).length Φ d τ := by
            simp [stateStepIter, List.length_cons]

/-! ## The log-Lipschitz half of the contraction, for a FAMILY -/

/-- Ordered half of `stateStepOp_logLipschitz`. -/
theorem stateStepOp_logLipschitz_aux {Φ : S → ℝ → ℝ} {L c r B : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hΦ : InCone B Φ) (δ : S → ℕ → S) (d : S)
    (hlip : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Φ e x - Φ e y| ≤ L * |Real.log (1 + x) - Real.log (1 + y)|)
    (hc : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, |Φ e x - c| ≤ r)
    {t t' : ℝ} (ht0' : 0 ≤ t') (htt' : t' ≤ t) (ht1 : t ≤ 1) :
    |stateStepOp δ Φ d t - stateStepOp δ Φ d t'|
      ≤ ((2 / 5) * L + (3 / 5) * r) * (Real.log (1 + t) - Real.log (1 + t')) := by
  have ht0 : (0 : ℝ) ≤ t := ht0'.trans htt'
  have ht1' : t' ≤ 1 := htt'.trans ht1
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have htI' : t' ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0', ht1'⟩
  set ψ : ℕ → ℝ → ℝ := fun k => Φ (δ d (k + 1)) with hψdef
  have hψlip : ∀ k : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |ψ k x - ψ k y| ≤ L * |Real.log (1 + x) - Real.log (1 + y)| :=
    fun k x hx y hy => hlip _ x hx y hy
  set δlog : ℝ := Real.log (1 + t) - Real.log (1 + t') with hδlog
  have hδ0 : 0 ≤ δlog := by
    have := Real.log_le_log (by linarith : (0:ℝ) < 1 + t') (by linarith : (1:ℝ) + t' ≤ 1 + t)
    rw [hδlog]; linarith
  set Aq : ℕ → ℝ := fun k => stepWeight t k * (ψ k (stepPt t k) - ψ k (stepPt t' k)) with hAq
  set Bq : ℕ → ℝ := fun k => (stepWeight t k - stepWeight t' k) * (ψ k (stepPt t' k) - c)
    with hBq
  -- summabilities
  have hS1 : Summable (fun k => stepWeight t k * ψ k (stepPt t k)) :=
    summable_stateStep hΦ δ d htI
  have hS2 : Summable (fun k => stepWeight t' k * ψ k (stepPt t' k)) :=
    summable_stateStep hΦ δ d htI'
  have hbnd : ∀ k : ℕ, |ψ k (stepPt t' k) - c| ≤ r :=
    fun k => hc _ _ (stepPt_mem_Icc ht0' k)
  have hSmix : Summable (fun k => stepWeight t k * ψ k (stepPt t' k)) := by
    refine Summable.of_abs (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((summable_stepWeight ht0).mul_right (B + |c| + r)))
    rw [abs_mul, abs_of_nonneg (stepWeight_nonneg ht0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (stepWeight_nonneg ht0 k)
    have h1 := (hΦ (δ d (k + 1)) _ (stepPt_mem_Icc ht0' k))
    have : |ψ k (stepPt t' k)| = ψ k (stepPt t' k) := abs_of_nonneg h1.1
    rw [this]
    have := h1.2
    have habs : (0 : ℝ) ≤ |c| := abs_nonneg c
    linarith
  have hSA : Summable Aq := by
    have : Aq = fun k => stepWeight t k * ψ k (stepPt t k)
        - stepWeight t k * ψ k (stepPt t' k) := by funext k; rw [hAq]; ring
    rw [this]; exact hS1.sub hSmix
  have hSΔ : Summable (fun k => |stepWeight t k - stepWeight t' k|) :=
    ((summable_stepWeight ht0).sub (summable_stepWeight ht0')).abs
  have hSBabs : Summable (fun k => |Bq k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) (hSΔ.mul_right r)
    rw [hBq, abs_mul]
    exact mul_le_mul_of_nonneg_left (hbnd k) (abs_nonneg _)
  have hSB : Summable Bq := hSBabs.of_abs
  -- the split
  have hsplit : stateStepOp δ Φ d t - stateStepOp δ Φ d t'
      = (∑' k, Aq k) + ∑' k, Bq k := by
    have hcz : Summable (fun k => (stepWeight t k - stepWeight t' k) * c) :=
      ((summable_stepWeight ht0).sub (summable_stepWeight ht0')).mul_right c
    have hczero : ∑' k, (stepWeight t k - stepWeight t' k) * c = 0 := by
      rw [tsum_mul_right, (summable_stepWeight ht0).tsum_sub (summable_stepWeight ht0'),
        tsum_stepWeight ht0, tsum_stepWeight ht0', sub_self, zero_mul]
    have hBalt : (∑' k, Bq k)
        = (∑' k, stepWeight t k * ψ k (stepPt t' k))
          - (∑' k, stepWeight t' k * ψ k (stepPt t' k)) := by
      have hBex : Bq = fun k => (stepWeight t k * ψ k (stepPt t' k)
          - stepWeight t' k * ψ k (stepPt t' k)) - (stepWeight t k - stepWeight t' k) * c := by
        funext k; rw [hBq]; ring
      rw [hBex, Summable.tsum_sub (hSmix.sub hS2) hcz, hczero, sub_zero,
        hSmix.tsum_sub hS2]
    have hAalt : (∑' k, Aq k)
        = (∑' k, stepWeight t k * ψ k (stepPt t k))
          - ∑' k, stepWeight t k * ψ k (stepPt t' k) := by
      have hAex : Aq = fun k => stepWeight t k * ψ k (stepPt t k)
          - stepWeight t k * ψ k (stepPt t' k) := by funext k; rw [hAq]; ring
      rw [hAex, hS1.tsum_sub hSmix]
    rw [hAalt, hBalt, stateStepOp, stateStepOp]
    ring
  -- the two estimates
  have hAbound : |∑' k, Aq k| ≤ (2 / 5) * L * δlog := by
    have hstep : |∑' k, Aq k| ≤ ∑' k, |Aq k| := by
      have := norm_tsum_le_tsum_norm (f := Aq)
        (by simpa [Real.norm_eq_abs] using hSA.abs)
      simpa only [Real.norm_eq_abs] using this
    exact hstep.trans (WeightTV.tsum_abs_Afamily_le hL hψlip ht0' htt' ht1)
  have hBbound : |∑' k, Bq k| ≤ (3 / 5) * r * δlog := by
    have h1 : |∑' k, Bq k| ≤ ∑' k, |Bq k| := by
      have := norm_tsum_le_tsum_norm (f := Bq)
        (by simpa [Real.norm_eq_abs] using hSBabs)
      simpa only [Real.norm_eq_abs] using this
    refine h1.trans ?_
    have h2 : ∑' k, |Bq k| ≤ (∑' k, |stepWeight t k - stepWeight t' k|) * r := by
      rw [← tsum_mul_right]
      refine hSBabs.tsum_le_tsum (fun k => ?_) (hSΔ.mul_right r)
      rw [hBq, abs_mul]
      exact mul_le_mul_of_nonneg_left (hbnd k) (abs_nonneg _)
    refine h2.trans ?_
    have h3 := WeightTV.tsum_abs_stepWeight_sub_le htI htI'
    have h4 : |Real.log (1 + t) - Real.log (1 + t')| = δlog := abs_of_nonneg hδ0
    rw [h4] at h3
    nlinarith [hr, hδ0]
  rw [hsplit]
  calc |(∑' k, Aq k) + ∑' k, Bq k| ≤ |∑' k, Aq k| + |∑' k, Bq k| := abs_add_le _ _
    _ ≤ (2 / 5) * L * δlog + (3 / 5) * r * δlog := add_le_add hAbound hBbound
    _ = ((2 / 5) * L + (3 / 5) * r) * δlog := by ring

/-- **The family log-Lipschitz contraction.**  If every `Φ(e, ·)` is `L`-log-Lipschitz on
`[0,1]` and the whole family lies within `r` of a single constant `c`, then
`stateStepOp δ Φ (d, ·)` is `((2/5)L + (3/5)r)`-log-Lipschitz.

This is the family analogue of `CFPsiPin.stepOp_logLipschitz`, with the Abel-resummed `B`-series
replaced by `WeightTV.tsum_abs_stepWeight_sub_le` (which needs no Abel resummation because
`Σ_k w_τ(k) = 1` lets the constant `c` be subtracted freely) and the `A`-series by
`WeightTV.tsum_abs_Afamily_le` (which is term-by-term in `k` and so survives the passage to a
family verbatim).

Coupled with the Doeblin step `stateStepIter_ge_word`, this closes the 2×2 linear recursion for
`(oscillation, log-Lipschitz constant)`: the cross terms satisfy `(3/5)·log 2 < 1`, so the
spectral radius is `< 1`. -/
theorem stateStepOp_logLipschitz {Φ : S → ℝ → ℝ} {L c r B : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hΦ : InCone B Φ) (δ : S → ℕ → S) (d : S)
    (hlip : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Φ e x - Φ e y| ≤ L * |Real.log (1 + x) - Real.log (1 + y)|)
    (hc : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, |Φ e x - c| ≤ r)
    {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |stateStepOp δ Φ d t - stateStepOp δ Φ d t'|
      ≤ ((2 / 5) * L + (3 / 5) * r) * |Real.log (1 + t) - Real.log (1 + t')| := by
  have habs : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |Real.log (1 + b) - Real.log (1 + a)|
      = Real.log (1 + b) - Real.log (1 + a) := by
    intro a b ha hab
    refine abs_of_nonneg ?_
    have := Real.log_le_log (by linarith : (0:ℝ) < 1 + a) (by linarith : (1:ℝ) + a ≤ 1 + b)
    linarith
  rcases le_total t' t with h | h
  · rw [habs t' t ht'.1 h]
    exact stateStepOp_logLipschitz_aux hL hr hΦ δ d hlip hc ht'.1 h ht.2
  · rw [abs_sub_comm (stateStepOp δ Φ d t), abs_sub_comm (Real.log (1 + t)), habs t t' ht.1 h]
    exact stateStepOp_logLipschitz_aux hL hr hΦ δ d hlip hc ht.1 h ht'.2

/-! ## Affine algebra of the operator -/

lemma stateStepOp_sub_const {B B' a : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ)
    (hΨ : InCone B' (fun d τ => Φ d τ - a)) (δ : S → ℕ → S) (d : S)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    stateStepOp δ (fun d τ => Φ d τ - a) d τ = stateStepOp δ Φ d τ - a := by
  have h1 := summable_stateStep hΦ δ d hτ
  have h2 : Summable (fun k : ℕ => stepWeight τ k * a) :=
    (summable_stepWeight hτ.1).mul_right a
  have hsplit : ∀ k : ℕ, stepWeight τ k * ((fun d τ => Φ d τ - a) (δ d (k + 1)) (stepPt τ k))
      = stepWeight τ k * Φ (δ d (k + 1)) (stepPt τ k) - stepWeight τ k * a := by
    intro k; ring
  rw [stateStepOp, tsum_congr hsplit, h1.tsum_sub h2, tsum_mul_right,
    tsum_stepWeight hτ.1, one_mul, stateStepOp]

lemma stateStepOp_const_sub {B B' a : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ)
    (hΨ : InCone B' (fun d τ => a - Φ d τ)) (δ : S → ℕ → S) (d : S)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    stateStepOp δ (fun d τ => a - Φ d τ) d τ = a - stateStepOp δ Φ d τ := by
  have h1 := summable_stateStep hΦ δ d hτ
  have h2 : Summable (fun k : ℕ => stepWeight τ k * a) :=
    (summable_stepWeight hτ.1).mul_right a
  have hsplit : ∀ k : ℕ, stepWeight τ k * ((fun d τ => a - Φ d τ) (δ d (k + 1)) (stepPt τ k))
      = stepWeight τ k * a - stepWeight τ k * Φ (δ d (k + 1)) (stepPt τ k) := by
    intro k; ring
  rw [stateStepOp, tsum_congr hsplit, h2.tsum_sub h1, tsum_mul_right,
    tsum_stepWeight hτ.1, one_mul, stateStepOp]

lemma stateStepIter_sub_const {B B' a : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ)
    (hΨ : InCone B' (fun d τ => Φ d τ - a)) (δ : S → ℕ → S) :
    ∀ (n : ℕ) (d : S), ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
      stateStepIter δ n (fun d τ => Φ d τ - a) d τ = stateStepIter δ n Φ d τ - a := by
  intro n
  induction n with
  | zero => intro d τ _; rfl
  | succ n ih =>
      intro d τ hτ
      have hcΦ := stateStepIter_inCone hΦ δ n
      have hcΨ := stateStepIter_inCone hΨ δ n
      have hkey : InCone B' (fun d τ => stateStepIter δ n Φ d τ - a) := by
        intro e x hx
        have hx' := ih e hx
        simp only []
        rw [← hx']
        exact hcΨ e x hx
      have hstep : stateStepIter δ (n + 1) (fun d τ => Φ d τ - a) d τ
          = stateStepOp δ (fun e y => stateStepIter δ n Φ e y - a) d τ := by
        rw [stateStepIter, stateStepOp, stateStepOp]
        exact tsum_congr fun k => by rw [ih _ (stepPt_mem_Icc hτ.1 k)]
      rw [hstep, stateStepOp_sub_const hcΦ hkey δ d hτ, stateStepIter]

lemma stateStepIter_const_sub {B B' a : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ)
    (hΨ : InCone B' (fun d τ => a - Φ d τ)) (δ : S → ℕ → S) :
    ∀ (n : ℕ) (d : S), ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
      stateStepIter δ n (fun d τ => a - Φ d τ) d τ = a - stateStepIter δ n Φ d τ := by
  intro n
  induction n with
  | zero => intro d τ _; rfl
  | succ n ih =>
      intro d τ hτ
      have hcΦ := stateStepIter_inCone hΦ δ n
      have hcΨ := stateStepIter_inCone hΨ δ n
      have hkey : InCone B' (fun d τ => a - stateStepIter δ n Φ d τ) := by
        intro e x hx
        have hx' := ih e hx
        simp only []
        rw [← hx']
        exact hcΨ e x hx
      have hstep : stateStepIter δ (n + 1) (fun d τ => a - Φ d τ) d τ
          = stateStepOp δ (fun e y => a - stateStepIter δ n Φ e y) d τ := by
        rw [stateStepIter, stateStepOp, stateStepOp]
        exact tsum_congr fun k => by rw [ih _ (stepPt_mem_Icc hτ.1 k)]
      rw [hstep, stateStepOp_const_sub hcΦ hkey δ d hτ, stateStepIter]

/-! ## The range of a family over `S × [0,1]` -/

section Range

variable [Nonempty S]

/-- The set of values a family takes on `S × [0,1]`. -/
def famRange (Φ : S → ℝ → ℝ) : Set ℝ :=
  {v : ℝ | ∃ d : S, ∃ x ∈ Set.Icc (0 : ℝ) 1, Φ d x = v}

lemma famRange_nonempty (Φ : S → ℝ → ℝ) : (famRange Φ).Nonempty :=
  ⟨Φ (Classical.arbitrary S) 0, Classical.arbitrary S, 0, ⟨le_rfl, by norm_num⟩, rfl⟩

lemma famRange_bddAbove {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) : BddAbove (famRange Φ) := by
  refine ⟨B, ?_⟩
  rintro v ⟨d, x, hx, rfl⟩
  exact (hΦ d x hx).2

lemma famRange_bddBelow {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) : BddBelow (famRange Φ) := by
  refine ⟨0, ?_⟩
  rintro v ⟨d, x, hx, rfl⟩
  exact (hΦ d x hx).1

/-- The supremum of the family over `S × [0,1]`. -/
noncomputable def famSup (Φ : S → ℝ → ℝ) : ℝ := sSup (famRange Φ)

/-- The infimum of the family over `S × [0,1]`. -/
noncomputable def famInf (Φ : S → ℝ → ℝ) : ℝ := sInf (famRange Φ)

lemma le_famSup {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) (d : S) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : Φ d x ≤ famSup Φ :=
  le_csSup (famRange_bddAbove hΦ) ⟨d, x, hx, rfl⟩

lemma famInf_le {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) (d : S) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : famInf Φ ≤ Φ d x :=
  csInf_le (famRange_bddBelow hΦ) ⟨d, x, hx, rfl⟩

lemma famInf_nonneg {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) : 0 ≤ famInf Φ :=
  le_csInf (famRange_nonempty Φ) (by rintro v ⟨d, x, hx, rfl⟩; exact (hΦ d x hx).1)

lemma famInf_le_famSup {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) : famInf Φ ≤ famSup Φ := by
  obtain ⟨v, hv⟩ := famRange_nonempty Φ
  obtain ⟨d, x, hx, rfl⟩ := hv
  exact (famInf_le hΦ d hx).trans (le_famSup hΦ d hx)

lemma famSup_le_bound {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) : famSup Φ ≤ B :=
  csSup_le (famRange_nonempty Φ) (by rintro v ⟨d, x, hx, rfl⟩; exact (hΦ d x hx).2)

lemma exists_gt_famSup_sub {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : S, ∃ x ∈ Set.Icc (0 : ℝ) 1, famSup Φ - ε < Φ d x := by
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup (famRange_nonempty Φ)
    (by linarith : famSup Φ - ε < famSup Φ)
  obtain ⟨d, x, hx, rfl⟩ := hv
  exact ⟨d, x, hx, hlt⟩

lemma exists_lt_famInf_add {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : S, ∃ x ∈ Set.Icc (0 : ℝ) 1, Φ d x < famInf Φ + ε := by
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_csInf_lt (famRange_nonempty Φ)
    (by linarith : famInf Φ < famInf Φ + ε)
  obtain ⟨d, x, hx, rfl⟩ := hv
  exact ⟨d, x, hx, hlt⟩

end Range

/-! ## The two-sided Doeblin step -/

/-- **The Doeblin contraction of the oscillation.**  Suppose every pair of states is joined by a
genuine digit word of length exactly `M` whose weight is at least `β > 0`, and the family varies
by at most `q` in the tail parameter at a fixed state.  Then after `M` steps the family is
squeezed into `[m + β(M' − q), M' − β(M' − q)]` where `m = famInf Φ`, `M' = famSup Φ`
(writing `M'−m` for the oscillation) — i.e.

`osc(L^M Φ) ≤ (1 − 2β)·osc(Φ) + 2β·q`.

The classical one-point Doeblin argument: pick a state/parameter where `Φ` is within `ε` of its
supremum, drive `d` there by the reach word, and apply `stateStepIter_ge_word` to the
nonnegative family `Φ − m`; symmetrically with `M' − Φ`. Only ONE word per `(d, target)` is
needed, so no expansion of `L^M` over words is required. -/
theorem stateStepIter_doeblin_two_sided [Nonempty S] {B q β : ℝ} {Φ : S → ℝ → ℝ}
    (hΦ : InCone B Φ) (δ : S → ℕ → S) (M : ℕ) (hβ : 0 < β) (hq : 0 ≤ q)
    (hreach : ∀ d t : S, ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = t ∧ β ≤ wordWeight w)
    (hosc : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |Φ e x - Φ e y| ≤ q)
    (d : S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    famInf Φ + β * (famSup Φ - famInf Φ - q) ≤ stateStepIter δ M Φ d τ ∧
      stateStepIter δ M Φ d τ ≤ famSup Φ - β * (famSup Φ - famInf Φ - q) := by
  have hm0 : 0 ≤ famInf Φ := famInf_nonneg hΦ
  have hMB : famSup Φ ≤ B := famSup_le_bound hΦ
  -- the two shifted families
  have hΨ1 : InCone B (fun e y => Φ e y - famInf Φ) := by
    intro e x hx
    exact ⟨sub_nonneg.mpr (famInf_le hΦ e hx), by linarith [(hΦ e x hx).2]⟩
  have hΨ2 : InCone B (fun e y => famSup Φ - Φ e y) := by
    intro e x hx
    exact ⟨sub_nonneg.mpr (le_famSup hΦ e hx), by linarith [(hΦ e x hx).1]⟩
  constructor
  · -- lower bound
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨t₀, x₀, hx₀, hgt⟩ := exists_gt_famSup_sub hΦ (ε := ε / (β + 1))
      (by positivity)
    obtain ⟨w, hwlen, hwpos, hwrun, hwβ⟩ := hreach d t₀
    set c : ℝ := max 0 (Φ t₀ x₀ - q - famInf Φ) with hc
    have hc0 : 0 ≤ c := le_max_left _ _
    have hcle : ∀ y ∈ Set.Icc (0 : ℝ) 1, c ≤ (fun e y => Φ e y - famInf Φ) (runState δ d w) y := by
      intro y hy
      rw [hwrun]
      refine max_le (sub_nonneg.mpr (famInf_le hΦ t₀ hy)) ?_
      have := abs_le.mp (hosc t₀ x₀ hx₀ y hy)
      simp only []
      linarith [this.1]
    have hkey := stateStepIter_ge_word hΨ1 δ hc0 w hwpos d hcle hτ
    rw [hwlen] at hkey
    have heq := stateStepIter_sub_const hΦ hΨ1 δ M d hτ
    rw [heq] at hkey
    have hcge : Φ t₀ x₀ - q - famInf Φ ≤ c := le_max_right _ _
    have hwc : β * c ≤ wordWeight w * c := mul_le_mul_of_nonneg_right hwβ hc0
    have hεb : famSup Φ - ε / (β + 1) < Φ t₀ x₀ := hgt
    have hfin : β * (famSup Φ - famInf Φ - q) - β * (ε / (β + 1)) ≤ wordWeight w * c := by
      refine le_trans ?_ hwc
      have : famSup Φ - ε / (β + 1) - q - famInf Φ ≤ c := by linarith
      nlinarith [hβ]
    have hsmall : β * (ε / (β + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hε.le]
    linarith
  · -- upper bound
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨t₁, x₁, hx₁, hlt⟩ := exists_lt_famInf_add hΦ (ε := ε / (β + 1)) (by positivity)
    obtain ⟨w, hwlen, hwpos, hwrun, hwβ⟩ := hreach d t₁
    set c : ℝ := max 0 (famSup Φ - (Φ t₁ x₁ + q)) with hc
    have hc0 : 0 ≤ c := le_max_left _ _
    have hcle : ∀ y ∈ Set.Icc (0 : ℝ) 1, c ≤ (fun e y => famSup Φ - Φ e y) (runState δ d w) y := by
      intro y hy
      rw [hwrun]
      refine max_le (sub_nonneg.mpr (le_famSup hΦ t₁ hy)) ?_
      have := abs_le.mp (hosc t₁ x₁ hx₁ y hy)
      simp only []
      linarith [this.2]
    have hkey := stateStepIter_ge_word hΨ2 δ hc0 w hwpos d hcle hτ
    rw [hwlen] at hkey
    have heq := stateStepIter_const_sub hΦ hΨ2 δ M d hτ
    rw [heq] at hkey
    have hcge : famSup Φ - (Φ t₁ x₁ + q) ≤ c := le_max_right _ _
    have hwc : β * c ≤ wordWeight w * c := mul_le_mul_of_nonneg_right hwβ hc0
    have hfin : β * (famSup Φ - famInf Φ - q) - β * (ε / (β + 1)) ≤ wordWeight w * c := by
      refine le_trans ?_ hwc
      have : famSup Φ - famInf Φ - ε / (β + 1) - q ≤ c := by linarith
      nlinarith [hβ]
    have hsmall : β * (ε / (β + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hε.le]
    linarith

/-! ## Monotonicity of the range, and the shifted iterate -/

/-- The operator is an average, so it never widens the range. -/
lemma stateStepOp_mem_range_bounds [Nonempty S] {B : ℝ} {Φ : S → ℝ → ℝ} (hΦ : InCone B Φ)
    (δ : S → ℕ → S) (d : S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    famInf Φ ≤ stateStepOp δ Φ d τ ∧ stateStepOp δ Φ d τ ≤ famSup Φ := by
  have hsum := summable_stateStep hΦ δ d hτ
  constructor
  · calc famInf Φ = ∑' k : ℕ, stepWeight τ k * famInf Φ := by
          rw [tsum_mul_right, tsum_stepWeight hτ.1, one_mul]
      _ ≤ stateStepOp δ Φ d τ :=
          ((summable_stepWeight hτ.1).mul_right _).tsum_le_tsum
            (fun k => mul_le_mul_of_nonneg_left
              (famInf_le hΦ _ (stepPt_mem_Icc hτ.1 k)) (stepWeight_nonneg hτ.1 k)) hsum
  · calc stateStepOp δ Φ d τ ≤ ∑' k : ℕ, stepWeight τ k * famSup Φ :=
          hsum.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
            (le_famSup hΦ _ (stepPt_mem_Icc hτ.1 k)) (stepWeight_nonneg hτ.1 k))
            ((summable_stepWeight hτ.1).mul_right _)
      _ = famSup Φ := by rw [tsum_mul_right, tsum_stepWeight hτ.1, one_mul]

/-- `F_{n+m}(·,s) = Lᵐ F_n(·,s)` on `[0,1]`. -/
theorem stateHorizonIntegral_add (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (s : S) (n : ℕ) :
    ∀ (m : ℕ) (d : S), ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
      stateHorizonIntegral δ A (n + m) d s τ
        = stateStepIter δ m (fun d' τ' => stateHorizonIntegral δ A n d' s τ') d τ := by
  intro m
  induction m with
  | zero => intro d τ _; rfl
  | succ m ih =>
      intro d τ hτ
      have hstep : n + (m + 1) = (n + m) + 1 := by omega
      rw [hstep, stateHorizonIntegral_succ δ hA (n + m) d s hτ, stateStepIter,
        stateStepOp, stateStepOp]
      exact tsum_congr fun k => by rw [ih _ (stepPt_mem_Icc hτ.1 k)]

/-- On `[0,1]` the log metric has diameter `log 2`. -/
lemma abs_log_sub_le_log_two {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : |Real.log (1 + x) - Real.log (1 + y)| ≤ Real.log 2 := by
  have hb : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.log (1 + z) ∧ Real.log (1 + z) ≤ Real.log 2 := by
    intro z hz
    exact ⟨Real.log_nonneg (by linarith [hz.1]),
      Real.log_le_log (by linarith [hz.1]) (by linarith [hz.2])⟩
  obtain ⟨hx0, hx2⟩ := hb x hx
  obtain ⟨hy0, hy2⟩ := hb y hy
  rw [abs_le]
  constructor <;> linarith

/-! ## One step of the joint recursion -/

lemma stateStepIter_add (δ : S → ℕ → S) (b : ℕ) :
    ∀ (a : ℕ) (Φ : S → ℝ → ℝ),
      stateStepIter δ (a + b) Φ = stateStepIter δ a (stateStepIter δ b Φ) := by
  intro a
  induction a with
  | zero => intro Φ; rw [Nat.zero_add]; rfl
  | succ a ih => intro Φ; rw [show a + 1 + b = (a + b) + 1 by omega, stateStepIter,
      ih Φ, stateStepIter]

/-- One step of the pair `(log-Lipschitz constant, oscillation)`. -/
lemma stateStepOp_step_bounds [Nonempty S] {B Λ Ω : ℝ} {Ψ : S → ℝ → ℝ}
    (hΨ : InCone B Ψ) (δ : S → ℕ → S) (hΛ : 0 ≤ Λ) (hΩ : 0 ≤ Ω)
    (hlip : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Ψ e x - Ψ e y| ≤ Λ * |Real.log (1 + x) - Real.log (1 + y)|)
    (hosc : famSup Ψ - famInf Ψ ≤ Ω) :
    (∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |stateStepOp δ Ψ e x - stateStepOp δ Ψ e y|
        ≤ ((2 / 5) * Λ + (3 / 10) * Ω) * |Real.log (1 + x) - Real.log (1 + y)|)
    ∧ famSup (stateStepOp δ Ψ) - famInf (stateStepOp δ Ψ) ≤ Ω := by
  constructor
  · intro e x hx y hy
    have hc : ∀ f : S, ∀ z ∈ Set.Icc (0 : ℝ) 1,
        |Ψ f z - (famSup Ψ + famInf Ψ) / 2| ≤ Ω / 2 := by
      intro f z hz
      have h1 := famInf_le hΨ f hz
      have h2 := le_famSup hΨ f hz
      rw [abs_le]
      constructor <;> linarith
    have := stateStepOp_logLipschitz hΛ (by linarith : (0:ℝ) ≤ Ω / 2) hΨ δ e hlip hc hx hy
    calc |stateStepOp δ Ψ e x - stateStepOp δ Ψ e y|
        ≤ ((2 / 5) * Λ + (3 / 5) * (Ω / 2)) * |Real.log (1 + x) - Real.log (1 + y)| := this
      _ = ((2 / 5) * Λ + (3 / 10) * Ω) * |Real.log (1 + x) - Real.log (1 + y)| := by ring
  · have hub : famSup (stateStepOp δ Ψ) ≤ famSup Ψ := by
      refine csSup_le (famRange_nonempty _) ?_
      rintro v ⟨d, x, hx, rfl⟩
      exact (stateStepOp_mem_range_bounds hΨ δ d hx).2
    have hlb : famInf Ψ ≤ famInf (stateStepOp δ Ψ) := by
      refine le_csInf (famRange_nonempty _) ?_
      rintro v ⟨d, x, hx, rfl⟩
      exact (stateStepOp_mem_range_bounds hΨ δ d hx).1
    linarith

/-! ## The geometric decay of the oscillation -/

/-- `j` single steps: the log-Lipschitz constant decays like `(2/5)ʲ` with an `Ω/2` floor, and
the oscillation never grows. -/
lemma stateStepIter_lip_bound [Nonempty S] {B Λ Ω : ℝ} {Ψ : S → ℝ → ℝ}
    (hΨ : InCone B Ψ) (δ : S → ℕ → S) (hΛ : 0 ≤ Λ) (hΩ : 0 ≤ Ω)
    (hlip : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Ψ e x - Ψ e y| ≤ Λ * |Real.log (1 + x) - Real.log (1 + y)|)
    (hosc : famSup Ψ - famInf Ψ ≤ Ω) :
    ∀ j : ℕ,
      (∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |stateStepIter δ j Ψ e x - stateStepIter δ j Ψ e y|
          ≤ ((2 / 5 : ℝ) ^ j * Λ + (1 / 2) * Ω) * |Real.log (1 + x) - Real.log (1 + y)|) ∧
      famSup (stateStepIter δ j Ψ) - famInf (stateStepIter δ j Ψ) ≤ Ω := by
  intro j
  induction j with
  | zero =>
      refine ⟨fun e x hx y hy => ?_, by simpa [stateStepIter] using hosc⟩
      refine (hlip e x hx y hy).trans ?_
      refine mul_le_mul_of_nonneg_right (by simp; linarith) (abs_nonneg _)
  | succ j ih =>
      obtain ⟨hl, ho⟩ := ih
      have hcone : InCone B (stateStepIter δ j Ψ) := stateStepIter_inCone hΨ δ j
      have hΛj : 0 ≤ (2 / 5 : ℝ) ^ j * Λ + (1 / 2) * Ω := by positivity
      have h := stateStepOp_step_bounds hcone δ hΛj hΩ hl ho
      refine ⟨fun e x hx y hy => ?_, ?_⟩
      · rw [stateStepIter]
        refine (h.1 e x hx y hy).trans ?_
        refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (abs_nonneg _)
        rw [pow_succ]; ring
      · rw [stateStepIter]; exact h.2

set_option maxHeartbeats 800000 in
/-- **The joint contraction.**  `M ≥ 2` single steps contract the log-Lipschitz constant by
`(2/5)^M ≤ 4/25`, one Doeblin block of length `M` contracts the oscillation by `1 − 2β`, and the
Lyapunov function `V = osc + 2β·Lip` contracts by `1 − β` per block, because

`log 2 + (2/5)^M ≤ 0.6932 + 0.16 = 0.8532 ≤ 1 − β` whenever `β ≤ 1/8`.

Hence `osc(L^{Mm} Φ) ≤ (1−β)ᵐ (Ω₀ + 2β Λ₀)`. -/
theorem stateStepIter_osc_geom [Nonempty S] {B β Λ₀ Ω₀ : ℝ} {Φ : S → ℝ → ℝ}
    (hΦ : InCone B Φ) (δ : S → ℕ → S) (hβ : 0 < β) (hβ' : β ≤ 1 / 8)
    (M : ℕ) (hM : 2 ≤ M)
    (hreach : ∀ d t : S, ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = t ∧ β ≤ wordWeight w)
    (hΛ₀ : 0 ≤ Λ₀) (hΩ₀ : 0 ≤ Ω₀)
    (hlip0 : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Φ e x - Φ e y| ≤ Λ₀ * |Real.log (1 + x) - Real.log (1 + y)|)
    (hosc0 : famSup Φ - famInf Φ ≤ Ω₀) (m : ℕ) :
    famSup (stateStepIter δ (M * m) Φ) - famInf (stateStepIter δ (M * m) Φ)
      ≤ (1 - β) ^ m * (Ω₀ + 2 * β * Λ₀) := by
  have hlog2 : Real.log 2 ≤ 0.6932 := le_of_lt (lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num))
  have hlog2p : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpowM : (2 / 5 : ℝ) ^ M ≤ 4 / 25 := by
    calc (2 / 5 : ℝ) ^ M ≤ (2 / 5 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hM
      _ = 4 / 25 := by norm_num
  have hpowMnn : (0 : ℝ) ≤ (2 / 5 : ℝ) ^ M := by positivity
  have key : ∀ m : ℕ, ∃ Λ Ω : ℝ, 0 ≤ Λ ∧ 0 ≤ Ω ∧
      (∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |stateStepIter δ (M * m) Φ e x - stateStepIter δ (M * m) Φ e y|
          ≤ Λ * |Real.log (1 + x) - Real.log (1 + y)|) ∧
      (famSup (stateStepIter δ (M * m) Φ) - famInf (stateStepIter δ (M * m) Φ) ≤ Ω) ∧
      Ω + 2 * β * Λ ≤ (1 - β) ^ m * (Ω₀ + 2 * β * Λ₀) := by
    intro m
    induction m with
    | zero =>
        refine ⟨Λ₀, Ω₀, hΛ₀, hΩ₀, ?_, ?_, by simp⟩
        · rw [show M * 0 = 0 by omega]; exact hlip0
        · rw [show M * 0 = 0 by omega]; exact hosc0
    | succ m ih =>
        obtain ⟨Λ, Ω, hΛ, hΩ, hlip, hosc, hV⟩ := ih
        set Ψ : S → ℝ → ℝ := stateStepIter δ (M * m) Φ with hΨdef
        have hΨ : InCone B Ψ := stateStepIter_inCone hΦ δ (M * m)
        have hsplit : stateStepIter δ (M * (m + 1)) Φ = stateStepIter δ M Ψ := by
          rw [hΨdef, ← stateStepIter_add δ (M * m) M Φ, Nat.mul_succ, Nat.add_comm]
        -- the Lipschitz side
        have hmulti := stateStepIter_lip_bound hΨ δ hΛ hΩ hlip hosc M
        set ΛM : ℝ := (2 / 5 : ℝ) ^ M * Λ + (1 / 2) * Ω with hΛM
        have hΛMp : 0 ≤ ΛM := by rw [hΛM]; positivity
        -- the Doeblin side
        set q : ℝ := Λ * Real.log 2 with hq
        have hqnn : 0 ≤ q := by rw [hq]; positivity
        have hoscq : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
            |Ψ e x - Ψ e y| ≤ q := by
          intro e x hx y hy
          refine (hlip e x hx y hy).trans ?_
          rw [hq]
          exact mul_le_mul_of_nonneg_left (abs_log_sub_le_log_two hx hy) hΛ
        have hdoeb := fun (d : S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) =>
          stateStepIter_doeblin_two_sided hΨ δ M hβ hqnn hreach hoscq d hτ
        have hub : famSup (stateStepIter δ (M * (m + 1)) Φ)
            ≤ famSup Ψ - β * (famSup Ψ - famInf Ψ - q) := by
          rw [hsplit]
          refine csSup_le (famRange_nonempty _) ?_
          rintro v ⟨d, x, hx, rfl⟩
          exact (hdoeb d hx).2
        have hlb : famInf Ψ + β * (famSup Ψ - famInf Ψ - q)
            ≤ famInf (stateStepIter δ (M * (m + 1)) Φ) := by
          rw [hsplit]
          refine le_csInf (famRange_nonempty _) ?_
          rintro v ⟨d, x, hx, rfl⟩
          exact (hdoeb d hx).1
        set Ω' : ℝ := (1 - 2 * β) * Ω + 2 * β * q with hΩ'
        have hΩ'p : 0 ≤ Ω' := by rw [hΩ']; nlinarith
        have hoscnew : famSup (stateStepIter δ (M * (m + 1)) Φ)
            - famInf (stateStepIter δ (M * (m + 1)) Φ) ≤ Ω' := by
          have ho := famInf_le_famSup hΨ
          rw [hΩ']
          nlinarith [hosc, hβ.le, hβ']
        refine ⟨ΛM, Ω', hΛMp, hΩ'p, ?_, hoscnew, ?_⟩
        · rw [hsplit]; exact hmulti.1
        · have hstep : Ω' + 2 * β * ΛM ≤ (1 - β) * (Ω + 2 * β * Λ) := by
            rw [hΩ', hΛM, hq]
            nlinarith [hΩ, hΛ, hβ.le, hβ', hlog2, hlog2p, hpowM, hpowMnn,
              mul_nonneg hβ.le hΛ, mul_nonneg hβ.le hΩ,
              mul_nonneg (mul_nonneg hβ.le hβ.le) hΛ,
              mul_nonneg hΛ (sub_nonneg.mpr hpowM)]
          calc Ω' + 2 * β * ΛM ≤ (1 - β) * (Ω + 2 * β * Λ) := hstep
            _ ≤ (1 - β) * ((1 - β) ^ m * (Ω₀ + 2 * β * Λ₀)) :=
                mul_le_mul_of_nonneg_left hV (by linarith)
            _ = (1 - β) ^ (m + 1) * (Ω₀ + 2 * β * Λ₀) := by ring
  obtain ⟨Λ, Ω, hΛ, hΩ, -, hosc, hV⟩ := key m
  have : 0 ≤ 2 * β * Λ := by positivity
  linarith

/-! ## Assembly helpers -/

/-- `F_0(d,s) = [d = s]·G_0`. -/
lemma stateHorizonIntegral_zero (δ : S → ℕ → S) (A : Set ℝ) (d s : S) (τ : ℝ) :
    stateHorizonIntegral δ A 0 d s τ = if d = s then horizonIntegral A 0 τ else 0 := by
  by_cases h : d = s
  · have hset : stateHorizonSet δ A 0 d s = horizonSet A 0 := by
      simp [stateHorizonSet, cfWord, runState_nil, h]
    rw [stateHorizonIntegral, hset, if_pos h, horizonIntegral]
  · have hset : stateHorizonSet δ A 0 d s = (∅ : Set ℝ) := by
      simp [stateHorizonSet, cfWord, runState_nil, h]
    rw [stateHorizonIntegral, hset, if_neg h, Measure.restrict_empty, integral_zero_measure]

/-- `G₀ ≤ 4 log 2 · γ(A)`: on `[0,1]²` one has `h_t ≤ 2 ≤ 4/(1+y)`. -/
lemma horizonIntegral_zero_le {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    horizonIntegral A 0 t ≤ 4 * Real.log 2 * (gaussMeasure A).toReal := by
  have hB0 : horizonSet A 0 = A := by
    rw [horizonSet, Function.iterate_zero, Set.preimage_id,
      Set.inter_eq_self_of_subset_right hA1]
  have hint : IntegrableOn (tailDensity t) A volume :=
    (integrableOn_tailDensity ht.1).mono_set hA1
  have hg : IntegrableOn (fun y => 2 * (2 * Real.log 2) * gaussDensityReal y) A volume :=
    (integrableOn_gaussDensityReal hA1).const_mul _
  rw [horizonIntegral, hB0]
  calc ∫ y in A, tailDensity t y
      ≤ ∫ y in A, 2 * (2 * Real.log 2) * gaussDensityReal y := by
        refine setIntegral_mono_on hint hg hA fun y hy => ?_
        obtain ⟨hy0, hy1⟩ := hA1 hy
        have hxy : (0 : ℝ) ≤ t * y := mul_nonneg ht.1 hy0.le
        have hden : (1 : ℝ) ≤ (1 + t * y) ^ 2 := by nlinarith
        have h2 : tailDensity t y ≤ 2 / (1 + y) := by
          rw [tailDensity, div_le_div_iff₀ (by nlinarith) (by linarith)]
          nlinarith [ht.2]
        have h3 : (2 : ℝ) / (1 + y) = 2 * Real.log 2 * gaussDensityReal y :=
          inv_one_add_eq_log_mul_gaussDensityReal y
        rw [h3] at h2
        have hgd : 0 ≤ gaussDensityReal y := by
          rw [gaussDensityReal]; positivity
        nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
    _ = 4 * Real.log 2 * (gaussMeasure A).toReal := by
        rw [integral_const_mul, ← gaussMeasure_toReal_eq hA hA1]; ring

/-- The oscillation never grows along the iteration. -/
lemma stateStepIter_osc_le [Nonempty S] {B Ω : ℝ} {Ψ : S → ℝ → ℝ} (hΨ : InCone B Ψ)
    (δ : S → ℕ → S) (hosc : famSup Ψ - famInf Ψ ≤ Ω) :
    ∀ j : ℕ, famSup (stateStepIter δ j Ψ) - famInf (stateStepIter δ j Ψ) ≤ Ω := by
  intro j
  induction j with
  | zero => simpa [stateStepIter] using hosc
  | succ j ih =>
      have hcone : InCone B (stateStepIter δ j Ψ) := stateStepIter_inCone hΨ δ j
      have hub : famSup (stateStepIter δ (j + 1) Ψ) ≤ famSup (stateStepIter δ j Ψ) := by
        rw [stateStepIter]
        refine csSup_le (famRange_nonempty _) ?_
        rintro v ⟨d, x, hx, rfl⟩
        exact (stateStepOp_mem_range_bounds hcone δ d hx).2
      have hlb : famInf (stateStepIter δ j Ψ) ≤ famInf (stateStepIter δ (j + 1) Ψ) := by
        rw [stateStepIter]
        refine le_csInf (famRange_nonempty _) ?_
        rintro v ⟨d, x, hx, rfl⟩
        exact (stateStepOp_mem_range_bounds hcone δ d hx).1
      linarith

/-- Blockwise geometric decay converted to a genuine `θⁿ`, with `θ = (1−β)^{1/M}`. -/
lemma geom_block_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    (1 - β) ^ (n / M) ≤ (1 - β)⁻¹ * ((1 - β) ^ ((M : ℝ)⁻¹)) ^ n := by
  have hb0 : (0 : ℝ) < 1 - β := by linarith
  have hb1 : (1 : ℝ) - β ≤ 1 := by linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hrpow : ((1 - β) ^ ((M : ℝ)⁻¹)) ^ n = (1 - β) ^ ((n : ℝ) / M) := by
    rw [← Real.rpow_natCast ((1 - β) ^ ((M : ℝ)⁻¹)) n, ← Real.rpow_mul hb0.le]
    congr 1
    field_simp
  have hexp : (n : ℝ) / M - 1 ≤ ((n / M : ℕ) : ℝ) := by
    have h2 : n < (n / M + 1) * M := by
      have hd : M * (n / M) + n % M = n := Nat.div_add_mod n M
      have hm : n % M < M := Nat.mod_lt _ hM
      nlinarith [hd, hm]
    have h3 : (n : ℝ) < (((n / M : ℕ) : ℝ) + 1) * M := by
      have := (Nat.cast_lt (α := ℝ)).mpr h2
      push_cast at this
      linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hMR]
    nlinarith
  have hstep : (1 - β) ^ ((n / M : ℕ) : ℝ) ≤ (1 - β) ^ ((n : ℝ) / M - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hexp
  have hval : (1 - β) ^ ((n : ℝ) / M - 1) = (1 - β)⁻¹ * (1 - β) ^ ((n : ℝ) / M) := by
    rw [Real.rpow_sub hb0, Real.rpow_one]
    field_simp
  rw [hrpow, ← hval, ← Real.rpow_natCast (1 - β) (n / M)]
  exact hstep

/-- Two families agreeing on `S × [0,1]` have the same range. -/
lemma famRange_congr [Nonempty S] {Φ Ψ : S → ℝ → ℝ}
    (h : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ e x = Ψ e x) : famRange Φ = famRange Ψ := by
  ext v
  constructor
  · rintro ⟨d, x, hx, rfl⟩; exact ⟨d, x, hx, (h d x hx).symm⟩
  · rintro ⟨d, x, hx, rfl⟩; exact ⟨d, x, hx, h d x hx⟩

/-! ## The crux -/

set_option maxHeartbeats 1000000 in
/-- **The crux of Vandehey 2017 Theorem 1.1**, as one named statement: the refined horizon
integral equidistributes over the state space, geometrically and uniformly in the tail
parameter and in the initial state.

`N = 1` (a one-state automaton) is exactly `CFPsiPin.horizonIntegral_pin_geom`, via
`sum_stateHorizonIntegral`.  The two hypotheses are the ones the class automaton of
`VandeheyClass` supplies: a uniform Doeblin word length (`Doeblin.exists_classWord_three`) and
bijectivity of every digit step (`VandeheyRenewal.classStep_bijective`, which forces the
invariant law to be *uniform* — `sum_classKernel_col`).

**Proof.**  A Lyapunov argument on the pair `(oscillation, log-Lipschitz constant)` over
`S × [0,1]`:

* `stateStepOp_logLipschitz` contracts the tail-parameter direction by `2/5` per step, at the
  cost of `(3/5)·r` where `r` is half the oscillation;
* `stateStepIter_doeblin_two_sided` contracts the state direction by `1 − 2β` per `M`-block, at
  the cost of `2β·q` where `q ≤ log 2 ·` (log-Lipschitz constant);
* `stateStepIter_osc_geom` combines them: `V = osc + 2β·Lip` obeys `V' ≤ (1−β)V` because
  `log 2 + (2/5)^M ≤ 0.6932 + 0.16 ≤ 1 − β` for `β ≤ 1/8` and `M ≥ 2`.

The limiting constant needs no computation: `sum_stateHorizonIntegral` and
`sum_over_initial_stateHorizonIntegral` make the family doubly stochastic, so
`(card S)⁻¹·G_n(τ)` is the average of the values `F_n(d,s)(τ)` over `d` and therefore lies
between their inf and sup; `CFPsiPin.horizonIntegral_pin_geom` sends `G_n(τ)` to `γ(A)`. -/
theorem stateHorizonIntegral_pin [Nonempty S] (δ : S → ℕ → S) {A : Set ℝ}
    (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hreach : ∀ d s : S, ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = s)
    (hbij : ∀ a : ℕ, Function.Bijective (fun d : S => δ d a)) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ (n : ℕ) (d s : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ A n d s τ
          - (Fintype.card S : ℝ)⁻¹ * (gaussMeasure A).toReal|
        ≤ C * θ ^ n * (gaussMeasure A).toReal := by
  classical
  set γA : ℝ := (gaussMeasure A).toReal with hγA
  have hγ0 : 0 ≤ γA := ENNReal.toReal_nonneg
  have hlog2 : Real.log 2 ≤ 0.6932 := le_of_lt (lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num))
  have hlog2p : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hM0 : 0 < M := by omega
  -- ### the uniform Doeblin weight `β`
  choose w hwlen hwpos hwrun using hreach
  obtain ⟨p, -, hpmin⟩ := Finset.exists_min_image (Finset.univ : Finset (S × S))
    (fun q => wordWeight (w q.1 q.2))
    ⟨(Classical.arbitrary S, Classical.arbitrary S), Finset.mem_univ _⟩
  set β : ℝ := min (wordWeight (w p.1 p.2)) (1 / 8) with hβdef
  have hβpos : 0 < β := lt_min wordWeight_pos (by norm_num)
  have hβ8 : β ≤ 1 / 8 := min_le_right _ _
  have hβ1 : β < 1 := by linarith
  have hreach' : ∀ d t : S, ∃ v : List ℕ, v.length = M ∧ (∀ a ∈ v, 1 ≤ a) ∧
      runState δ d v = t ∧ β ≤ wordWeight v := fun d t =>
    ⟨w d t, hwlen d t, hwpos d t, hwrun d t,
      le_trans (min_le_left _ _) (hpmin (d, t) (Finset.mem_univ _))⟩
  -- ### the rate
  set θ₁ : ℝ := (1 - β) ^ ((M : ℝ)⁻¹) with hθ₁
  have hθ₁pos : 0 < θ₁ := Real.rpow_pos_of_pos (by linarith) _
  have hθ₁lt : θ₁ < 1 :=
    Real.rpow_lt_one (by linarith) (by linarith) (by positivity)
  set θ : ℝ := max θ₁ (79 / 100) with hθ
  have hθpos : 0 < θ := lt_of_lt_of_le hθ₁pos (le_max_left _ _)
  have hθlt : θ < 1 := max_lt hθ₁lt (by norm_num)
  refine ⟨4 * (1 - β)⁻¹ + 1, θ, by positivity, hθpos.le, hθlt, ?_⟩
  intro n d s τ hτ
  -- ### the initial family `F₀(·,s)`
  set Φ : S → ℝ → ℝ := fun d' τ' => stateHorizonIntegral δ A 0 d' s τ' with hΦdef
  have hΦcone : InCone 2 Φ := fun e x hx =>
    ⟨stateHorizonIntegral_nonneg δ hA 0 e s hx.1, stateHorizonIntegral_le_two δ hA 0 e s hx⟩
  set Λ₀ : ℝ := 2 * Real.log 2 * γA with hΛ₀d
  set Ω₀ : ℝ := 4 * Real.log 2 * γA with hΩ₀d
  have hΛ₀ : 0 ≤ Λ₀ := by rw [hΛ₀d]; positivity
  have hΩ₀ : 0 ≤ Ω₀ := by rw [hΩ₀d]; positivity
  have hlip0 : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Φ e x - Φ e y| ≤ Λ₀ * |Real.log (1 + x) - Real.log (1 + y)| := by
    intro e x hx y hy
    rw [hΦdef]
    simp only [stateHorizonIntegral_zero]
    by_cases h : e = s
    · rw [if_pos h, if_pos h]
      exact horizonIntegral_zero_logLip hA hA1 hx hy
    · rw [if_neg h, if_neg h, sub_self, abs_zero]
      positivity
  have hosc0 : famSup Φ - famInf Φ ≤ Ω₀ := by
    have hsup : famSup Φ ≤ Ω₀ := by
      refine csSup_le (famRange_nonempty _) ?_
      rintro v ⟨e, x, hx, rfl⟩
      rw [hΦdef]
      simp only [stateHorizonIntegral_zero]
      by_cases h : e = s
      · rw [if_pos h]; exact horizonIntegral_zero_le hA hA1 hx
      · rw [if_neg h]; exact hΩ₀
    linarith [famInf_nonneg hΦcone]
  -- ### the geometric decay of the oscillation
  have hgeom := stateStepIter_osc_geom hΦcone δ hβpos hβ8 M hM hreach' hΛ₀ hΩ₀ hlip0 hosc0
    (n / M)
  set Ψ : S → ℝ → ℝ := stateStepIter δ (M * (n / M)) Φ with hΨdef
  have hΨcone : InCone 2 Ψ := stateStepIter_inCone hΦcone δ _
  have hr : (n - M * (n / M)) + M * (n / M) = n := by
    have h1 : M * (n / M) ≤ n := Nat.mul_div_le n M
    omega
  have hiter : stateStepIter δ n Φ = stateStepIter δ (n - M * (n / M)) Ψ := by
    rw [hΨdef, ← stateStepIter_add δ (M * (n / M)) (n - M * (n / M)) Φ, hr]
  have hoscn : famSup (stateStepIter δ n Φ) - famInf (stateStepIter δ n Φ)
      ≤ (1 - β) ^ (n / M) * (Ω₀ + 2 * β * Λ₀) := by
    rw [hiter]
    exact stateStepIter_osc_le hΨcone δ hgeom _
  -- ### transfer to `F_n(·,s)`
  set Fn : S → ℝ → ℝ := fun d' τ' => stateHorizonIntegral δ A n d' s τ' with hFn
  have hFneq : ∀ e : S, ∀ x ∈ Set.Icc (0 : ℝ) 1, Fn e x = stateStepIter δ n Φ e x := by
    intro e x hx
    rw [hFn, hΦdef]
    exact stateHorizonIntegral_iter δ hA s n e hx
  have hFrange : famRange Fn = famRange (stateStepIter δ n Φ) := famRange_congr hFneq
  have hoscFn : famSup Fn - famInf Fn ≤ (1 - β) ^ (n / M) * (Ω₀ + 2 * β * Λ₀) := by
    rw [famSup, famInf, hFrange, ← famSup, ← famInf]
    exact hoscn
  have hFncone : InCone 2 Fn := fun e x hx =>
    ⟨stateHorizonIntegral_nonneg δ hA n e s hx.1, stateHorizonIntegral_le_two δ hA n e s hx⟩
  -- ### the centre is the average over the initial state
  have hcard : 0 < Fintype.card S := Fintype.card_pos
  have hcardR : (0 : ℝ) < (Fintype.card S : ℝ) := by exact_mod_cast hcard
  set cen : ℝ := (Fintype.card S : ℝ)⁻¹ * horizonIntegral A n τ with hcen
  have hsum : ∑ d' : S, Fn d' τ = horizonIntegral A n τ :=
    sum_over_initial_stateHorizonIntegral δ hA hbij n s hτ
  have hcen_lb : famInf Fn ≤ cen := by
    have h1 : (Fintype.card S : ℝ) * famInf Fn ≤ horizonIntegral A n τ := by
      rw [← hsum]
      calc (Fintype.card S : ℝ) * famInf Fn = ∑ _d' : S, famInf Fn := by
            rw [Finset.sum_const, Finset.card_univ]; ring
        _ ≤ ∑ d' : S, Fn d' τ :=
            Finset.sum_le_sum fun d' _ => famInf_le hFncone d' hτ
    rw [hcen, le_inv_mul_iff₀ hcardR]
    linarith
  have hcen_ub : cen ≤ famSup Fn := by
    have h1 : horizonIntegral A n τ ≤ (Fintype.card S : ℝ) * famSup Fn := by
      rw [← hsum]
      calc ∑ d' : S, Fn d' τ ≤ ∑ _d' : S, famSup Fn :=
            Finset.sum_le_sum fun d' _ => le_famSup hFncone d' hτ
        _ = (Fintype.card S : ℝ) * famSup Fn := by
            rw [Finset.sum_const, Finset.card_univ]; ring
    rw [hcen, inv_mul_le_iff₀ hcardR]
    linarith
  have hdev : |Fn d τ - cen| ≤ famSup Fn - famInf Fn := by
    have h1 := famInf_le hFncone d hτ
    have h2 := le_famSup hFncone d hτ
    rw [abs_le]
    constructor <;> linarith
  -- ### the centre against `γ(A)`
  have hpin := horizonIntegral_pin_geom hA hA1 n hτ
  have hcen2 : |cen - (Fintype.card S : ℝ)⁻¹ * γA| ≤ (79 / 100 : ℝ) ^ n * γA := by
    have hle1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) := by exact_mod_cast hcard
    have hinv : (Fintype.card S : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact hle1
    have hinvpos : (0 : ℝ) < (Fintype.card S : ℝ)⁻¹ := by positivity
    rw [hcen, ← mul_sub, abs_mul, abs_of_pos hinvpos]
    calc (Fintype.card S : ℝ)⁻¹ * |horizonIntegral A n τ - γA|
        ≤ 1 * ((79 / 100 : ℝ) ^ n * γA) := by
          refine mul_le_mul hinv hpin (abs_nonneg _) (by norm_num)
      _ = (79 / 100 : ℝ) ^ n * γA := by ring
  -- ### combine
  have hV : Ω₀ + 2 * β * Λ₀ ≤ 4 * γA := by
    rw [hΩ₀d, hΛ₀d]
    nlinarith [hγ0, hβpos.le, hβ8, hlog2, hlog2p, mul_nonneg hβpos.le hγ0,
      mul_nonneg (mul_nonneg hβpos.le hlog2p) hγ0]
  have hblock : (1 - β) ^ (n / M) ≤ (1 - β)⁻¹ * θ ^ n := by
    refine (geom_block_bound hβpos hβ1 hM0 n).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ hθ₁pos.le (le_max_left _ _) n
  have h79 : (79 / 100 : ℝ) ^ n ≤ θ ^ n :=
    pow_le_pow_left₀ (by norm_num) (le_max_right _ _) n
  have hθn : (0 : ℝ) ≤ θ ^ n := by positivity
  have hfinal : famSup Fn - famInf Fn ≤ 4 * ((1 - β)⁻¹ * θ ^ n) * γA := by
    refine hoscFn.trans ?_
    calc (1 - β) ^ (n / M) * (Ω₀ + 2 * β * Λ₀)
        ≤ ((1 - β)⁻¹ * θ ^ n) * (4 * γA) := by
          refine mul_le_mul hblock hV (by positivity) (by positivity)
      _ = 4 * ((1 - β)⁻¹ * θ ^ n) * γA := by ring
  calc |stateHorizonIntegral δ A n d s τ - (Fintype.card S : ℝ)⁻¹ * γA|
      = |(Fn d τ - cen) + (cen - (Fintype.card S : ℝ)⁻¹ * γA)| := by
        rw [hFn]; ring_nf
    _ ≤ |Fn d τ - cen| + |cen - (Fintype.card S : ℝ)⁻¹ * γA| := abs_add_le _ _
    _ ≤ 4 * ((1 - β)⁻¹ * θ ^ n) * γA + (79 / 100 : ℝ) ^ n * γA := by
        exact add_le_add (hdev.trans hfinal) hcen2
    _ ≤ 4 * ((1 - β)⁻¹ * θ ^ n) * γA + θ ^ n * γA := by
        gcongr
    _ = (4 * (1 - β)⁻¹ + 1) * θ ^ n * γA := by ring

end VandeheyState

end NormalNumbers
