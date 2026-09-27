/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyRenyi
import NormalNumbers.CFPsiPin

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

/-! ## The crux -/

/-- **The crux of Vandehey 2017 Theorem 1.1**, as one named statement: the refined horizon
integral equidistributes over the state space, geometrically and uniformly in the tail
parameter and in the initial state.

`N = 1` (a one-state automaton) is exactly `CFPsiPin.horizonIntegral_pin_geom`, via
`sum_stateHorizonIntegral`.  The two hypotheses are the ones the class automaton of
`VandeheyClass` supplies: a uniform Doeblin word length (`Doeblin.exists_classWord_three`) and
bijectivity of every digit step (`VandeheyRenewal.classStep_bijective`, which forces the
invariant law to be *uniform* — `sum_classKernel_col`).

**Disclosed `sorry`** — the active crux, decomposed below into
`stateHorizonIntegral_pin_step` (one Doeblin contraction of the projective diameter) and the
iteration.  Route: the operator `stateStepOp` preserves the cone of families that are
nonnegative and log-Lipschitz in `τ` with a small constant; `CFPsiPin.stepOp_logLipschitz`
contracts the `τ`-direction geometrically, and the Doeblin word contracts the state direction
by a factor `1 − Nα` every `M` steps. -/
theorem stateHorizonIntegral_pin (δ : S → ℕ → S) {A : Set ℝ} (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1)
    (M : ℕ) (hM : 0 < M)
    (hreach : ∀ d s : S, ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = s)
    (hbij : ∀ a : ℕ, Function.Bijective (fun d : S => δ d a)) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ (n : ℕ) (d s : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ A n d s τ
          - (Fintype.card S : ℝ)⁻¹ * (gaussMeasure A).toReal|
        ≤ C * θ ^ n * (gaussMeasure A).toReal := by
  sorry

end VandeheyState

end NormalNumbers
