/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GaussErgodic
import NormalNumbers.CFOrbitFreq

/-!
# Krylov–Bogolyubov without compactness: the empirical CDF along an ultrafilter

Step (iii) of the `VandeheyS7.GaussACRigidity` discharge.  The textbook route takes a weak-∗
limit point of the empirical measures (Prokhorov) and then needs the portmanteau theorem and a
mapping theorem for a.e.-continuous functions, because the Gauss map is discontinuous at every
`1/k`.  That is a great deal of machinery.

This module takes a cheaper route, available **because the hypothesis is a uniform absolute
continuity bound**:

* fix one ultrafilter `𝒰 ≤ atTop` and let `limCDF y t := lim_𝒰 (#{j < p : Tʲy < t} / p)`.  The
  values lie in the compact `[0,1]`, so the limit exists — no Prokhorov;
* the AC bound makes `limCDF` **`C`-Lipschitz**, hence monotone and continuous.  So the limit
  object is a `StieltjesFunction`, its measure `ν` is absolutely continuous, and there are no
  continuity-point caveats anywhere — the portmanteau theorem is not needed;
* `T^{-1}(a,b) ∩ (0,1) = ⋃ₖ (1/(k+b), 1/(k+a))` is an **explicit** countable union of intervals,
  whose tail sits in `(0,1/K)` and so has mass `≤ C/K` uniformly in `p`.  That makes
  `ν(T^{-1}(a,b)) = ν((a,b))` an honest limit interchange, with no mapping theorem;
* then `ν` is an a.c. invariant probability, so `ν = γ` by `eq_gaussMeasure_of_ac_invariant`, and
  since *every* ultrafilter limit is `γ`, the whole sequence converges.

## Status

The Lipschitz limit object and its basic theory are proved here.  The remaining steps are named
`sorry`s, each a self-contained statement (see `PENDING_WORK.md`).
-/

namespace NormalNumbers

open MeasureTheory Filter Topology Set

/-- The empirical CDF of the first `p` Gauss iterates of `y`. -/
noncomputable def empCDF (y : ℝ) (p : ℕ) (t : ℝ) : ℝ := blockCount (Ioo 0 t) p y / p

/-- The uniform absolute-continuity hypothesis on the orbit of `y`, with constant `C`. -/
def OrbitACHyp (y C : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ p : ℕ in atTop, blockCount (Ioo a b) p y / p ≤ C * (b - a) + ε

/-! ## Elementary bounds on `blockCount` -/

lemma blockIndic_nonneg (A : Set ℝ) (x : ℝ) : 0 ≤ blockIndic A x := by
  rw [blockIndic]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma blockIndic_le_one (A : Set ℝ) (x : ℝ) : blockIndic A x ≤ 1 := by
  rw [blockIndic]
  by_cases h : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma blockCount_nonneg (A : Set ℝ) (p : ℕ) (y : ℝ) : 0 ≤ blockCount A p y := by
  rw [blockCount_apply]
  exact Finset.sum_nonneg fun k _ => blockIndic_nonneg A _

lemma blockCount_le_card (A : Set ℝ) (p : ℕ) (y : ℝ) : blockCount A p y ≤ p := by
  rw [blockCount_apply]
  calc ∑ k ∈ Finset.range p, blockIndic A (gaussMap^[k] y)
      ≤ ∑ _k ∈ Finset.range p, (1:ℝ) := Finset.sum_le_sum fun k _ => blockIndic_le_one A _
    _ = p := by simp

lemma blockCount_mono {A B : Set ℝ} (hAB : A ⊆ B) (p : ℕ) (y : ℝ) :
    blockCount A p y ≤ blockCount B p y := by
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [blockIndic, blockIndic]
  by_cases h : gaussMap^[k] y ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hAB h)]
  · rw [Set.indicator_of_notMem h]
    exact blockIndic_nonneg B _

lemma empCDF_mem_Icc (y : ℝ) (p : ℕ) (t : ℝ) : empCDF y p t ∈ Icc (0:ℝ) 1 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [empCDF]
  · have hpR : (0:ℝ) < p := by exact_mod_cast hp
    rw [empCDF]
    refine ⟨div_nonneg (blockCount_nonneg _ _ _) hpR.le, ?_⟩
    rw [div_le_one hpR]
    exact blockCount_le_card _ _ _

lemma empCDF_mono (y : ℝ) (p : ℕ) : Monotone (empCDF y p) := by
  intro s t hst
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [empCDF]
  · have hpR : (0:ℝ) < p := by exact_mod_cast hp
    rw [empCDF, empCDF, div_le_div_iff_of_pos_right hpR]
    exact blockCount_mono (Ioo_subset_Ioo le_rfl hst) p y

/-! ## The ultrafilter limit -/

/-- One fixed ultrafilter refining `atTop`; all limits below are taken along it. -/
noncomputable def orbitUF : Ultrafilter ℕ := Ultrafilter.of atTop

lemma orbitUF_le_atTop : (orbitUF : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop

/-- The limit CDF along the ultrafilter. -/
noncomputable def limCDF (y t : ℝ) : ℝ := limUnder (orbitUF : Filter ℕ) (fun p => empCDF y p t)

lemma tendsto_empCDF_limCDF (y t : ℝ) :
    Tendsto (fun p => empCDF y p t) (orbitUF : Filter ℕ) (nhds (limCDF y t)) := by
  obtain ⟨a, _, ha⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).ultrafilter_le_nhds
    (orbitUF.map (fun p => empCDF y p t))
    (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact Filter.Eventually.of_forall fun p => empCDF_mem_Icc y p t)
  have h : Tendsto (fun p => empCDF y p t) (orbitUF : Filter ℕ) (nhds a) := ha
  rw [limCDF, h.limUnder_eq]
  exact h

lemma limCDF_mem_Icc (y t : ℝ) : limCDF y t ∈ Icc (0:ℝ) 1 :=
  ⟨ge_of_tendsto' (tendsto_empCDF_limCDF y t) (fun p => (empCDF_mem_Icc y p t).1),
    le_of_tendsto' (tendsto_empCDF_limCDF y t) (fun p => (empCDF_mem_Icc y p t).2)⟩

/-! ## The limit CDF is Lipschitz -/

/-- A difference of two initial-segment counts is a count over the gap interval, whenever the gap
interval really absorbs the difference set. -/
lemma empCDF_sub_le {a b a' : ℝ} (y : ℝ) (p : ℕ) (hab : a ≤ b)
    (hsub : ∀ x : ℝ, x ∈ Ioo (0:ℝ) b → x ∉ Ioo (0:ℝ) a → x ∈ Ioo a' b) :
    empCDF y p b - empCDF y p a ≤ blockCount (Ioo a' b) p y / p := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [empCDF]
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  rw [empCDF, empCDF, div_sub_div_same, div_le_div_iff_of_pos_right hpR,
    blockCount_apply, blockCount_apply, blockCount_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  set x := gaussMap^[k] y
  rw [blockIndic, blockIndic, blockIndic]
  by_cases hb : x ∈ Ioo (0:ℝ) b
  · by_cases ha : x ∈ Ioo (0:ℝ) a
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem ha]
      have : (1:ℝ → ℝ) x - (1:ℝ → ℝ) x = 0 := by simp
      rw [this]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    · rw [Set.indicator_of_mem hb, Set.indicator_of_notMem ha,
        Set.indicator_of_mem (hsub x hb ha)]
      simp
  · have ha : x ∉ Ioo (0:ℝ) a := fun hx => hb ⟨hx.1, lt_of_lt_of_le hx.2 hab⟩
    rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem ha, sub_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

@[simp] lemma empCDF_zero (y : ℝ) (p : ℕ) : empCDF y p 0 = 0 := by
  simp [empCDF, blockCount_apply, blockIndic]

@[simp] lemma limCDF_zero (y : ℝ) : limCDF y 0 = 0 :=
  tendsto_nhds_unique (tendsto_empCDF_limCDF y 0) (by simpa using tendsto_const_nhds)

/-- **The limit CDF is `C`-Lipschitz on `[0,1]`**, directly from the absolute-continuity
hypothesis.  This is what replaces Prokhorov + portmanteau: the limit object is continuous by
construction, so no continuity-point caveats arise later. -/
theorem limCDF_sub_le {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    limCDF y b - limCDF y a ≤ C * (b - a) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a gap interval `(a', b)` with `a' ≤ a`, short enough that `C·(a − a')` is negligible
  obtain ⟨a', ha'0, ha'a, hgap, hsub⟩ :
      ∃ a' : ℝ, 0 ≤ a' ∧ a' ≤ a ∧ C * (a - a') ≤ ε / 2 ∧
        ∀ x : ℝ, x ∈ Ioo (0:ℝ) b → x ∉ Ioo (0:ℝ) a → x ∈ Ioo a' b := by
    rcases eq_or_lt_of_le ha with h0 | h0
    · refine ⟨0, le_rfl, ha, by rw [← h0]; simp; positivity, ?_⟩
      intro x hxb hxa
      exact ⟨hxb.1, hxb.2⟩
    · set δ : ℝ := min a (ε / (2 * (C + 1))) with hδ
      have hδ0 : 0 < δ := lt_min h0 (by positivity)
      have hδa : δ ≤ a := min_le_left _ _
      refine ⟨a - δ, by linarith, by linarith, ?_, ?_⟩
      · have : δ ≤ ε / (2 * (C + 1)) := min_le_right _ _
        have hC1 : (0:ℝ) < C + 1 := by linarith
        have : C * δ ≤ (C + 1) * (ε / (2 * (C + 1))) := by
          apply mul_le_mul (by linarith) this hδ0.le (by linarith)
        calc C * (a - (a - δ)) = C * δ := by ring
          _ ≤ (C + 1) * (ε / (2 * (C + 1))) := this
          _ = ε / 2 := by field_simp
      · intro x hxb hxa
        refine ⟨?_, hxb.2⟩
        have : a ≤ x := by
          by_contra hcon
          exact hxa ⟨hxb.1, lt_of_not_ge hcon⟩
        linarith
  have hev : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ),
      empCDF y p b - empCDF y p a ≤ C * (b - a') + ε / 2 := by
    have h0 : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ),
        blockCount (Ioo a' b) p y / p ≤ C * (b - a') + ε / 2 :=
      orbitUF_le_atTop (hAC a' b ha'0 (ha'a.trans hab) hb (ε/2) (by linarith))
    filter_upwards [h0] with p hp
    exact (empCDF_sub_le y p hab hsub).trans hp
  have hlim : limCDF y b - limCDF y a ≤ C * (b - a') + ε / 2 :=
    le_of_tendsto ((tendsto_empCDF_limCDF y b).sub (tendsto_empCDF_limCDF y a)) hev
  have : C * (b - a') = C * (b - a) + C * (a - a') := by ring
  linarith

lemma empCDF_one {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {p : ℕ} (hp : 0 < p) :
    empCDF y p 1 = 1 := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  rw [empCDF, blockCount_apply]
  have : ∀ k ∈ Finset.range p, blockIndic (Ioo (0:ℝ) 1) (gaussMap^[k] y) = 1 := by
    intro k _
    rw [blockIndic, Set.indicator_of_mem (horb k)]
    rfl
  rw [Finset.sum_congr rfl this]
  simp [hpR.ne']

/-- The limit CDF is a genuine probability CDF on `[0,1]`: no mass escapes. -/
lemma limCDF_one {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) : limCDF y 1 = 1 := by
  refine tendsto_nhds_unique (tendsto_empCDF_limCDF y 1) ?_
  have h0 : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ), 0 < p :=
    orbitUF_le_atTop (eventually_gt_atTop 0)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h0] with p hp
  exact (empCDF_one horb hp).symm

lemma limCDF_mono (y : ℝ) : Monotone (limCDF y) := by
  intro s t hst
  exact le_of_tendsto_of_tendsto (tendsto_empCDF_limCDF y s) (tendsto_empCDF_limCDF y t)
    (Eventually.of_forall fun p => empCDF_mono y p hst)

/-! ## The limit CDF, globally -/

lemma limCDF_of_nonpos (y : ℝ) {t : ℝ} (ht : t ≤ 0) : limCDF y t = 0 := by
  refine tendsto_nhds_unique (tendsto_empCDF_limCDF y t) ?_
  have : ∀ p : ℕ, empCDF y p t = 0 := by
    intro p
    rw [empCDF, blockCount_apply]
    have : ∀ k ∈ Finset.range p, blockIndic (Ioo (0:ℝ) t) (gaussMap^[k] y) = 0 := by
      intro k _
      rw [blockIndic, Set.indicator_of_notMem]
      intro hx
      exact absurd (hx.1.trans hx.2) (by linarith)
    rw [Finset.sum_congr rfl this]
    simp
  simpa [this] using tendsto_const_nhds (α := ℝ) (f := (orbitUF : Filter ℕ)) (a := (0:ℝ))

lemma limCDF_of_one_le {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {t : ℝ}
    (ht : 1 ≤ t) : limCDF y t = 1 := by
  refine le_antisymm (limCDF_mem_Icc y t).2 ?_
  rw [← limCDF_one horb]
  exact limCDF_mono y ht

/-- The clamp of `t` to `[0,1]` does not change the limit CDF. -/
lemma limCDF_clamp {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) (t : ℝ) :
    limCDF y t = limCDF y (max 0 (min t 1)) := by
  rcases le_or_gt t 0 with h | h
  · rw [limCDF_of_nonpos y h, min_eq_left (by linarith), max_eq_left h, limCDF_of_nonpos y le_rfl]
  · rcases le_or_gt t 1 with h1 | h1
    · rw [min_eq_left h1, max_eq_right h.le]
    · rw [min_eq_right h1.le, max_eq_right zero_le_one, limCDF_of_one_le horb h1.le,
        limCDF_of_one_le horb le_rfl]

/-- **Global Lipschitz bound.** -/
theorem limCDF_sub_le' {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {a b : ℝ} (hab : a ≤ b) :
    limCDF y b - limCDF y a ≤ C * (b - a) := by
  set a' := max 0 (min a 1) with ha'
  set b' := max 0 (min b 1) with hb'
  have ha'0 : 0 ≤ a' := le_max_left _ _
  have hb'1 : b' ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hab' : a' ≤ b' := by
    apply max_le_max le_rfl
    exact min_le_min hab le_rfl
  have hdiff : b' - a' ≤ b - a := by
    rcases le_or_gt a 0 with h | h
    · have : a' = 0 := by rw [ha', min_eq_left (by linarith), max_eq_left h]
      rw [this]
      rcases le_or_gt b 1 with h1 | h1
      · rcases le_or_gt b 0 with h0 | h0
        · have : b' = 0 := by rw [hb', min_eq_left (by linarith), max_eq_left h0]
          rw [this]; linarith
        · have : b' = b := by rw [hb', min_eq_left h1, max_eq_right h0.le]
          rw [this]; linarith
      · have : b' = 1 := by rw [hb', min_eq_right h1.le, max_eq_right zero_le_one]
        rw [this]; linarith
    · rcases le_or_gt a 1 with h1 | h1
      · have haa : a' = a := by rw [ha', min_eq_left h1, max_eq_right h.le]
        rw [haa]
        rcases le_or_gt b 1 with hb1 | hb1
        · have : b' = b := by rw [hb', min_eq_left hb1, max_eq_right (by linarith : (0:ℝ) ≤ b)]
          rw [this]
        · have : b' = 1 := by rw [hb', min_eq_right hb1.le, max_eq_right zero_le_one]
          rw [this]; linarith
      · have haa : a' = 1 := by rw [ha', min_eq_right h1.le, max_eq_right zero_le_one]
        have hbb : b' = 1 := by
          rw [hb', min_eq_right (by linarith : (1:ℝ) ≤ b), max_eq_right zero_le_one]
        rw [haa, hbb]; linarith
  calc limCDF y b - limCDF y a = limCDF y b' - limCDF y a' := by
        rw [← limCDF_clamp horb, ← limCDF_clamp horb]
    _ ≤ C * (b' - a') := limCDF_sub_le hC hAC ha'0 hab' hb'1
    _ ≤ C * (b - a) := by nlinarith

lemma limCDF_lipschitz {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) :
    LipschitzWith (Real.toNNReal C) (limCDF y) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [Real.coe_toNNReal C hC, Real.dist_eq, Real.dist_eq, abs_sub_le_iff]
  constructor
  · rcases le_or_gt s t with h | h
    · have := limCDF_mono y h
      have h2 := limCDF_sub_le' hC hAC horb h
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    · have h2 := limCDF_sub_le' hC hAC horb h.le
      rw [abs_of_nonneg (by linarith)]
      nlinarith
  · rcases le_or_gt s t with h | h
    · have h2 := limCDF_sub_le' hC hAC horb h
      have := limCDF_mono y h
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    · have h2 := limCDF_sub_le' hC hAC horb h.le
      have := limCDF_mono y h.le
      rw [abs_of_nonneg (by linarith)]
      nlinarith

/-! ## The limit measure -/

/-- Comparison of Stieltjes measures: it is enough to compare the increments, because both outer
measures are infima over the *same* covers by `Ioc`s. -/
lemma stieltjes_measure_le {f g : StieltjesFunction ℝ}
    (h : ∀ a b : ℝ, ENNReal.ofReal (f b - f a) ≤ ENNReal.ofReal (g b - g a)) :
    f.measure ≤ g.measure := by
  have hlen : ∀ s : Set ℝ, f.length s ≤ g.length s := by
    intro s
    rw [StieltjesFunction.length_eq, StieltjesFunction.length_eq]
    exact iInf_mono fun a => iInf_mono fun b => iInf_mono fun _ => h a b
  have houter : f.outer ≤ g.outer :=
    MeasureTheory.OuterMeasure.le_ofFunction.2
      fun s => (MeasureTheory.OuterMeasure.ofFunction_le s).trans (hlen s)
  intro s
  rw [StieltjesFunction.measure, StieltjesFunction.measure]
  exact houter s

/-- The linear Stieltjes function `t ↦ C·t`, whose measure is `C·volume`. -/
noncomputable def linStieltjes {C : ℝ} (hC : 0 ≤ C) : StieltjesFunction ℝ where
  toFun := fun t => C * t
  mono' := fun s t hst => by dsimp; nlinarith
  right_continuous' := fun x =>
    (continuous_const.mul continuous_id).continuousAt.continuousWithinAt

@[simp] lemma linStieltjes_apply {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : linStieltjes hC t = C * t := rfl

lemma linStieltjes_measure {C : ℝ} (hC : 0 ≤ C) :
    (linStieltjes hC).measure = ENNReal.ofReal C • volume := by
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  rw [StieltjesFunction.measure_Ioc, Measure.smul_apply, smul_eq_mul, Real.volume_Ioc,
    ← ENNReal.ofReal_mul hC]
  simp only [linStieltjes_apply]
  ring_nf

/-- The limit CDF as a `StieltjesFunction`: Lipschitz, hence continuous, hence right-continuous. -/
noncomputable def limStieltjes {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) : StieltjesFunction ℝ where
  toFun := limCDF y
  mono' := limCDF_mono y
  right_continuous' := fun x =>
    ((limCDF_lipschitz hC hAC horb).continuous.continuousAt).continuousWithinAt

@[simp] lemma limStieltjes_apply {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) (t : ℝ) :
    limStieltjes hC hAC horb t = limCDF y t := rfl

/-- **The limit measure of the orbit**: the Stieltjes measure of the limit CDF. -/
noncomputable def limMeasure {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) : Measure ℝ :=
  (limStieltjes hC hAC horb).measure

lemma limMeasure_Ioc {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) (a b : ℝ) :
    limMeasure hC hAC horb (Ioc a b) = ENNReal.ofReal (limCDF y b - limCDF y a) :=
  (limStieltjes hC hAC horb).measure_Ioc a b

/-- The limit measure is a probability measure: no mass escapes to the ends. -/
lemma limMeasure_univ {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) :
    limMeasure hC hAC horb Set.univ = 1 := by
  have hbot : Tendsto (limStieltjes hC hAC horb) atBot (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_le_atBot (0:ℝ)] with t ht
    exact (limCDF_of_nonpos y ht).symm
  have htop : Tendsto (limStieltjes hC hAC horb) atTop (nhds 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    exact (limCDF_of_one_le horb ht).symm
  rw [limMeasure, StieltjesFunction.measure_univ _ hbot htop]
  simp

/-- **The limit measure is absolutely continuous**, with density at most `C` — the payoff of the
Lipschitz bound. -/
lemma limMeasure_le {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) :
    limMeasure hC hAC horb ≤ ENNReal.ofReal C • volume := by
  rw [limMeasure, ← linStieltjes_measure hC]
  refine stieltjes_measure_le fun a b => ?_
  rcases le_or_gt a b with hab | hab
  · refine ENNReal.ofReal_le_ofReal ?_
    have h := limCDF_sub_le' hC hAC horb hab
    simp only [linStieltjes_apply, limStieltjes_apply]
    nlinarith
  · have : limCDF y b - limCDF y a ≤ 0 := by
      have := limCDF_mono y hab.le
      linarith
    simpa [ENNReal.ofReal_eq_zero.2 this] using zero_le _

/-! ## Towards invariance: elementary count identities -/

/-- The count over a half-open interval is the difference of two initial-segment counts, exactly,
as long as the orbit stays in `(0,1)`. -/
lemma blockCount_Ico {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (p : ℕ) :
    blockCount (Ico c d) p y = blockCount (Ioo 0 d) p y - blockCount (Ioo 0 c) p y := by
  rw [blockCount_apply, blockCount_apply, blockCount_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx := horb k
  set x := gaussMap^[k] y
  rw [blockIndic, blockIndic, blockIndic]
  by_cases h1 : x ∈ Ico c d
  · rw [Set.indicator_of_mem h1,
      Set.indicator_of_mem (show x ∈ Ioo (0:ℝ) d from ⟨hx.1, h1.2⟩),
      Set.indicator_of_notMem (fun h => absurd h1.1 (not_le.2 h.2))]
    simp
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : x ∈ Ioo (0:ℝ) d
    · have h3 : x ∈ Ioo (0:ℝ) c := by
        refine ⟨hx.1, ?_⟩
        by_contra hcon
        exact h1 ⟨not_lt.1 hcon, h2.2⟩
      rw [Set.indicator_of_mem h2, Set.indicator_of_mem h3]
      simp
    · have h3 : x ∉ Ioo (0:ℝ) c := fun h => h2 ⟨h.1, lt_of_lt_of_le h.2 hcd⟩
      rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
      simp

/-- **Approximate invariance of the empirical measure**, exactly: shifting the window by one costs
only the two boundary terms. -/
lemma blockCount_preimage (S : Set ℝ) (p : ℕ) (y : ℝ) :
    blockCount (gaussMap ⁻¹' S) p y
      = blockCount S p y - blockIndic S y + blockIndic S (gaussMap^[p] y) := by
  induction p with
  | zero => simp [blockCount_apply]
  | succ n ih =>
      rw [blockCount_apply, Finset.sum_range_succ, ← blockCount_apply, ih]
      rw [blockCount_apply (A := S) (n := n + 1), Finset.sum_range_succ, ← blockCount_apply]
      have h1 : blockIndic (gaussMap ⁻¹' S) (gaussMap^[n] y)
          = blockIndic S (gaussMap^[n + 1] y) := by
        rw [blockIndic, blockIndic, Function.iterate_succ_apply']
        rfl
      rw [h1]
      ring

/-- A single point has vanishing empirical density along the ultrafilter — the AC hypothesis
forbids the orbit from concentrating anywhere.  This is what lets `Ioo`, `Ico` and `Ioc` be used
interchangeably in every limit below. -/
lemma tendsto_blockCount_singleton {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) (c : ℝ) :
    Tendsto (fun p : ℕ => blockCount {c} p y / p) (orbitUF : Filter ℕ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_cases hc : c ∈ Ioo (0:ℝ) 1
  · obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * C * δ + ε / 2 < ε := by
      refine ⟨min (1/2) (ε / (4 * (C + 1))), lt_min (by norm_num) (by positivity), ?_⟩
      set δ := min (1/2 : ℝ) (ε / (4 * (C + 1))) with hδdef
      have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
      have hd1 : δ ≤ ε / (4 * (C + 1)) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at hd1
      nlinarith
    set a := max 0 (c - δ) with ha
    set b := min 1 (c + δ) with hb
    have ha0 : 0 ≤ a := le_max_left _ _
    have hb1 : b ≤ 1 := min_le_left _ _
    have hac : a < c := max_lt hc.1 (by linarith)
    have hcb : c < b := lt_min hc.2 (by linarith)
    have hab : a ≤ b := le_of_lt (hac.trans hcb)
    have hba : b - a ≤ 2 * δ := by
      have h1 : a ≥ c - δ := le_max_right _ _
      have h2 : b ≤ c + δ := min_le_right _ _
      linarith
    have h0 : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ),
        blockCount (Ioo a b) p y / p ≤ C * (b - a) + ε / 2 :=
      orbitUF_le_atTop (hAC a b ha0 hab hb1 (ε/2) (by linarith))
    filter_upwards [h0] with p hp
    have hmono : blockCount {c} p y ≤ blockCount (Ioo a b) p y :=
      blockCount_mono (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨hac, hcb⟩) p y
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0; simpa using hε
    have hpR : (0:ℝ) < p := by exact_mod_cast hp0
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (blockCount_nonneg _ _ _) hpR.le)]
    calc blockCount {c} p y / p ≤ blockCount (Ioo a b) p y / p := by gcongr
      _ ≤ C * (b - a) + ε / 2 := hp
      _ ≤ 2 * C * δ + ε / 2 := by nlinarith
      _ < ε := hδ
  · have : ∀ p : ℕ, blockCount {c} p y / p = 0 := by
      intro p
      have : blockCount {c} p y = 0 := by
        rw [blockCount_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [blockIndic, Set.indicator_of_notMem]
        intro h
        rw [Set.mem_singleton_iff] at h
        exact hc (h ▸ horb k)
      rw [this, zero_div]
    simpa [this] using hε

/-! ## The explicit preimage of an interval -/

/-- **The branch decomposition.**  For an irrational `x ∈ (0,1)`, `Tx ∈ (a,b]` happens exactly on
the `k`-th branch interval `[1/(k+b), 1/(k+a))`, where `k` is the first CF digit of `x`.
Irrationality removes the one boundary case (`x = 1/(k+1)`, where `Tx = 0`). -/
lemma mem_branch_iff {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {x : ℝ} (hirr : Irrational x) (hx : x ∈ Ioo (0:ℝ) 1) {k : ℕ} (hk : 1 ≤ k) :
    x ∈ Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a)) ↔ (cfDigit x 0 = k ∧ gaussMap x ∈ Ioc a b) := by
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hka : (0:ℝ) < (k:ℝ) + a := by linarith
  have hkb : (0:ℝ) < (k:ℝ) + b := by linarith
  have hx0 : (0:ℝ) < x := hx.1
  have hginv : gaussMap x = x⁻¹ - (cfDigit x 0 : ℝ) := gaussMap_eq_inv_sub hx
  constructor
  · rintro ⟨h1, h2⟩
    have hinv1 : x⁻¹ ≤ (k:ℝ) + b := by
      rw [one_div] at h1
      exact (inv_le_comm₀ hx0 hkb).2 h1
    have hinv2 : (k:ℝ) + a < x⁻¹ := by
      rw [one_div] at h2
      exact (lt_inv_comm₀ hx0 hka).1 h2
    have hlt : x⁻¹ < (k:ℝ) + 1 := by
      rcases lt_or_eq_of_le (hinv1.trans (by linarith : (k:ℝ) + b ≤ (k:ℝ) + 1)) with h | h
      · exact h
      · exact absurd (h ▸ hirr.inv) (by
          simpa using (Rat.not_irrational ((k : ℚ) + 1)) ∘ (by
            intro hh
            convert hh using 2
            push_cast
            ring))
    have hfl : cfDigit x 0 = k := by
      rw [cfDigit_zero, Nat.floor_eq_iff (by positivity)]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    refine ⟨hfl, ?_⟩
    rw [hginv, hfl]
    constructor
    · linarith
    · linarith
  · rintro ⟨hfl, h1, h2⟩
    rw [hginv, hfl] at h1 h2
    have hinv2 : (k:ℝ) + a < x⁻¹ := by linarith
    have hinv1 : x⁻¹ ≤ (k:ℝ) + b := by linarith
    constructor
    · rw [one_div]
      exact (inv_le_comm₀ hkb hx0).2 hinv1
    · rw [one_div]
      exact (lt_inv_comm₀ hx0 hka).2 hinv2

/-- The branch intervals are disjoint (each determines the first digit), so at most one indicator
fires; and when one does, the point really is in the preimage. -/
lemma sum_blockIndic_branch_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {x : ℝ} (hirr : Irrational x) (hx : x ∈ Ioo (0:ℝ) 1) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x
      ≤ blockIndic (gaussMap ⁻¹' (Ioc a b)) x := by
  by_cases h : ∃ k ∈ Finset.Icc 1 K, x ∈ Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))
  · obtain ⟨k₀, hk₀mem, hk₀⟩ := h
    have hk₀1 : 1 ≤ k₀ := (Finset.mem_Icc.1 hk₀mem).1
    obtain ⟨hdig, hgauss⟩ := (mem_branch_iff ha hab hb hirr hx hk₀1).1 hk₀
    rw [Finset.sum_eq_single k₀ ?_ ?_]
    · rw [blockIndic, Set.indicator_of_mem hk₀, blockIndic,
        Set.indicator_of_mem (show x ∈ gaussMap ⁻¹' (Ioc a b) from hgauss)]
    · intro k hkmem hkne
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hkmem).1
      rw [blockIndic, Set.indicator_of_notMem]
      intro hxk
      exact hkne (((mem_branch_iff ha hab hb hirr hx hk1).1 hxk).1.symm.trans hdig)
    · intro hnot
      exact absurd hk₀mem hnot
  · push_neg at h
    have : ∑ k ∈ Finset.Icc 1 K, blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [blockIndic, Set.indicator_of_notMem (h k hk)]
    rw [this]
    exact blockIndic_nonneg _ _

/-- Conversely, a point of the preimage is on one of the first `K` branches, or else it is tiny —
and the tail `(0, 1/(K+a))` is what the AC bound makes uniformly negligible. -/
lemma blockIndic_preimage_le_sum {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {x : ℝ} (hirr : Irrational x) (hx : x ∈ Ioo (0:ℝ) 1) {K : ℕ} (hK : 1 ≤ K) :
    blockIndic (gaussMap ⁻¹' (Ioc a b)) x
      ≤ (∑ k ∈ Finset.Icc 1 K, blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x)
        + blockIndic (Ioo 0 (1/((K:ℝ)+a))) x := by
  by_cases hmem : x ∈ gaussMap ⁻¹' (Ioc a b)
  · set m := cfDigit x 0 with hm
    have hm1 : 1 ≤ m := one_le_cfDigit x hirr hx 0
    have hxm : x ∈ Ico (1/((m:ℝ)+b)) (1/((m:ℝ)+a)) :=
      (mem_branch_iff ha hab hb hirr hx hm1).2 ⟨rfl, hmem⟩
    rw [blockIndic, Set.indicator_of_mem hmem]
    by_cases hmK : m ≤ K
    · have hmem' : m ∈ Finset.Icc 1 K := Finset.mem_Icc.2 ⟨hm1, hmK⟩
      have h1 : blockIndic (Ico (1/((m:ℝ)+b)) (1/((m:ℝ)+a))) x
          ≤ ∑ k ∈ Finset.Icc 1 K, blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x :=
        Finset.single_le_sum (a := m)
          (f := fun k : ℕ => blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x)
          (fun k _ => blockIndic_nonneg _ _) hmem'
      rw [blockIndic, Set.indicator_of_mem hxm] at h1
      have h2 := blockIndic_nonneg (Ioo (0:ℝ) (1/((K:ℝ)+a))) x
      simp only [Pi.one_apply] at h1 ⊢
      linarith
    · push_neg at hmK
      have hmR : (K:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmK
      have hKa : (0:ℝ) < (K:ℝ) + a := by
        have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
        linarith
      have hxlt : x < 1/((K:ℝ)+a) := by
        refine hxm.2.trans_le ?_
        apply one_div_le_one_div_of_le hKa
        linarith
      have h1 : blockIndic (Ioo (0:ℝ) (1/((K:ℝ)+a))) x = 1 := by
        rw [blockIndic, Set.indicator_of_mem
          (show x ∈ Ioo (0:ℝ) (1/((K:ℝ)+a)) from ⟨hx.1, hxlt⟩)]
        rfl
      have h2 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 K,
          blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x :=
        Finset.sum_nonneg fun k _ => blockIndic_nonneg _ _
      rw [h1]
      simp only [Pi.one_apply]
      linarith
  · rw [blockIndic, Set.indicator_of_notMem hmem]
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 K,
        blockIndic (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) x :=
      Finset.sum_nonneg fun k _ => blockIndic_nonneg _ _
    have h2 := blockIndic_nonneg (Ioo (0:ℝ) (1/((K:ℝ)+a))) x
    linarith

/-! ## Summing the branch inequalities over the orbit -/

lemma blockCount_union_le (A B : Set ℝ) (p : ℕ) (y : ℝ) :
    blockCount (A ∪ B) p y ≤ blockCount A p y + blockCount B p y := by
  rw [blockCount_apply, blockCount_apply, blockCount_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  set x := gaussMap^[k] y
  rw [blockIndic, blockIndic, blockIndic]
  by_cases hA : x ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (Set.mem_union_left B hA)]
    have := Set.indicator_nonneg (f := (1 : ℝ → ℝ)) (s := B)
      (fun (_ : ℝ) _ => zero_le_one) x
    simp only [Pi.one_apply] at *
    linarith
  · by_cases hB : x ∈ B
    · rw [Set.indicator_of_mem hB, Set.indicator_of_mem (Set.mem_union_right A hB),
        Set.indicator_of_notMem hA]
      simp
    · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB,
        Set.indicator_of_notMem (by simpa using ⟨hA, hB⟩ : x ∉ A ∪ B)]
      simp

/-- The empirical count of a half-open interval converges to the CDF increment. -/
lemma tendsto_blockCount_Ico {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    Tendsto (fun p : ℕ => blockCount (Ico c d) p y / p) (orbitUF : Filter ℕ)
      (nhds (limCDF y d - limCDF y c)) := by
  have h : ∀ p : ℕ, blockCount (Ico c d) p y / p = empCDF y p d - empCDF y p c := by
    intro p
    rw [blockCount_Ico horb hc hcd p, empCDF, empCDF, sub_div]
  simp only [h]
  exact (tendsto_empCDF_limCDF y d).sub (tendsto_empCDF_limCDF y c)

/-- The same for the open-closed interval: the two differ only by endpoints, which the AC bound
makes negligible. -/
lemma tendsto_blockCount_Ioc {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    Tendsto (fun p : ℕ => blockCount (Ioc c d) p y / p) (orbitUF : Filter ℕ)
      (nhds (limCDF y d - limCDF y c)) := by
  have hbase := tendsto_blockCount_Ico horb hc hcd
  have hsa := tendsto_blockCount_singleton hC hAC horb c
  have hsb := tendsto_blockCount_singleton hC hAC horb d
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun p : ℕ => blockCount (Ico c d) p y / p - blockCount {c} p y / p)
    (h := fun p : ℕ => blockCount (Ico c d) p y / p + blockCount {d} p y / p)
    (by simpa using hbase.sub hsa) (by simpa using hbase.add hsb) ?_ ?_
  · intro p
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    have hpR : (0:ℝ) < p := by exact_mod_cast hp
    show blockCount (Ico c d) p y / p - blockCount {c} p y / p
        ≤ blockCount (Ioc c d) p y / p
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hpR]
    have : blockCount (Ico c d) p y ≤ blockCount (Ioc c d) p y + blockCount {c} p y := by
      refine le_trans (blockCount_mono (B := Ioc c d ∪ {c}) ?_ p y) (blockCount_union_le _ _ p y)
      intro z hz
      rcases eq_or_lt_of_le hz.1 with h | h
      · exact Set.mem_union_right _ (by simp [h])
      · exact Set.mem_union_left _ ⟨h, hz.2.le⟩
    linarith
  · intro p
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    have hpR : (0:ℝ) < p := by exact_mod_cast hp
    show blockCount (Ioc c d) p y / p
        ≤ blockCount (Ico c d) p y / p + blockCount {d} p y / p
    rw [← add_div, div_le_div_iff_of_pos_right hpR]
    refine le_trans (blockCount_mono (B := Ico c d ∪ {d}) ?_ p y) (blockCount_union_le _ _ p y)
    intro z hz
    rcases eq_or_lt_of_le hz.2 with h | h
    · exact Set.mem_union_right _ (by simp [h])
    · exact Set.mem_union_left _ ⟨hz.1.le, h⟩

/-! ## The two-sided bound, and invariance at the level of the CDF -/

lemma sum_blockCount_branch_le {y a b : ℝ} (hirr : Irrational y) (hy : y ∈ Ioo (0:ℝ) 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (K p : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, blockCount (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) p y
      ≤ blockCount (gaussMap ⁻¹' (Ioc a b)) p y := by
  simp only [blockCount_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨hj1, hj2⟩ := irrational_orbit y hirr hy j
  exact sum_blockIndic_branch_le ha hab hb hj1 hj2 K

lemma blockCount_preimage_le_sum {y a b : ℝ} (hirr : Irrational y) (hy : y ∈ Ioo (0:ℝ) 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {K : ℕ} (hK : 1 ≤ K) (p : ℕ) :
    blockCount (gaussMap ⁻¹' (Ioc a b)) p y
      ≤ (∑ k ∈ Finset.Icc 1 K, blockCount (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) p y)
        + blockCount (Ioo 0 (1/((K:ℝ)+a))) p y := by
  simp only [blockCount_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨hj1, hj2⟩ := irrational_orbit y hirr hy j
  exact blockIndic_preimage_le_sum ha hab hb hj1 hj2 hK

/-- The limit of the finite branch sums. -/
lemma tendsto_sum_blockCount_branch {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (K : ℕ) :
    Tendsto (fun p : ℕ =>
        ∑ k ∈ Finset.Icc 1 K, blockCount (Ico (1/((k:ℝ)+b)) (1/((k:ℝ)+a))) p y / p)
      (orbitUF : Filter ℕ)
      (nhds (∑ k ∈ Finset.Icc 1 K, (limCDF y (1/((k:ℝ)+a)) - limCDF y (1/((k:ℝ)+b))))) := by
  refine tendsto_finset_sum _ fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hkb : (0:ℝ) < (k:ℝ) + b := by linarith
  refine tendsto_blockCount_Ico horb (le_of_lt (div_pos zero_lt_one hkb)) ?_
  apply one_div_le_one_div_of_le (by linarith)
  linarith

/-- The empirical count of the preimage converges to the CDF increment: the window shift costs
only the two boundary terms. -/
lemma tendsto_blockCount_preimage {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C)
    (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    Tendsto (fun p : ℕ => blockCount (gaussMap ⁻¹' (Ioc a b)) p y / p) (orbitUF : Filter ℕ)
      (nhds (limCDF y b - limCDF y a)) := by
  have hbase := tendsto_blockCount_Ioc hC hAC horb ha hab
  have hone : Tendsto (fun p : ℕ => (1:ℝ) / p) (orbitUF : Filter ℕ) (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.mono_left orbitUF_le_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun p : ℕ => blockCount (Ioc a b) p y / p - 1 / p)
    (h := fun p : ℕ => blockCount (Ioc a b) p y / p + 1 / p)
    (by simpa using hbase.sub hone) (by simpa using hbase.add hone) ?_ ?_
  · intro p
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    have hpR : (0:ℝ) < p := by exact_mod_cast hp
    show blockCount (Ioc a b) p y / p - 1 / p ≤ blockCount (gaussMap ⁻¹' (Ioc a b)) p y / p
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hpR, blockCount_preimage]
    have h1 := blockIndic_le_one (Ioc a b) y
    have h2 := blockIndic_nonneg (Ioc a b) (gaussMap^[p] y)
    linarith
  · intro p
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp [blockCount_apply]
    have hpR : (0:ℝ) < p := by exact_mod_cast hp
    show blockCount (gaussMap ⁻¹' (Ioc a b)) p y / p ≤ blockCount (Ioc a b) p y / p + 1 / p
    rw [← add_div, div_le_div_iff_of_pos_right hpR, blockCount_preimage]
    have h1 := blockIndic_le_one (Ioc a b) (gaussMap^[p] y)
    have h2 := blockIndic_nonneg (Ioc a b) y
    linarith

section Audit

#print axioms limCDF_sub_le
#print axioms limCDF_one
#print axioms limCDF_mono
#print axioms limCDF_sub_le'
#print axioms limMeasure_univ
#print axioms limMeasure_le

end Audit

end NormalNumbers
