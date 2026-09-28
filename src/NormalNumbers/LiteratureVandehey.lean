/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.CFAeNormal

/-!
# Vandehey 2017, Theorem 1.1: non-trivial matrix actions preserve CF-normality

Discharges the cited `Literature.vandehey_matrix_action` (side quest, 2026-09-27).

## The architecture, and how it routes AROUND the published gap

⚠️ **Known gap in the published proof.**  Vandehey's Lemma 3.3 (3.2 in arXiv v1) is the
Pyatetskii-Shapiro hot-spot criterion, proved as "a simple consequence of
[Moshchevitin–Shkredov 2003, Theorem 1]".  Airey–Mance (arXiv:1912.10265) show that
theorem is FALSE on non-compact spaces, and the CF space is non-compact.  The repair:
add a tightness hypothesis (Airey–Mance Theorem A/B) and prove that the empirical
measures of a CF-normal point are tight.  Full write-up:
`papers/vandehey-2017-open-problem-attack-map.md` §6.1; paper notes:
`papers/vandehey-2017-matrix-actions-cf-normality.md`.

**Where that gap sits in our decomposition.**  Vandehey's §6 endgame is an *either-or*
trick: the transducer analysis (§2 transducer, §3 skew product, §4 transitive
components, §5 trigger strings, §6 assembly) never computes the limiting frequency
`ρ_r` of a word `r` in `Mx`; it only shows the limit EXISTS and is the SAME for every
CF-normal `x`.  The identification `ρ_r = γ(I_r)` is then free, by a measure-theoretic
pigeonhole.  So the whole theorem factors as

* `VandeheyUniformFreq` — the crux (§2–§6): *the frequency of every genuine word in
  `Mx` converges to a limit independent of the CF-normal `x`*.  This is where the
  hot-spot criterion is used (§3, Theorem 3.1), so this is where we owe the
  **tightness-corrected** criterion plus tightness of a CF-normal point's empirical
  measures.  `sorry` here, disclosed; attacked lap by lap.
* `vandehey_matrix_action_of_uniformFreq` — **PROVED here, unconditionally.**  Given the
  crux, Theorem 1.1 follows.  The broken lemma plays no role in this half: identifying
  `ρ_r` needs only that a.e. real is CF-normal (`ae_isCFNormal`) and that a nonsingular
  integer Möbius map is Lebesgue-nonsingular (`volume_image_mobius_null`), so the
  CF-normal reals and their `M`-preimages must MEET; at a point of the intersection the
  `x`-independent limit is forced to be `γ(I_v)`.

Net effect: the corrected hot-spot criterion is needed only for the *existence* half,
never for the *identification* half, and the version of record's defective step is
nowhere reproduced.

**And the existence half no longer wants it either.**  `VandeheyAutomaton.lean` builds a
different engine for §3: if the transducer has a *synchronizing* genuine word, the state
at time `i` is a function of the last `L` digits alone (pathwise merging,
`stateAt_eq_of_window_sync`), so the joint (window, state) frequency is a finite sum of
plain cylinder frequencies plus a residue of frequency `γ(z-free length-L words) → 0`.
That needs only CF-normality of `x` and the repo's mixing stack — no hot-spot criterion,
no tightness, no ergodicity, no Ryll-Nardzewski/Vitali-Hahn-Saks.  The remaining debt on
that route is the existence of a synchronizing word for Vandehey's `M_D` transducer
(his §2 + §4 material).

Available machinery: `Literature.philipp_psi_mixing_holds` (ψ-mixing, `CFPsiPin.lean`),
Rényi-type bounds, the CF cylinder / digit-law stack, `HotSpot.lean` (base-`b` only),
`CFAeNormal.ae_isCFNormal`.
-/

namespace NormalNumbers.Literature

open NormalNumbers MeasureTheory Filter

/-! ## Step 0: nonsingular integer Möbius maps are Lebesgue-nonsingular -/

/-- A real Möbius map, in the coordinates used by `vandehey_matrix_action`. -/
noncomputable def mobius (p q r s : ℝ) (y : ℝ) : ℝ := (p * y + q) / (r * y + s)

/-- The zero set of a nontrivial real affine function is a subsingleton. -/
lemma subsingleton_affine_zero {r s : ℝ} (h : r ≠ 0 ∨ s ≠ 0) :
    {y : ℝ | r * y + s = 0}.Subsingleton := by
  intro y₁ h₁ y₂ h₂
  simp only [Set.mem_setOf_eq] at h₁ h₂
  rcases eq_or_ne r 0 with hr | hr
  · rcases h with h | h
    · exact absurd hr h
    · rw [hr] at h₁; simp at h₁; exact absurd h₁ h
  · have : r * y₁ = r * y₂ := by linarith
    exact mul_left_cancel₀ hr this

lemma measurableSet_affine_zero (r s : ℝ) : MeasurableSet {y : ℝ | r * y + s = 0} := by
  have hc : Continuous fun y : ℝ => r * y + s := by fun_prop
  exact hc.measurable (measurableSet_singleton (0 : ℝ))

/-- **Lebesgue-nonsingularity of a nonsingular Möbius map**: it maps null sets to null
sets.  (Change of variables through the one-dimensional Jacobian; the pole contributes
at most one point.)  This is the only measure-theoretic input the endgame needs beyond
`ae_isCFNormal`. -/
lemma volume_image_mobius_null (p q r s : ℝ) (hdet : p * s - q * r ≠ 0)
    {Z : Set ℝ} (hZmeas : MeasurableSet Z) (hZ : volume Z = 0) :
    volume (mobius p q r s '' Z) = 0 := by
  set P : Set ℝ := {y : ℝ | r * y + s = 0} with hP
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hdet (by rw [hcon.1, hcon.2]; ring)
  have hPmeas : MeasurableSet P := measurableSet_affine_zero r s
  set A : Set ℝ := Z \ P with hA
  have hAmeas : MeasurableSet A := hZmeas.diff hPmeas
  have hA0 : volume A = 0 := measure_mono_null Set.diff_subset hZ
  -- the image of the good part is null by change of variables
  have himA : volume (mobius p q r s '' A) = 0 := by
    have hderiv : ∀ y ∈ A, HasDerivWithinAt (mobius p q r s)
        ((p * s - q * r) / (r * y + s) ^ 2) A y := by
      intro y hy
      have hne : r * y + s ≠ 0 := by
        intro h; exact hy.2 (by simpa [hP] using h)
      have hnum : HasDerivAt (fun z : ℝ => p * z + q) p y := by
        simpa using (hasDerivAt_id y).const_mul p |>.add_const q
      have hden : HasDerivAt (fun z : ℝ => r * z + s) r y := by
        simpa using (hasDerivAt_id y).const_mul r |>.add_const s
      have h := hnum.div hden hne
      have heq : (p * (r * y + s) - (p * y + q) * r) / (r * y + s) ^ 2
          = (p * s - q * r) / (r * y + s) ^ 2 := by ring_nf
      rw [heq] at h
      exact h.hasDerivWithinAt
    have hinj : Set.InjOn (mobius p q r s) A := by
      intro y₁ h₁ y₂ h₂ heq
      have hne₁ : r * y₁ + s ≠ 0 := fun h => h₁.2 (by simpa [hP] using h)
      have hne₂ : r * y₂ + s ≠ 0 := fun h => h₂.2 (by simpa [hP] using h)
      simp only [mobius, div_eq_div_iff hne₁ hne₂] at heq
      have : (p * s - q * r) * (y₁ - y₂) = 0 := by nlinarith [heq]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hdet
      · linarith
    have h := lintegral_image_eq_lintegral_abs_deriv_mul hAmeas hderiv hinj
      (fun _ => (1 : ENNReal))
    rw [setLIntegral_one] at h
    rw [h, setLIntegral_measure_zero _ _ hA0]
  -- the image of the pole part is a subsingleton
  have himP : volume (mobius p q r s '' (Z ∩ P)) = 0 := by
    refine Set.Subsingleton.measure_zero ?_ _
    exact ((subsingleton_affine_zero hrs).anti Set.inter_subset_right).image _
  have hsub : mobius p q r s '' Z ⊆
      mobius p q r s '' A ∪ mobius p q r s '' (Z ∩ P) := by
    rw [← Set.image_union]
    refine Set.image_mono ?_
    intro y hy
    by_cases h : y ∈ P
    · exact Or.inr ⟨hy, h⟩
    · exact Or.inl ⟨hy, h⟩
  exact measure_mono_null hsub (by
    simpa [himA, himP] using measure_union_null himA himP)

/-! ## Step 1: the non-CF-normal reals are covered by a null set -/

/-- The reals whose fractional part is not CF-normal sit inside a measurable Lebesgue
null set.  `ae_isCFNormal` gives this on `(0,1)` for the Gauss measure; the density
comparison moves it to Lebesgue and the `ℤ`-periodization of `Int.fract` spreads it
over `ℝ`. -/
lemma exists_null_cover_notCFNormal_fract :
    ∃ Z : Set ℝ, MeasurableSet Z ∧ volume Z = 0 ∧
      ∀ y : ℝ, ¬ IsCFNormal (Int.fract y) → y ∈ Z := by
  have hAnull : gaussMeasure {y | ¬ IsCFNormal y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact ae_isCFNormal
  obtain ⟨W₀, hW₀sub, hW₀meas, hW₀0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hAnull
  set W : Set ℝ := W₀ ∩ Set.Ioo (0 : ℝ) 1 with hW
  have hWmeas : MeasurableSet W := hW₀meas.inter measurableSet_Ioo
  have hWsub : W ⊆ Set.Ioo (0 : ℝ) 1 := Set.inter_subset_right
  have hWγ0 : gaussMeasure W = 0 :=
    measure_mono_null Set.inter_subset_left hW₀0
  have hWvol0 : volume W = 0 := by
    have h := volume_le_ofReal_mul_gaussMeasure W hWmeas hWsub
    rw [hWγ0, mul_zero] at h
    exact le_antisymm h (zero_le)
  refine ⟨Set.range ((↑) : ℤ → ℝ) ∪ ⋃ n : ℤ, (fun y : ℝ => y + (-(n : ℝ))) ⁻¹' W,
    ?_, ?_, ?_⟩
  · exact (Set.countable_range _).measurableSet.union
      (MeasurableSet.iUnion fun n => hWmeas.preimage (by fun_prop))
  · refine measure_union_null ((Set.countable_range _).measure_zero _) ?_
    refine measure_iUnion_null fun n => ?_
    rw [measure_preimage_add_right]
    exact hWvol0
  · intro y hy
    rcases eq_or_lt_of_le (Int.fract_nonneg y) with h0 | h0
    · left
      have : y = (⌊y⌋ : ℝ) := by
        have hfl := Int.floor_add_fract y
        rw [← h0] at hfl; linarith
      exact ⟨⌊y⌋, this.symm⟩
    · right
      refine Set.mem_iUnion.mpr ⟨⌊y⌋, ?_⟩
      have hmem : Int.fract y ∈ W := by
        refine ⟨hW₀sub hy, h0, Int.fract_lt_one y⟩
      simpa [Int.fract, sub_eq_add_neg] using hmem

/-! ## Step 2: the crux (Vandehey §2–§6) -/

/-- **(★) The crux of Vandehey 2017** — the conclusion of his §6 assembly.  For every
nonsingular integer matrix `(a b; c d)` and every genuine CF word `v`, the window
frequency of `v` in the CF expansion of `Mx` converges, to a limit `L` that does **not
depend on which CF-normal `x`** is fed in.  No value of `L` is asserted: the endgame
below computes it.

This is the whole transducer programme: §2 (Raney-style finite-state transducer on the
finite set `M_D` of det-`±D` normal forms), §3 (skew product `T̃(x,M) = (Tx, f_{a₁}(M))`
and its `T̃`-normality statement — the step needing the **tightness-corrected**
Pyatetskii-Shapiro criterion, see the module docstring), §4 (transitive components,
Cesàro counting for cylinder families with bounded overlap), §5 (trigger strings),
§6 (`ℓ(n) = c₁n(1+o(1))`, trigger counts `c_r n(1+o(1))`). -/
def VandeheyUniformFreq : Prop :=
  ∀ (a b c d : ℤ), a * d - b * c ≠ 0 → ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) →
    ∃ L : ℝ, ∀ x : ℝ, (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
      Filter.Tendsto
        (fun p => (countOccurrences v ((List.range p).map
            (cfDigit (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))))) : ℝ) / p)
        Filter.atTop (nhds L)

/-! ## Step 3: the either-or endgame (unconditional) -/

/-- **The pigeonhole witness.**  For a nonsingular integer matrix there is a real `x₀`
in `(0,1)` which is CF-normal, off the pole, and whose image `Mx₀` is CF-normal too.
Proof: the three bad sets — the pole (a subsingleton), the non-CF-normal reals (null by
`exists_null_cover_notCFNormal_fract`), and their `M`-preimage (null because the inverse
Möbius map pushes a null set to a null set, `volume_image_mobius_null`) — cannot cover
`(0,1)`, which has measure `1`. -/
theorem exists_cfNormal_with_cfNormal_image (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    ∃ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ (c : ℝ) * x + d ≠ 0 ∧
      IsCFNormal (Int.fract x) ∧
      IsCFNormal (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))) := by
  have hdetR : (a : ℝ) * d - b * c ≠ 0 := by
    intro h
    apply hdet
    have : ((a * d - b * c : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨Z, hZmeas, hZ0, hZcov⟩ := exists_null_cover_notCFNormal_fract
  -- the inverse Möbius map, with matrix `(d -b; -c a)`
  set g : ℝ → ℝ := mobius (d : ℝ) (-(b : ℝ)) (-(c : ℝ)) (a : ℝ) with hg
  have hgdet : (d : ℝ) * (a : ℝ) - (-(b : ℝ)) * (-(c : ℝ)) ≠ 0 := by
    intro h; exact hdetR (by linarith)
  have hgZ : volume (g '' Z) = 0 := volume_image_mobius_null _ _ _ _ hgdet hZmeas hZ0
  set P : Set ℝ := {y : ℝ | (c : ℝ) * y + d = 0} with hP
  have hcd : (c : ℝ) ≠ 0 ∨ (d : ℝ) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hdetR (by rw [hcon.1, hcon.2]; ring)
  have hP0 : volume P = 0 := (subsingleton_affine_zero hcd).measure_zero _
  set bad : Set ℝ := P ∪ Z ∪ g '' Z with hbad
  have hbad0 : volume bad = 0 :=
    measure_union_null (measure_union_null hP0 hZ0) hgZ
  have hnotsub : ¬ Set.Ioo (0 : ℝ) 1 ⊆ bad := by
    intro hsub
    have h1 : volume (Set.Ioo (0 : ℝ) 1) = 0 := measure_mono_null hsub hbad0
    rw [Real.volume_Ioo] at h1
    norm_num at h1
  obtain ⟨x, hxI, hxbad⟩ := Set.not_subset.mp hnotsub
  refine ⟨x, hxI, ?_, ?_, ?_⟩
  · intro h; exact hxbad (Or.inl (Or.inl (by simpa [hP] using h)))
  · by_contra h; exact hxbad (Or.inl (Or.inr (hZcov x h)))
  · by_contra h
    have hden : (c : ℝ) * x + d ≠ 0 := fun h' =>
      hxbad (Or.inl (Or.inl (by simpa [hP] using h')))
    set y : ℝ := ((a : ℝ) * x + b) / ((c : ℝ) * x + d) with hy
    have hyZ : y ∈ Z := hZcov y h
    have hy' : y * ((c : ℝ) * x + d) = (a : ℝ) * x + b := by
      rw [hy, div_mul_cancel₀ _ hden]
    have hnum : ((d : ℝ) * y + -(b : ℝ)) * ((c : ℝ) * x + d)
        = ((a : ℝ) * d - b * c) * x := by linear_combination (d : ℝ) * hy'
    have hden' : (-(c : ℝ) * y + (a : ℝ)) * ((c : ℝ) * x + d)
        = (a : ℝ) * d - b * c := by linear_combination (-(c : ℝ)) * hy'
    have hdene : -(c : ℝ) * y + (a : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hden'; exact hdetR hden'.symm
    have hgy : g y = x := by
      simp only [hg, mobius]
      rw [div_eq_iff hdene]
      have h1 : (((d : ℝ) * y + -(b : ℝ)) - x * (-(c : ℝ) * y + (a : ℝ)))
          * ((c : ℝ) * x + d) = 0 := by linear_combination hnum - x * hden'
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact absurd h2 hden
    exact hxbad (Or.inr ⟨y, hyZ, hgy⟩)

/-- **The either-or endgame**: the crux `VandeheyUniformFreq` implies Theorem 1.1.

The limit `L` given by the crux is independent of the CF-normal `x`.  By
`exists_cfNormal_with_cfNormal_image` there is *some* CF-normal `x₀` off the pole whose
image is CF-normal; for that `x₀` the same frequency sequence converges to
`γ(I_v)`.  Uniqueness of limits forces `L = γ(I_v)`, and hence every CF-normal `x` has
`Mx` CF-normal.  Vandehey computes no frequency anywhere — neither do we. -/
theorem vandehey_matrix_action_of_uniformFreq (h : VandeheyUniformFreq) :
    vandehey_matrix_action := by
  intro x a b c d hdet hden hx v hne hpos
  obtain ⟨L, hL⟩ := h a b c d hdet v hne hpos
  obtain ⟨x₀, hx₀I, hx₀den, hx₀n, hx₀img⟩ :=
    exists_cfNormal_with_cfNormal_image a b c d hdet
  have hLγ : L = (gaussMeasure (cfCylinder v)).toReal :=
    tendsto_nhds_unique (hL x₀ hx₀den hx₀n) (hx₀img v hne hpos)
  exact hLγ ▸ hL x hden hx

/-! ## Step 4: the headline -/

/-- The crux, still open: Vandehey §2–§6, with §3's hot-spot step to be replaced by the
tightness-corrected criterion (module docstring).  Disclosed `sorry`. -/
theorem vandeheyUniformFreq_holds : VandeheyUniformFreq := by
  sorry

/-- **Vandehey 2017, Theorem 1.1**: integer Möbius maps with nonzero determinant
preserve CF-normality. -/
theorem vandehey_matrix_action_holds : vandehey_matrix_action :=
  vandehey_matrix_action_of_uniformFreq vandeheyUniformFreq_holds

end NormalNumbers.Literature
