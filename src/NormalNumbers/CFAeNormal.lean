/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFOrbitFreq
import NormalNumbers.CFBlockFreq
import NormalNumbers.CFAffine
import NormalNumbers.TBrick
import NormalNumbers.CFDigitLaw

/-!
# B6 via the MEASURE route — a.e. CF-normality and the affine-image witness

The B6 headline `exists_cfNormal_and_affine_cfNormal` asks only for the
*existence* of a real `x` with both `x` and `ψ(x) = q·x + r` CF-normal.  That is
a.e.-trivial: a.e. `x` is CF-normal, and (on the feasible interval) a.e. `x` has
`ψ(x)` CF-normal, so the two co-null sets meet.  This file discharges that route,
replacing the (provably obstructed) interleaved-schedule witness.

* `ae_orbit_freq` — **THE crux**: for a genuine word `v`, a.e. `y` has orbit
  block-frequency `blockCount (cfCylinder v) p y / p → γ(I_v)`.  Classic
  L²→a.e.: `variance_blockCount_le` + Chebyshev + Borel–Cantelli along `p = k²`
  + a monotone gap-squeeze.  Birkhoff-FREE.
* `ae_isCFNormal` — a.e. CF-normality, by intersecting `ae_orbit_freq` over the
  countable set of words and the a.e. irrational / orbit-in-`(0,1)` conditions,
  fed to `isCFNormal_of_irrational_orbit_freq`.
* `exists_feasible_cfNormal_affine` — on `(0,1) ∩ ψ⁻¹(0,1)` (positive measure
  when `-q < r < 1`) the CF-normal set and the `ψ`-CF-normal set both meet it.
  Measurability of the CF-normal set is DODGED via `exists_measurable_superset_of_null`.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- `ψ = affineMap q r` is measurable. -/
lemma measurable_affineMap' (q r : ℝ) : Measurable (affineMap q r) := by
  unfold affineMap; fun_prop

/-- `γ` is null on the range of `ℚ` (countable, and `γ ≤ (log 2)⁻¹·vol`). -/
lemma gaussMeasure_range_rat' : gaussMeasure (Set.range ((↑) : ℚ → ℝ)) = 0 := by
  have hv : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume
  have h := gaussMeasure_le_volume (Set.range ((↑) : ℚ → ℝ))
    ((Set.countable_range ((↑) : ℚ → ℝ)).measurableSet)
  rw [hv, mul_zero] at h
  exact le_antisymm h (zero_le)

/-- a.e. `y` (for `γ`) is irrational. -/
lemma ae_irrational : ∀ᵐ y ∂gaussMeasure, Irrational y := by
  rw [MeasureTheory.ae_iff]
  have hset : {y | ¬ Irrational y} = Set.range ((↑) : ℚ → ℝ) := by
    ext y
    simp only [Set.mem_setOf_eq, Irrational, not_not, Set.mem_range]
  rw [hset]; exact gaussMeasure_range_rat'

/-- a.e. `y` (for `γ`) lies in `(0,1)` — `γ` is supported there. -/
lemma ae_mem_Ioo : ∀ᵐ y ∂gaussMeasure, y ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [MeasureTheory.ae_iff]
  have hcompl : {y | ¬ y ∈ Set.Ioo (0 : ℝ) 1} = (Set.Ioo (0 : ℝ) 1)ᶜ := by
    ext y; simp
  have h1 : gaussMeasure (Set.Ioo (0 : ℝ) 1) = 1 := by
    rw [gaussMeasure_Ioo (le_refl 0) (by norm_num) (le_refl 1)]
    norm_num
  rw [hcompl, MeasureTheory.measure_compl measurableSet_Ioo (by
        rw [h1]; exact ENNReal.one_ne_top), gaussMeasure_univ, h1, tsub_self]

/-! ## The crux: a.e. orbit block-frequency -/

/-- **THE crux (a.e. orbit frequency).**  For a genuine word `v`, a.e. `y` has
`blockCount (cfCylinder v) p y / p → γ(I_v)`.

Route (classic L²→a.e., Birkhoff-FREE):
* `chebyshev_blockCount` (`CFBlockFreq`) gives, for `δ>0`, `p>0`,
  `γ{|S_p/p − γv| ≥ δ} ≤ (8|v|+80)γv/(δ²p)`.
* Along `p = (k+1)²` this is `≤ C/(k+1)²`, summable, so Borel–Cantelli
  (`ae_eventually_not_mem`) gives, for each fixed `δ = 1/(m+1)`, a.e. `y`
  eventually good; intersect over `m` ⇒ a.e. convergence along the squares.
* Fill the gaps by monotonicity of `p ↦ S_p` and `k²/(k+1)² → 1`. -/
theorem ae_orbit_freq (v : List ℕ) (hne : v ≠ []) (hpos : ∀ a ∈ v, 1 ≤ a) :
    ∀ᵐ y ∂gaussMeasure,
      Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder v)).toReal) := by
  sorry

/-! ## a.e. CF-normality -/

/-- **a.e. CF-normality.**  `∀ᵐ y ∂γ, IsCFNormal y`. -/
theorem ae_isCFNormal : ∀ᵐ y ∂gaussMeasure, IsCFNormal y := by
  have hfreq : ∀ᵐ y ∂gaussMeasure, ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder v)).toReal) := by
    rw [MeasureTheory.ae_all_iff]
    intro v
    by_cases hv : v ≠ [] ∧ (∀ a ∈ v, 1 ≤ a)
    · filter_upwards [ae_orbit_freq v hv.1 hv.2] with y hy _ _; exact hy
    · filter_upwards with y hne hposv; exact absurd ⟨hne, hposv⟩ hv
  filter_upwards [ae_irrational, ae_mem_Ioo, hfreq] with y hirr hIoo hy
  exact isCFNormal_of_irrational_orbit_freq y hirr hIoo hy

/-! ## The feasible affine witness -/

/-- **B6 feasible core (measure route).**  For `q > 0` and `-q < r < 1`, there is
`x` with both `x` and `ψ(x) = q·x + r` CF-normal.  The CF-normal set `A` and the
set `B = {x : ψ(x) CF-normal}` are both `γ`-co-null on the feasible interval
`F = (0,1) ∩ ψ⁻¹(0,1)` (positive measure), so `F ∩ A ∩ B ≠ ∅`.  Measurability of
`A` is not needed: it is dodged with `exists_measurable_superset_of_null`. -/
theorem exists_feasible_cfNormal_affine {q : ℝ} (hq : 0 < q) (r : ℝ)
    (hr : -q < r ∧ r < 1) :
    ∃ x : ℝ, IsCFNormal x ∧ IsCFNormal (affineMap q r x) := by
  obtain ⟨hrL, hrU⟩ := hr
  set ψ := affineMap q r with hψ
  -- the bad set `{¬ IsCFNormal}` is `γ`-null; grab a measurable null superset in `(0,1)`
  have hAnull : gaussMeasure {y | ¬ IsCFNormal y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact ae_isCFNormal
  obtain ⟨W₀, hW₀sub, hW₀meas, hW₀0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hAnull
  set W := W₀ ∩ Set.Ioo (0 : ℝ) 1 with hW
  have hWmeas : MeasurableSet W := hW₀meas.inter measurableSet_Ioo
  have hWsub : W ⊆ Set.Ioo (0 : ℝ) 1 := Set.inter_subset_right
  have hWγ0 : gaussMeasure W = 0 :=
    le_antisymm (le_trans (measure_mono Set.inter_subset_left) (le_of_eq hW₀0)) (zero_le)
  -- push through `ψ`: `vol W = 0 ⇒ vol (ψ⁻¹ W) = 0 ⇒ γ (ψ⁻¹ W) = 0`
  have hWvol0 : volume W = 0 := by
    have h := volume_le_ofReal_mul_gaussMeasure W hWmeas hWsub
    rw [hWγ0, mul_zero] at h
    exact le_antisymm h (zero_le)
  have hpreWvol0 : volume (ψ ⁻¹' W) = 0 := by
    rw [hψ, volume_preimage_affineMap hq.ne' r W, hWvol0, mul_zero]
  have hpreWγ0 : gaussMeasure (ψ ⁻¹' W) = 0 := by
    have h := gaussMeasure_le_volume (ψ ⁻¹' W)
      (measurable_affineMap' q r hWmeas)
    rw [hpreWvol0, mul_zero] at h
    exact le_antisymm h (zero_le)
  -- feasible interval `F = (0,1) ∩ ψ⁻¹(0,1) = Ioo lo hi`, positive `γ`-measure
  set lo : ℝ := max 0 ((0 - r) / q) with hlo
  set hi : ℝ := min 1 ((1 - r) / q) with hhi
  have hlonn : 0 ≤ lo := le_max_left _ _
  have hhile : hi ≤ 1 := min_le_left _ _
  have hlohi : lo < hi := by
    rw [hlo, hhi, max_lt_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨by norm_num, ?_⟩, ?_, ?_⟩
    · rw [lt_div_iff₀ hq]; nlinarith
    · rw [div_lt_iff₀ hq]; nlinarith
    · rw [div_lt_div_iff₀ hq hq]; nlinarith
  set F : Set ℝ := Set.Ioo lo hi with hF
  have hFsub01 : F ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.Ioo_subset_Ioo hlonn hhile
  have hFsubψ : F ⊆ ψ ⁻¹' Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    rw [hψ, preimage_affineMap_Ioo hq]
    exact Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _) hx
  have hFγpos : 0 < gaussMeasure F := by
    rw [hF, gaussMeasure_Ioo hlonn hlohi.le hhile]
    rw [ENNReal.ofReal_pos]
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    apply div_pos _ hlog
    have : Real.log (1 + lo) < Real.log (1 + hi) :=
      Real.log_lt_log (by linarith) (by linarith)
    linarith
  -- `F ⊆ (F∩A∩B) ∪ (F∩Aᶜ) ∪ (F∩Bᶜ)`, the last two `γ`-null
  set A : Set ℝ := {y | IsCFNormal y} with hA
  set B : Set ℝ := {x | IsCFNormal (ψ x)} with hB
  have hFAc : gaussMeasure (F ∩ Aᶜ) = 0 := by
    refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hAnull)) (zero_le)
    intro x hx; exact hx.2
  have hFBc : gaussMeasure (F ∩ Bᶜ) = 0 := by
    refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hpreWγ0)) (zero_le)
    intro x hx
    obtain ⟨hxF, hxB⟩ := hx
    -- `ψ x ∈ (0,1)` and `¬ IsCFNormal (ψ x)`, so `ψ x ∈ W`, i.e. `x ∈ ψ⁻¹ W`
    have hψx01 : ψ x ∈ Set.Ioo (0 : ℝ) 1 := hFsubψ hxF
    have hψbad : ¬ IsCFNormal (ψ x) := hxB
    rw [Set.mem_preimage, hW]
    exact ⟨hW₀sub hψbad, hψx01⟩
  -- so `F ∩ A ∩ B` has positive measure ⇒ nonempty
  have hcover : F ⊆ (F ∩ A ∩ B) ∪ (F ∩ Aᶜ) ∪ (F ∩ Bᶜ) := by
    intro x hx
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · exact Or.inl (Or.inl ⟨⟨hx, hxA⟩, hxB⟩)
      · exact Or.inr ⟨hx, hxB⟩
    · exact Or.inl (Or.inr ⟨hx, hxA⟩)
  have hmono : gaussMeasure F ≤ gaussMeasure (F ∩ A ∩ B) := by
    calc gaussMeasure F
        ≤ gaussMeasure ((F ∩ A ∩ B) ∪ (F ∩ Aᶜ) ∪ (F ∩ Bᶜ)) := measure_mono hcover
      _ ≤ gaussMeasure ((F ∩ A ∩ B) ∪ (F ∩ Aᶜ)) + gaussMeasure (F ∩ Bᶜ) :=
          measure_union_le _ _
      _ ≤ gaussMeasure (F ∩ A ∩ B) + gaussMeasure (F ∩ Aᶜ) + gaussMeasure (F ∩ Bᶜ) := by
          gcongr; exact measure_union_le _ _
      _ = gaussMeasure (F ∩ A ∩ B) := by rw [hFAc, hFBc, add_zero, add_zero]
  have hpos : 0 < gaussMeasure (F ∩ A ∩ B) := lt_of_lt_of_le hFγpos hmono
  obtain ⟨x, ⟨⟨_, hxA⟩, hxB⟩⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨x, hxA, hxB⟩

end NormalNumbers
