import NormalNumbers.CFScheduleA

/-!
# B6 Tier 2 — the affine FAMILY (simultaneous images)

Building on the measure route for the single affine map (`CFAeNormal.lean`,
`CFScheduleA.exists_cfNormal_and_affine_cfNormal`), this file proves the
**general-family** strengthening asked for by the B6 spec (`KHINCHIN.md`, "Tier 2"):

> Fix a COUNTABLE set `Q` of affine maps `ψ_{q,r}(x) = q·x + r` with `q > 0` and
> `r ≥ 0`.  Then there is a single `x ∈ (0,1)` such that `x` is CF-normal AND
> `ψ_{q,r}(x)` is CF-normal for EVERY `(q,r) ∈ Q` — simultaneously.

The single-map argument intersected two co-null sets on the feasible interval.
The family version is the same idea made uniform: the crux is that the
non-CF-normal set is **Lebesgue-null on all of `[0,∞)`** (not just on `(0,1)`),
which follows from the `(0,1)` nullity (`ae_isCFNormal`) plus integer-shift
invariance of CF-normality (`isCFNormal_add_nat`).  Given that, each
`{x : ¬ IsCFNormal (ψ x)}` is `γ`-null (affine pullback of a null set), and a
countable union of null sets is null, so the good set is co-null in `(0,1)` and
meets it.

Two forms are proved.  `exists_cfNormal_and_affine_family_cfNormal` assumes
`r ≥ 0` (images stay in `[0,∞)`, positive-shift crux `volume_notCFNormal_Ici0`).
`exists_cfNormal_and_affine_family_cfNormal'` is the FULL Vandehey §7 "Tier 2"
statement: `q > 0` and `r ∈ ℝ` arbitrary.  The negative half of the crux
(`volume_notCFNormal_univ`) uses the universal one-step descent
`cfDigit w (k+1) = cfDigit (gaussMap w) k` (so `w < 0` reduces to `gaussMap w ∈
[0,1)`) together with `gaussMap`-nonsingularity on the negatives, obtained by
writing `w ↦ Int.fract w⁻¹` on `Iio 0` as `inv ∘ (Int.fract-preimage)` and hitting
the null `Int.fract`-preimage with the differentiable-image-of-null lemma
(`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`).
-/

namespace NormalNumbers

open MeasureTheory Filter Set

/-- The non-CF-normal set is `γ`-null (repackaging of `ae_isCFNormal`). -/
lemma gaussMeasure_notCFNormal : gaussMeasure {y | ¬ IsCFNormal y} = 0 := by
  rw [← MeasureTheory.ae_iff]; exact ae_isCFNormal

/-- The non-CF-normal set is Lebesgue-null inside `(0,1)`.  (γ dominates a
positive multiple of Lebesgue on `(0,1)`, and the set is γ-null.) -/
lemma volume_notCFNormal_Ioo01 :
    volume ({y | ¬ IsCFNormal y} ∩ Set.Ioo (0 : ℝ) 1) = 0 := by
  obtain ⟨W₀, hW₀sub, hW₀meas, hW₀0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null gaussMeasure_notCFNormal
  set W := W₀ ∩ Set.Ioo (0 : ℝ) 1 with hW
  have hWmeas : MeasurableSet W := hW₀meas.inter measurableSet_Ioo
  have hWsub : W ⊆ Set.Ioo (0 : ℝ) 1 := Set.inter_subset_right
  have hWγ0 : gaussMeasure W = 0 :=
    le_antisymm (le_trans (measure_mono Set.inter_subset_left) (le_of_eq hW₀0)) (zero_le)
  have hWvol0 : volume W = 0 := by
    have h := volume_le_ofReal_mul_gaussMeasure W hWmeas hWsub
    rw [hWγ0, mul_zero] at h
    exact le_antisymm h (zero_le)
  refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hWvol0)) (zero_le)
  intro x hx
  exact ⟨hW₀sub hx.1, hx.2⟩

/-- **The Tier-2 crux.**  The non-CF-normal set is Lebesgue-null on all of
`[0,∞)`.  Every `w ≥ 0` reduces to its fractional representative `w - ⌊w⌋ ∈ [0,1)`
by the integer-shift invariance of CF-normality, so the bad set on `[0,∞)` is
covered by the countably many integer translates of the bad set on `(0,1)` plus
the (null) set of nonnegative integers. -/
lemma volume_notCFNormal_Ici0 :
    volume ({y | ¬ IsCFNormal y} ∩ Set.Ici (0 : ℝ)) = 0 := by
  set N : Set ℝ := {y | ¬ IsCFNormal y} with hN
  set N01 : Set ℝ := N ∩ Set.Ioo (0 : ℝ) 1 with hN01
  -- covering: every bad `w ≥ 0` is either a nonneg integer, or an integer
  -- translate of a bad point in `(0,1)`.
  have hcover : N ∩ Set.Ici (0 : ℝ) ⊆
      (⋃ n : ℕ, (fun t => t + (n : ℝ)) '' N01) ∪ Set.range (fun n : ℕ => (n : ℝ)) := by
    intro w hw
    obtain ⟨hwN, hw0⟩ := hw
    have hw0' : (0 : ℝ) ≤ w := hw0
    set n : ℕ := ⌊w⌋₊ with hn
    set z : ℝ := w - (n : ℝ) with hz
    have hzlt : z < 1 := by rw [hz]; have := Nat.lt_floor_add_one w; simp only [hn]; linarith
    have hz0 : 0 ≤ z := by rw [hz]; have := Nat.floor_le hw0'; simp only [hn]; linarith
    by_cases hzpos : 0 < z
    · -- `z ∈ (0,1)`, bad, and `w = z + n`
      have hzIoo : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨hzpos, hzlt⟩
      have hzbad : ¬ IsCFNormal z := by
        intro hzcf
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · apply hwN
          have : w = z := by rw [hz, hn0]; simp
          rwa [this]
        · exact hwN (by
            have := isCFNormal_add_nat hzIoo hnpos hzcf
            have hwz : w = z + (n : ℝ) := by rw [hz]; ring
            rwa [hwz])
      refine Or.inl (Set.mem_iUnion.mpr ⟨n, ?_⟩)
      exact ⟨z, ⟨hzbad, hzIoo⟩, by rw [hz]; ring⟩
    · -- `z = 0`, i.e. `w = n` is a nonneg integer
      have hzeq : z = 0 := le_antisymm (not_lt.mp hzpos) hz0
      refine Or.inr ⟨n, ?_⟩
      have : w = (n : ℝ) := by rw [hz] at hzeq; linarith
      exact this.symm
  -- each piece is null
  have hN01vol : volume N01 = 0 := volume_notCFNormal_Ioo01
  have htransl : ∀ n : ℕ, volume ((fun t => t + (n : ℝ)) '' N01) = 0 := by
    intro n
    -- `(· + n) '' N01 = affineMap 1 (-n) ⁻¹' N01`
    have himg : (fun t => t + (n : ℝ)) '' N01 = affineMap 1 (-(n : ℝ)) ⁻¹' N01 := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, affineMap_apply, one_mul]
      constructor
      · rintro ⟨t, ht, rfl⟩
        have : t + (n : ℝ) + -(n : ℝ) = t := by ring
        rw [this]; exact ht
      · intro hx
        refine ⟨x + -(n : ℝ), hx, ?_⟩
        ring
    rw [himg, volume_preimage_affineMap (one_ne_zero) (-(n : ℝ)) N01, hN01vol, mul_zero]
  have hunionvol : volume (⋃ n : ℕ, (fun t => t + (n : ℝ)) '' N01) = 0 :=
    measure_iUnion_null htransl
  have hrangevol : volume (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero volume
  refine le_antisymm (le_trans (measure_mono hcover) ?_) (zero_le)
  calc volume ((⋃ n : ℕ, (fun t => t + (n : ℝ)) '' N01) ∪ Set.range (fun n : ℕ => (n : ℝ)))
      ≤ volume (⋃ n : ℕ, (fun t => t + (n : ℝ)) '' N01)
          + volume (Set.range (fun n : ℕ => (n : ℝ))) := measure_union_le _ _
    _ = 0 := by rw [hunionvol, hrangevol, add_zero]

/-- For `q > 0` and `r ≥ 0`, the set of `x ∈ (0,1)` whose affine image is NOT
CF-normal is `γ`-null.  On the domain `(0,1)` the image `ψ x = q·x + r > 0`
lands in `[0,∞)`, where the bad set is Lebesgue-null; pulling that null set back
through `ψ` (Lebesgue scaling) and dominating `γ ≤ C · volume` gives the result. -/
lemma gaussMeasure_notCFNormal_affine_Ioo01 {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r) :
    gaussMeasure ({x | ¬ IsCFNormal (affineMap q r x)} ∩ Set.Ioo (0 : ℝ) 1) = 0 := by
  obtain ⟨V, hVsub, hVmeas, hV0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null volume_notCFNormal_Ici0
  -- pull `V` back through `ψ`
  have hpreVvol : volume (affineMap q r ⁻¹' V) = 0 := by
    rw [volume_preimage_affineMap hq.ne' r V, hV0, mul_zero]
  have hpreVγ : gaussMeasure (affineMap q r ⁻¹' V) = 0 := by
    have h := gaussMeasure_le_volume (affineMap q r ⁻¹' V)
      (measurable_affineMap' q r hVmeas)
    rw [hpreVvol, mul_zero] at h
    exact le_antisymm h (zero_le)
  refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hpreVγ)) (zero_le)
  intro x hx
  obtain ⟨hxbad, hx0, hx1⟩ := hx
  -- `ψ x = q x + r > 0`, so `ψ x ∈ N ∩ Ici 0 ⊆ V`, i.e. `x ∈ ψ⁻¹ V`
  have hψx0 : (0 : ℝ) ≤ affineMap q r x := by
    simp only [affineMap_apply]; nlinarith [mul_pos hq hx0]
  exact hVsub ⟨hxbad, hψx0⟩

/-- `γ(0,1) > 0`. -/
lemma gaussMeasure_Ioo01_pos : 0 < gaussMeasure (Set.Ioo (0 : ℝ) 1) := by
  rw [gaussMeasure_Ioo (le_refl 0) (by norm_num) (le_refl 1), ENNReal.ofReal_pos]
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  apply div_pos _ hlog
  have : Real.log (1 + 0) < Real.log (1 + 1) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## Negative branch — removing the `r ≥ 0` restriction

The image `ψ((0,1)) = (r, q+r)` dips below `0` exactly when `r < 0`.  To cover
that we upgrade the crux from `[0,∞)` to all of `ℝ`: the non-CF-normal set is
Lebesgue-null everywhere.  The negative half reduces via the UNIVERSAL one-step
identity `cfDigit w (k+1) = cfDigit (gaussMap w) k` and the fact that for `w < 0`
the single Gauss step already lands in `[0,1)`; nonsingularity of `gaussMap` on
the negatives is handled by writing it as `inv ∘ (translate of Int.fract)` and
invoking the differentiable-image-of-null lemma. -/

/-- `gaussMap w ∈ [0,1)` for every `w`. -/
lemma gaussMap_mem_Ico01 (w : ℝ) : gaussMap w ∈ Set.Ico (0 : ℝ) 1 := by
  unfold gaussMap
  split_ifs with h
  · exact ⟨le_refl 0, by norm_num⟩
  · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **Universal one-step CF-normality descent.**  `IsCFNormal (gaussMap w) →
IsCFNormal w` for ANY `w`: the digit sequence of `w` is that of `gaussMap w`
shifted right by one (`cfDigit w (k+1) = cfDigit (gaussMap w) k`), and a
one-place shift preserves every window-frequency limit. -/
lemma isCFNormal_of_gaussMap {w : ℝ} (h : IsCFNormal (gaussMap w)) : IsCFNormal w := by
  intro v hv hpos
  refine cfFreq_tendsto_of_digit_shift (cfDigit (gaussMap w)) (cfDigit w) 1 ?_ v hv (h v hv hpos)
  intro k
  show cfDigit w (k + 1) = cfDigit (gaussMap w) k
  unfold cfDigit
  rw [Function.iterate_succ_apply]

/-- The non-CF-normal set is Lebesgue-null inside `[0,1)`. -/
lemma volume_notCFNormal_Ico01 :
    volume ({y | ¬ IsCFNormal y} ∩ Set.Ico (0 : ℝ) 1) = 0 := by
  have hsub : {y | ¬ IsCFNormal y} ∩ Set.Ico (0:ℝ) 1 ⊆
      ({y | ¬ IsCFNormal y} ∩ Set.Ioo (0:ℝ) 1) ∪ {(0:ℝ)} := by
    intro x ⟨hxN, hx0, hx1⟩
    rcases eq_or_lt_of_le hx0 with h | h
    · exact Or.inr (Set.mem_singleton_iff.mpr h.symm)
    · exact Or.inl ⟨hxN, h, hx1⟩
  refine le_antisymm (le_trans (measure_mono hsub) ?_) (zero_le)
  calc volume (({y | ¬ IsCFNormal y} ∩ Set.Ioo (0:ℝ) 1) ∪ {(0:ℝ)})
      ≤ volume ({y | ¬ IsCFNormal y} ∩ Set.Ioo (0:ℝ) 1) + volume ({(0:ℝ)}) :=
        measure_union_le _ _
    _ = 0 := by rw [volume_notCFNormal_Ioo01, Real.volume_singleton, add_zero]

/-- `Int.fract`-preimage of the `[0,1)`-bad set is Lebesgue-null: it is the
`ℤ`-translate union of the bad set. -/
lemma volume_fract_preimage_notCFNormal :
    volume (Int.fract ⁻¹' ({y | ¬ IsCFNormal y} ∩ Set.Ico (0 : ℝ) 1)) = 0 := by
  set Z : Set ℝ := {y | ¬ IsCFNormal y} ∩ Set.Ico (0 : ℝ) 1 with hZ
  have hZsub : Z ⊆ Set.Ico (0 : ℝ) 1 := Set.inter_subset_right
  have hZ0 : volume Z = 0 := volume_notCFNormal_Ico01
  -- `Int.fract ⁻¹' Z = ⋃ n : ℤ, (· + n) '' Z`
  have heq : Int.fract ⁻¹' Z = ⋃ n : ℤ, (fun t => t + (n : ℝ)) '' Z := by
    ext u
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hu
      refine ⟨⌊u⌋, u - (⌊u⌋ : ℝ), ?_, by ring⟩
      have : Int.fract u = u - (⌊u⌋ : ℝ) := rfl
      rwa [this] at hu
    · rintro ⟨n, z, hz, rfl⟩
      have hzIco : z ∈ Set.Ico (0:ℝ) 1 := hZsub hz
      rw [Int.fract_add_intCast, Int.fract_eq_self.mpr hzIco]
      exact hz
  rw [heq]
  refine le_antisymm (le_trans (measure_iUnion_le _) ?_) (zero_le)
  have : ∀ n : ℤ, volume ((fun t => t + (n : ℝ)) '' Z) = 0 := by
    intro n
    have himg : (fun t => t + (n : ℝ)) '' Z = affineMap 1 (-(n : ℝ)) ⁻¹' Z := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, affineMap_apply, one_mul]
      constructor
      · rintro ⟨t, ht, rfl⟩
        have : t + (n : ℝ) + -(n : ℝ) = t := by ring
        rw [this]; exact ht
      · intro hx; exact ⟨x + -(n : ℝ), hx, by ring⟩
    rw [himg, volume_preimage_affineMap one_ne_zero (-(n : ℝ)) Z, hZ0, mul_zero]
  simp only [this, tsum_zero, le_refl]

/-- **The full crux.**  The non-CF-normal set is Lebesgue-null on all of `ℝ`.
The `[0,∞)` half is `volume_notCFNormal_Ici0`; the `(-∞,0)` half descends one
Gauss step into `[0,1)` and pulls back through `inv` (differentiable off `0`),
the image of the null `Int.fract`-preimage set. -/
lemma volume_notCFNormal_univ : volume {y | ¬ IsCFNormal y} = 0 := by
  set N : Set ℝ := {y | ¬ IsCFNormal y} with hN
  set Z : Set ℝ := N ∩ Set.Ico (0 : ℝ) 1 with hZ
  -- negative half
  have hIio : volume (N ∩ Set.Iio (0 : ℝ)) = 0 := by
    -- `N ∩ Iio 0 ⊆ (·⁻¹) '' (Int.fract ⁻¹' Z ∩ Iio 0)`
    have hsub : N ∩ Set.Iio (0 : ℝ) ⊆ (fun w => w⁻¹) '' (Int.fract ⁻¹' Z ∩ Set.Iio (0 : ℝ)) := by
      intro w ⟨hwN, hw0⟩
      have hwne : w ≠ 0 := ne_of_lt hw0
      -- `gaussMap w = Int.fract w⁻¹` and it is bad
      have hgbad : ¬ IsCFNormal (gaussMap w) := fun hg => hwN (isCFNormal_of_gaussMap hg)
      have hgeq : gaussMap w = Int.fract w⁻¹ := by unfold gaussMap; rw [if_neg hwne]
      have hgZ : Int.fract w⁻¹ ∈ Z := by
        refine ⟨?_, ?_⟩
        · rw [← hgeq]; exact hgbad
        · rw [← hgeq]; exact gaussMap_mem_Ico01 w
      refine ⟨w⁻¹, ⟨?_, ?_⟩, inv_inv w⟩
      · exact hgZ
      · exact Set.mem_Iio.mpr (inv_lt_zero'.mpr hw0)
    refine le_antisymm (le_trans (measure_mono hsub) ?_) (zero_le)
    -- image of a null set under `inv` (differentiable on `Iio 0`) is null
    have hWnull : volume (Int.fract ⁻¹' Z ∩ Set.Iio (0 : ℝ)) = 0 :=
      measure_inter_null_of_null_left _ volume_fract_preimage_notCFNormal
    have hdiff : DifferentiableOn ℝ (fun w => w⁻¹) (Int.fract ⁻¹' Z ∩ Set.Iio (0 : ℝ)) := by
      intro x hx
      exact (differentiableAt_inv (ne_of_lt hx.2)).differentiableWithinAt
    exact le_of_eq (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hWnull)
  -- combine with `[0,∞)`
  have hcover : N = (N ∩ Set.Ici (0 : ℝ)) ∪ (N ∩ Set.Iio (0 : ℝ)) := by
    rw [← Set.inter_union_distrib_left, Set.Ici_union_Iio, Set.inter_univ]
  rw [hcover]
  refine le_antisymm (le_trans (measure_union_le _ _) ?_) (zero_le)
  rw [volume_notCFNormal_Ici0, hIio, add_zero]

/-- For any `q > 0` and any real `r`, the set of `x ∈ (0,1)` whose affine image
is not CF-normal is `γ`-null.  (Full-generality upgrade of
`gaussMeasure_notCFNormal_affine_Ioo01`, using the `ℝ`-wide null crux.) -/
lemma gaussMeasure_notCFNormal_affine_Ioo01' {q : ℝ} (hq : 0 < q) (r : ℝ) :
    gaussMeasure ({x | ¬ IsCFNormal (affineMap q r x)} ∩ Set.Ioo (0 : ℝ) 1) = 0 := by
  obtain ⟨V, hVsub, hVmeas, hV0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null volume_notCFNormal_univ
  have hpreVvol : volume (affineMap q r ⁻¹' V) = 0 := by
    rw [volume_preimage_affineMap hq.ne' r V, hV0, mul_zero]
  have hpreVγ : gaussMeasure (affineMap q r ⁻¹' V) = 0 := by
    have h := gaussMeasure_le_volume (affineMap q r ⁻¹' V) (measurable_affineMap' q r hVmeas)
    rw [hpreVvol, mul_zero] at h
    exact le_antisymm h (zero_le)
  refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hpreVγ)) (zero_le)
  intro x hx
  exact hVsub hx.1

/-- **B6 Tier 2 (full generality) — the affine FAMILY, any real shifts.**  For
any countable set `Q` of pairs `(q, r)` with `q > 0` (and `r ∈ ℝ` arbitrary),
there is a single `x ∈ (0,1)` that is CF-normal and whose affine image `q·x + r`
is CF-normal for EVERY `(q, r) ∈ Q`, simultaneously.  This is the faithful
statement of Vandehey §7 "Tier 2" (no sign restriction on the shift). -/
theorem exists_cfNormal_and_affine_family_cfNormal'
    (Q : Set (ℝ × ℝ)) (hQ : Q.Countable) (hq : ∀ p ∈ Q, 0 < p.1) :
    ∃ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ IsCFNormal x ∧
      ∀ p ∈ Q, IsCFNormal (affineMap p.1 p.2 x) := by
  set A : Set ℝ := {x | ¬ IsCFNormal x} ∩ Set.Ioo (0 : ℝ) 1 with hA
  set Bad : ∀ _ : ℝ × ℝ, Set ℝ :=
    fun p => {x | ¬ IsCFNormal (affineMap p.1 p.2 x)} ∩ Set.Ioo (0 : ℝ) 1 with hBad
  have hA0 : gaussMeasure A = 0 :=
    le_antisymm (le_trans (measure_mono Set.inter_subset_left)
      (le_of_eq gaussMeasure_notCFNormal)) (zero_le)
  have hBad0 : ∀ p ∈ Q, gaussMeasure (Bad p) = 0 :=
    fun p hp => gaussMeasure_notCFNormal_affine_Ioo01' (hq p hp) p.2
  have hBadU0 : gaussMeasure (⋃ p ∈ Q, Bad p) = 0 :=
    (measure_biUnion_null_iff hQ).mpr hBad0
  set BadAll : Set ℝ := A ∪ ⋃ p ∈ Q, Bad p with hBadAll
  have hBadAll0 : gaussMeasure BadAll = 0 :=
    le_antisymm (le_trans (measure_union_le _ _) (by rw [hA0, hBadU0, add_zero])) (zero_le)
  have hgood : gaussMeasure (Set.Ioo (0 : ℝ) 1 \ BadAll) = gaussMeasure (Set.Ioo (0 : ℝ) 1) :=
    measure_sdiff_null hBadAll0
  obtain ⟨x, hxIoo, hxBad⟩ := nonempty_of_measure_ne_zero
    (by rw [hgood]; exact gaussMeasure_Ioo01_pos.ne')
  have hxN : IsCFNormal x := by
    by_contra hxc; exact hxBad (Or.inl ⟨hxc, hxIoo⟩)
  refine ⟨x, hxIoo, hxN, ?_⟩
  intro p hp
  by_contra hxc
  exact hxBad (Or.inr (Set.mem_biUnion hp ⟨hxc, hxIoo⟩))

/-- **B6 Tier 2 — the affine FAMILY.**  For any countable set `Q` of pairs
`(q, r)` with `q > 0` and `r ≥ 0`, there is a single `x ∈ (0,1)` that is
CF-normal and whose affine image `q·x + r` is CF-normal for EVERY `(q, r) ∈ Q`,
simultaneously.  A constructive-in-spirit (measure-existence) strengthening of
`exists_cfNormal_and_affine_cfNormal` from one map to a whole countable family —
the "Tier 2" of the Vandehey §7 affine-image spec. -/
theorem exists_cfNormal_and_affine_family_cfNormal
    (Q : Set (ℝ × ℝ)) (hQ : Q.Countable)
    (hqr : ∀ p ∈ Q, 0 < p.1 ∧ 0 ≤ p.2) :
    ∃ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ IsCFNormal x ∧
      ∀ p ∈ Q, IsCFNormal (affineMap p.1 p.2 x) := by
  set A : Set ℝ := {x | ¬ IsCFNormal x} ∩ Set.Ioo (0 : ℝ) 1 with hA
  set Bad : ∀ _ : ℝ × ℝ, Set ℝ :=
    fun p => {x | ¬ IsCFNormal (affineMap p.1 p.2 x)} ∩ Set.Ioo (0 : ℝ) 1 with hBad
  have hA0 : gaussMeasure A = 0 :=
    le_antisymm (le_trans (measure_mono Set.inter_subset_left)
      (le_of_eq gaussMeasure_notCFNormal)) (zero_le)
  have hBad0 : ∀ p ∈ Q, gaussMeasure (Bad p) = 0 := by
    intro p hp
    obtain ⟨hq, hr⟩ := hqr p hp
    exact gaussMeasure_notCFNormal_affine_Ioo01 hq hr
  have hBadU0 : gaussMeasure (⋃ p ∈ Q, Bad p) = 0 :=
    (measure_biUnion_null_iff hQ).mpr hBad0
  set BadAll : Set ℝ := A ∪ ⋃ p ∈ Q, Bad p with hBadAll
  have hBadAll0 : gaussMeasure BadAll = 0 :=
    le_antisymm (le_trans (measure_union_le _ _) (by rw [hA0, hBadU0, add_zero])) (zero_le)
  -- the good region has positive γ-measure ⇒ nonempty
  have hgood : gaussMeasure (Set.Ioo (0 : ℝ) 1 \ BadAll) = gaussMeasure (Set.Ioo (0 : ℝ) 1) :=
    measure_sdiff_null hBadAll0
  obtain ⟨x, hxIoo, hxBad⟩ := nonempty_of_measure_ne_zero
    (by rw [hgood]; exact gaussMeasure_Ioo01_pos.ne')
  -- decode: `x` is CF-normal and every image is CF-normal
  have hxN : IsCFNormal x := by
    by_contra hxc
    exact hxBad (Or.inl ⟨hxc, hxIoo⟩)
  refine ⟨x, hxIoo, hxN, ?_⟩
  intro p hp
  by_contra hxc
  refine hxBad (Or.inr ?_)
  exact Set.mem_biUnion hp ⟨hxc, hxIoo⟩

end NormalNumbers
