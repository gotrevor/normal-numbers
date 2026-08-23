/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFMixing
import NormalNumbers.CFGammaMixing

/-!
# W4 — block-frequency variance and Chebyshev (lap-authored groundwork)

The Becher–Yuhjtman construction needs, for each stage, that the set of points
whose CF-block frequency deviates from `γ(I_v)` has measure `< ¼` of the base
brick.  With the *efficiency-free* substitute (this expedition's charter: no
CLT, no KPW large deviations), this is a plain second-moment / Chebyshev
argument fed by the proven γ-mixing engine `gaussMeasure_cylinder_mixing`.

Route (dependency order):

* `blockCount A n x = #{k < n : Tᵏx ∈ A}` as a real Birkhoff sum of `1_A`.
* `integral_blockCount` — **first moment** `∫ S_n dγ = n·γ(A)`.
* `gaussMeasureReal_pair_shift` — **pair invariance**
  `γ(T^{-j}A ∩ T^{-(j+m)}A) = γ(A ∩ T^{-m}A)`.
* `integral_blockCount_sq` — **second moment**
  `∫ S_n² dγ = Σ_{j,j' < n} γ(T^{-j}A ∩ T^{-j'}A)`.
* `abs_cov_le` — **per-pair covariance bound** from γ-mixing: geometric for
  gap `≥ |v|`, crude for gap `< |v|`.
* variance bound + Chebyshev (in progress — the remaining double-sum
  bookkeeping over `abs_cov_le`).

Since γ is a probability measure and `S_n` is a finite sum of `[0,1]`-valued
indicators, every integrability side-condition is immediate.
-/

namespace NormalNumbers

open MeasureTheory

/-- The Gauss measure is a probability measure (`gaussMeasure_univ`). -/
instance : IsProbabilityMeasure gaussMeasure := ⟨gaussMeasure_univ⟩

/-! ## The block-count Birkhoff sum -/

/-- The `ℝ`-valued indicator of `A`. -/
noncomputable def blockIndic (A : Set ℝ) : ℝ → ℝ := A.indicator (1 : ℝ → ℝ)

/-- `blockCount A n x = #{k < n : gaussMapᵏ x ∈ A}`, as a real number:
the Birkhoff sum of `1_A` over the Gauss map. -/
noncomputable def blockCount (A : Set ℝ) (n : ℕ) : ℝ → ℝ :=
  birkhoffSum gaussMap (blockIndic A) n

lemma blockCount_apply (A : Set ℝ) (n : ℕ) (x : ℝ) :
    blockCount A n x = ∑ k ∈ Finset.range n, blockIndic A (gaussMap^[k] x) := rfl

/-- Composing the indicator with an iterate is the indicator of the preimage. -/
lemma blockIndic_iterate (A : Set ℝ) (k : ℕ) (x : ℝ) :
    blockIndic A (gaussMap^[k] x) = blockIndic ((gaussMap^[k]) ⁻¹' A) x := by
  unfold blockIndic
  by_cases h : gaussMap^[k] x ∈ A
  · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mpr h),
      Pi.one_apply]
  · simp only [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hc => h (Set.mem_preimage.mp hc))]

/-- A product of two shifted indicators is the indicator of the intersection
of the two preimages. -/
lemma blockIndic_iterate_mul (A : Set ℝ) (j j' : ℕ) (x : ℝ) :
    blockIndic A (gaussMap^[j] x) * blockIndic A (gaussMap^[j'] x) =
      (((gaussMap^[j]) ⁻¹' A) ∩ ((gaussMap^[j']) ⁻¹' A)).indicator (1 : ℝ → ℝ) x := by
  rw [blockIndic_iterate, blockIndic_iterate]
  show ((gaussMap^[j]) ⁻¹' A).indicator (1 : ℝ → ℝ) x *
      ((gaussMap^[j']) ⁻¹' A).indicator (1 : ℝ → ℝ) x = _
  rw [← Pi.mul_apply, ← Set.inter_indicator_one]

/-- Each shifted indicator is integrable (bounded, finite measure). -/
lemma integrable_blockIndic_iterate (A : Set ℝ) (hA : MeasurableSet A) (k : ℕ) :
    Integrable (fun x => blockIndic A (gaussMap^[k] x)) gaussMeasure := by
  have hmeas : MeasurableSet ((gaussMap^[k]) ⁻¹' A) :=
    (measurable_gaussMap.iterate k) hA
  have heq : (fun x => blockIndic A (gaussMap^[k] x))
      = ((gaussMap^[k]) ⁻¹' A).indicator (1 : ℝ → ℝ) := by
    funext x; rw [blockIndic_iterate]; rfl
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator hmeas

/-- The product of two shifted indicators is integrable. -/
lemma integrable_blockIndic_iterate_mul (A : Set ℝ) (hA : MeasurableSet A)
    (j j' : ℕ) :
    Integrable (fun x =>
      blockIndic A (gaussMap^[j] x) * blockIndic A (gaussMap^[j'] x)) gaussMeasure := by
  have hmeas : MeasurableSet ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' A) :=
    ((measurable_gaussMap.iterate j) hA).inter ((measurable_gaussMap.iterate j') hA)
  have heq : (fun x =>
      blockIndic A (gaussMap^[j] x) * blockIndic A (gaussMap^[j'] x))
      = ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' A).indicator (1 : ℝ → ℝ) := by
    funext x; exact blockIndic_iterate_mul A j j' x
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator hmeas

/-! ## First moment -/

/-- **First moment**: `∫ S_n dγ = n · γ(A)`. -/
theorem integral_blockCount (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
    ∫ x, blockCount A n x ∂gaussMeasure = n * gaussMeasure.real A := by
  have hmp := measurePreserving_gaussMap
  calc ∫ x, blockCount A n x ∂gaussMeasure
      = ∑ k ∈ Finset.range n,
          ∫ x, blockIndic A (gaussMap^[k] x) ∂gaussMeasure := by
        rw [show (fun x => blockCount A n x)
            = fun x => ∑ k ∈ Finset.range n, blockIndic A (gaussMap^[k] x) from
          funext (blockCount_apply A n)]
        exact integral_finsetSum _
          (fun k _ => integrable_blockIndic_iterate A hA k)
    _ = ∑ _k ∈ Finset.range n, gaussMeasure.real A := by
        apply Finset.sum_congr rfl
        intro k _
        have hmeas : MeasurableSet ((gaussMap^[k]) ⁻¹' A) :=
          (measurable_gaussMap.iterate k) hA
        calc ∫ x, blockIndic A (gaussMap^[k] x) ∂gaussMeasure
            = ∫ x, ((gaussMap^[k]) ⁻¹' A).indicator (1 : ℝ → ℝ) x ∂gaussMeasure := by
              apply integral_congr_ae
              filter_upwards with x
              rw [blockIndic_iterate]; rfl
          _ = gaussMeasure.real ((gaussMap^[k]) ⁻¹' A) := integral_indicator_one hmeas
          _ = gaussMeasure.real A :=
              (hmp.iterate k).measureReal_preimage hA.nullMeasurableSet
    _ = n * gaussMeasure.real A := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Pair invariance -/

/-- Splitting an iterate preimage: `T^{-(j+m)}A = T^{-j}(T^{-m}A)`. -/
lemma preimage_iterate_add (A : Set ℝ) (j m : ℕ) :
    (gaussMap^[j + m]) ⁻¹' A = (gaussMap^[j]) ⁻¹' ((gaussMap^[m]) ⁻¹' A) := by
  rw [show gaussMap^[j + m] = gaussMap^[m] ∘ gaussMap^[j] by
        rw [Nat.add_comm]; exact Function.iterate_add gaussMap m j,
    Set.preimage_comp]

/-- **Pair invariance**: `γ(T^{-j}A ∩ T^{-(j+m)}A) = γ(A ∩ T^{-m}A)`.
By `T`-invariance the leading `j` iterates factor out. -/
theorem gaussMeasureReal_pair_shift (A : Set ℝ) (hA : MeasurableSet A) (j m : ℕ) :
    gaussMeasure.real
        ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j + m]) ⁻¹' A) =
      gaussMeasure.real (A ∩ (gaussMap^[m]) ⁻¹' A) := by
  have hmp := measurePreserving_gaussMap
  have hmm : MeasurableSet ((gaussMap^[m]) ⁻¹' A) :=
    (measurable_gaussMap.iterate m) hA
  rw [preimage_iterate_add A j m, ← Set.preimage_inter]
  exact (hmp.iterate j).measureReal_preimage (hA.inter hmm).nullMeasurableSet

/-! ## Second moment -/

/-- **Second moment**: `∫ S_n² dγ = Σ_{j,j' < n} γ(T^{-j}A ∩ T^{-j'}A)`. -/
theorem integral_blockCount_sq (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
    ∫ x, blockCount A n x ^ 2 ∂gaussMeasure =
      ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        gaussMeasure.real ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' A) := by
  have hsq : (fun x => blockCount A n x ^ 2) =
      fun x => ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        blockIndic A (gaussMap^[j] x) * blockIndic A (gaussMap^[j'] x) := by
    funext x
    rw [pow_two, blockCount_apply, Finset.sum_mul_sum]
  rw [hsq,
    integral_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun j' _ => integrable_blockIndic_iterate_mul A hA j j'))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun j' _ => integrable_blockIndic_iterate_mul A hA j j')]
  apply Finset.sum_congr rfl
  intro j' _
  have hmj : MeasurableSet ((gaussMap^[j]) ⁻¹' A) := (measurable_gaussMap.iterate j) hA
  have hmj' : MeasurableSet ((gaussMap^[j']) ⁻¹' A) := (measurable_gaussMap.iterate j') hA
  calc ∫ x, blockIndic A (gaussMap^[j] x) * blockIndic A (gaussMap^[j'] x) ∂gaussMeasure
      = ∫ x, (((gaussMap^[j]) ⁻¹' A) ∩ ((gaussMap^[j']) ⁻¹' A)).indicator
          (1 : ℝ → ℝ) x ∂gaussMeasure := by
        apply integral_congr_ae
        filter_upwards with x
        exact blockIndic_iterate_mul A j j' x
    _ = gaussMeasure.real ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' A) :=
        integral_indicator_one (hmj.inter hmj')

/-! ## Per-pair covariance bound (the γ-mixing consumer) -/

/-- **Per-pair covariance bound**: the cylinder self-correlation at gap `m`
deviates from `γ(I_v)²` by a geometrically-small amount once `m ≥ |v|`, and by
at most `2γ(I_v)` for the overlapping gaps `m < |v|`.  This is where the proven
γ-mixing engine `gaussMeasure_cylinder_mixing` enters; the `< |v|` case is the
crude "overlap" bound the variance sum tolerates. -/
theorem abs_cov_le (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) (m : ℕ) :
    |(gaussMeasure (cfCylinder v ∩ (gaussMap^[m]) ⁻¹' cfCylinder v)).toReal
        - (gaussMeasure (cfCylinder v)).toReal ^ 2|
      ≤ if v.length ≤ m
          then (9 / 10) ^ (m - v.length) * (4 * (volume (cfCylinder v)).toReal)
                * (gaussMeasure (cfCylinder v)).toReal
          else 2 * (gaussMeasure (cfCylinder v)).toReal := by
  by_cases hm : v.length ≤ m
  · rw [if_pos hm]
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_two]
    exact gaussMeasure_cylinder_mixing v hpos g
      (measurableSet_cfCylinder v) (cfCylinder_subset_Ioo v)
  · rw [if_neg hm]
    set X : Set ℝ := cfCylinder v ∩ (gaussMap^[m]) ⁻¹' cfCylinder v with hX
    set μr : ℝ := (gaussMeasure (cfCylinder v)).toReal with hμr
    have hXnn : 0 ≤ (gaussMeasure X).toReal := ENNReal.toReal_nonneg
    have hμnn : 0 ≤ μr := ENNReal.toReal_nonneg
    have hXle : (gaussMeasure X).toReal ≤ μr :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
    have hμ1 : μr ≤ 1 := by
      have h := ENNReal.toReal_mono (measure_ne_top gaussMeasure Set.univ)
        (measure_mono (Set.subset_univ (cfCylinder v)))
      rwa [gaussMeasure_univ, ENNReal.toReal_one] at h
    have hμsq : μr ^ 2 ≤ μr := by nlinarith [hμnn, hμ1]
    rw [abs_le]
    exact ⟨by nlinarith [sq_nonneg μr, hXnn], by nlinarith [hXle, hμsq]⟩

/-! ## Variance bound and Chebyshev (W4 targets — decomposition in progress)

The two theorems below are the W4 headline shapes.  They are lap-authored
*proposals* for judge ratification (like `CFGammaMixing.lean`), not
judge-frozen statements.  Both reduce to the fully-proved fundamentals above;
what remains is pure `Finset` arithmetic (no more analysis, no more measure
theory), so the route is de-risked. -/

/-- **Variance bound** `Var(S_n) ≤ K(v)·n·γ(I_v)` with `K(v) = 4|v| + 80`.

Proof route (all ingredients above are proved):
* `integral_blockCount_sq` writes `∫ S_n² dγ = Σ_{j,j'} γᵣ(T^{-j}I_v ∩ T^{-j'}I_v)`.
* `(n·μ)² = Σ_{j,j'} μ²`, so `Var = Σ_{j,j'} (γᵣ(T^{-j}I_v ∩ T^{-j'}I_v) − μ²)`.
* For each `(j,j')` set `d = |j−j'|`; `gaussMeasureReal_pair_shift` collapses
  the pair correlation to gap `d`, and `abs_cov_le` bounds `|·| ≤ B(d)` where
  `B(d) = (9/10)^{d−|v|}·4·|I_v|·μ` for `d ≥ |v|` and `2μ` for `d < |v|`.
* The double sum `Σ_{j,j'<n} B(|j−j'|) ≤ 2n·Σ_{d<n} B(d)` (each gap value is
  hit ≤ twice per row), and `Σ_{d} B(d) ≤ (2|v| + 40)·μ` (geometric tail sums
  to `10`, using `|I_v| ≤ 1`).  So `Var ≤ 2n·(2|v|+40)·μ = (4|v|+80)·n·μ`.

The remaining work is the `Finset` gap-counting reindex + the geometric-tail
sum — no measure theory. -/
theorem variance_blockCount_le (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) (n : ℕ) :
    |∫ x, blockCount (cfCylinder v) n x ^ 2 ∂gaussMeasure -
        (n * (gaussMeasure (cfCylinder v)).toReal) ^ 2| ≤
      (4 * v.length + 80) * n * (gaussMeasure (cfCylinder v)).toReal := by
  sorry

/-- **Chebyshev block-frequency bound** — the per-stage input to the
Becher–Yuhjtman refinement (`< ¼` bad measure for `n` large): for `δ > 0`,

`γ{ x : |S_n(x)/n − γ(I_v)| ≥ δ } ≤ (4|v|+80)·γ(I_v)/(δ²·n)`.

From `variance_blockCount_le` via Markov applied to `(S_n − n·γ(I_v))²`
(mathlib `meas_ge_le_variance_div_sq`, or `mul_meas_ge_le_lintegral₀`).  Given
`γ(I_v) → 0` and `δ` fixed, the RHS `→ 0` as `n → ∞`; choosing `n` with
`(4|v|+80)·γ(I_v)/(δ²n) < ¼` is exactly the stage bound the construction uses. -/
theorem chebyshev_blockCount (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMeasure {x | δ ≤ |blockCount (cfCylinder v) n x / n -
        (gaussMeasure (cfCylinder v)).toReal|}).toReal ≤
      (4 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n) := by
  sorry

end NormalNumbers
