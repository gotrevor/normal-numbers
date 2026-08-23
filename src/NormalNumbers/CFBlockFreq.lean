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

/-- `S_n` is measurable (finite sum of indicators of measurable preimages). -/
lemma measurable_blockCount (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
    Measurable (blockCount A n) := by
  have heq : blockCount A n = fun x =>
      ∑ k ∈ Finset.range n, ((gaussMap^[k]) ⁻¹' A).indicator (1 : ℝ → ℝ) x := by
    funext x
    rw [blockCount_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [blockIndic_iterate]; rfl
  rw [heq]
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.indicator ((measurable_gaussMap.iterate k) hA)

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

/-! ## Finset arithmetic for the variance sum -/

/-- `|I_v| ≤ 1` — the cylinder sits in `(0,1)`. -/
lemma volumeReal_cfCylinder_le_one (v : List ℕ) :
    (volume (cfCylinder v)).toReal ≤ 1 := by
  have h1 : volume (cfCylinder v) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
    measure_mono (cfCylinder_subset_Ioo v)
  have h2 : volume (Set.Ioo (0 : ℝ) 1) = 1 := by rw [Real.volume_Ioo]; norm_num
  rw [h2] at h1
  calc (volume (cfCylinder v)).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top h1
    _ = 1 := ENNReal.toReal_one

/-- **Per-pair covariance bound at gap `|j − j'|`**, with a single uniform
geometric dominating factor: the two-case `abs_cov_le` is majorised by
`4·γ(I_v)·(9/10)^{|j−j'| ∸ |v|}` (using `|I_v| ≤ 1` and truncated `∸`, so the
crude `2γ(I_v)` overlap case is absorbed at exponent `0`). -/
theorem abs_cov_pair_le (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) (j j' : ℕ) :
    |(gaussMeasure ((gaussMap^[j]) ⁻¹' cfCylinder v ∩
          (gaussMap^[j']) ⁻¹' cfCylinder v)).toReal -
        (gaussMeasure (cfCylinder v)).toReal ^ 2| ≤
      4 * (gaussMeasure (cfCylinder v)).toReal *
        ((9 : ℝ) / 10) ^ (Nat.dist j j' - v.length) := by
  have hμnn : 0 ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
  have hvol := volumeReal_cfCylinder_le_one v
  -- the gap-form bound, uniform over `m`
  have key : ∀ m : ℕ,
      |(gaussMeasure (cfCylinder v ∩ (gaussMap^[m]) ⁻¹' cfCylinder v)).toReal -
          (gaussMeasure (cfCylinder v)).toReal ^ 2| ≤
        4 * (gaussMeasure (cfCylinder v)).toReal *
          ((9 : ℝ) / 10) ^ (m - v.length) := by
    intro m
    refine (abs_cov_le v hpos m).trans ?_
    by_cases hm : v.length ≤ m
    · rw [if_pos hm]
      have hp : (0 : ℝ) ≤ ((9 : ℝ) / 10) ^ (m - v.length) := by positivity
      calc ((9 : ℝ) / 10) ^ (m - v.length) *
              (4 * (volume (cfCylinder v)).toReal) * (gaussMeasure (cfCylinder v)).toReal
          ≤ ((9 : ℝ) / 10) ^ (m - v.length) * (4 * 1) *
              (gaussMeasure (cfCylinder v)).toReal := by gcongr
        _ = 4 * (gaussMeasure (cfCylinder v)).toReal *
              ((9 : ℝ) / 10) ^ (m - v.length) := by ring
    · rw [if_neg hm]
      have hz : m - v.length = 0 := by omega
      rw [hz, pow_zero, mul_one]
      linarith [hμnn]
  rcases le_total j j' with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    have hps := gaussMeasureReal_pair_shift (cfCylinder v) (measurableSet_cfCylinder v) j (j' - j)
    rw [Nat.add_sub_cancel' hle] at hps
    rw [show (gaussMeasure ((gaussMap^[j]) ⁻¹' cfCylinder v ∩
        (gaussMap^[j']) ⁻¹' cfCylinder v)).toReal =
        (gaussMeasure (cfCylinder v ∩ (gaussMap^[j' - j]) ⁻¹' cfCylinder v)).toReal from hps]
    exact key (j' - j)
  · rw [Nat.dist_eq_sub_of_le_right hle, Set.inter_comm]
    have hps := gaussMeasureReal_pair_shift (cfCylinder v) (measurableSet_cfCylinder v) j' (j - j')
    rw [Nat.add_sub_cancel' hle] at hps
    rw [show (gaussMeasure ((gaussMap^[j']) ⁻¹' cfCylinder v ∩
        (gaussMap^[j]) ⁻¹' cfCylinder v)).toReal =
        (gaussMeasure (cfCylinder v ∩ (gaussMap^[j - j']) ⁻¹' cfCylinder v)).toReal from hps]
    exact key (j - j')

/-- Truncated geometric partial sum: `Σ_{d<n} (9/10)^{d ∸ L} ≤ L + 10`
(`L` head terms are `1`; the tail is geometric with sum `≤ 10`). -/
lemma geom_trunc_sum_le (L n : ℕ) :
    ∑ d ∈ Finset.range n, ((9 : ℝ) / 10) ^ (d - L) ≤ (L : ℝ) + 10 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (· < L)]
  apply add_le_add
  · calc ∑ d ∈ (Finset.range n).filter (· < L), ((9 : ℝ) / 10) ^ (d - L)
        = ∑ _d ∈ (Finset.range n).filter (· < L), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [Nat.sub_eq_zero_of_le hd.2.le, pow_zero]
      _ = (((Finset.range n).filter (· < L)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (L : ℝ) := by
          have hc : ((Finset.range n).filter (· < L)).card ≤ L := by
            calc ((Finset.range n).filter (· < L)).card
                ≤ (Finset.range L).card :=
                  Finset.card_le_card (by
                    intro d hd
                    rw [Finset.mem_filter] at hd
                    rw [Finset.mem_range]; exact hd.2)
              _ = L := Finset.card_range L
          exact_mod_cast hc
  · have hgeo : ∑ k ∈ Finset.range n, ((9 : ℝ) / 10) ^ k ≤ 10 := by
      have hsum : Summable (fun k => ((9 : ℝ) / 10) ^ k) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      calc ∑ k ∈ Finset.range n, ((9 : ℝ) / 10) ^ k
          ≤ ∑' k, ((9 : ℝ) / 10) ^ k := hsum.sum_le_tsum _ (fun k _ => by positivity)
        _ = (1 - 9 / 10)⁻¹ := tsum_geometric_of_lt_one (by norm_num) (by norm_num)
        _ = 10 := by norm_num
    have hinj : ∀ a ∈ (Finset.range n).filter (¬ · < L),
        ∀ b ∈ (Finset.range n).filter (¬ · < L), a - L = b - L → a = b := by
      intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb; omega
    calc ∑ d ∈ (Finset.range n).filter (¬ · < L), ((9 : ℝ) / 10) ^ (d - L)
        = ∑ k ∈ ((Finset.range n).filter (¬ · < L)).image (fun d => d - L),
            ((9 : ℝ) / 10) ^ k := (Finset.sum_image hinj).symm
      _ ≤ ∑ k ∈ Finset.range n, ((9 : ℝ) / 10) ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_image] at hk
            obtain ⟨d, hd, rfl⟩ := hk
            simp only [Finset.mem_filter, Finset.mem_range] at hd
            rw [Finset.mem_range]; omega
          · intro k _ _; positivity
      _ ≤ 10 := hgeo

/-- Sum of a nonnegative function of the gap `|j − j'|`, over `j'` in a range
containing `j`, is at most twice the sum over the range (each gap value is hit
at most twice — once on each side of `j`). -/
lemma sum_range_dist_le (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) (n j : ℕ) (hj : j < n) :
    ∑ j' ∈ Finset.range n, g (Nat.dist j j') ≤ 2 * ∑ d ∈ Finset.range n, g d := by
  classical
  rw [two_mul, ← Finset.sum_filter_add_sum_filter_not (Finset.range n) (· ≤ j)
    (fun j' => g (Nat.dist j j'))]
  apply add_le_add
  · have hinj : ∀ a ∈ (Finset.range n).filter (· ≤ j),
        ∀ b ∈ (Finset.range n).filter (· ≤ j), j - a = j - b → a = b := by
      intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb; omega
    calc ∑ j' ∈ (Finset.range n).filter (· ≤ j), g (Nat.dist j j')
        = ∑ j' ∈ (Finset.range n).filter (· ≤ j), g (j - j') := by
          apply Finset.sum_congr rfl
          intro j' hj'
          rw [Finset.mem_filter] at hj'
          rw [Nat.dist_eq_sub_of_le_right hj'.2]
      _ = ∑ d ∈ ((Finset.range n).filter (· ≤ j)).image (fun j' => j - j'), g d :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ d ∈ Finset.range n, g d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            rw [Finset.mem_image] at hd
            obtain ⟨j', hj', rfl⟩ := hd
            simp only [Finset.mem_filter, Finset.mem_range] at hj'
            rw [Finset.mem_range]; omega
          · intro d _ _; exact hg d
  · have hinj : ∀ a ∈ (Finset.range n).filter (¬ · ≤ j),
        ∀ b ∈ (Finset.range n).filter (¬ · ≤ j), a - j = b - j → a = b := by
      intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb; omega
    calc ∑ j' ∈ (Finset.range n).filter (¬ · ≤ j), g (Nat.dist j j')
        = ∑ j' ∈ (Finset.range n).filter (¬ · ≤ j), g (j' - j) := by
          apply Finset.sum_congr rfl
          intro j' hj'
          rw [Finset.mem_filter] at hj'
          rw [Nat.dist_eq_sub_of_le (by omega : j ≤ j')]
      _ = ∑ d ∈ ((Finset.range n).filter (¬ · ≤ j)).image (fun j' => j' - j), g d :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ d ∈ Finset.range n, g d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            rw [Finset.mem_image] at hd
            obtain ⟨j', hj', rfl⟩ := hd
            simp only [Finset.mem_filter, Finset.mem_range] at hj'
            rw [Finset.mem_range]; omega
          · intro d _ _; exact hg d

/-! ## Variance bound and Chebyshev (W4 targets)

Lap-authored *proposals* for judge ratification (like `CFGammaMixing.lean`),
not judge-frozen statements. -/

/-- **Variance bound** `Var(S_n) ≤ (8|v| + 80)·n·γ(I_v)`.

`integral_blockCount_sq` + `abs_cov_pair_le` (per-pair, via `pair_shift`) reduce
the variance to `Σ_{j,j'} 4γ(I_v)(9/10)^{|j−j'|∸|v|}`; `sum_range_dist_le` folds
each row to `2·Σ_d (9/10)^{d∸|v|}` and `geom_trunc_sum_le` bounds that by
`2(|v|+10)`, giving `4γ(I_v)·n·2(|v|+10) = (8|v|+80)·n·γ(I_v)`. -/
theorem variance_blockCount_le (v : List ℕ) (hpos : ∀ a ∈ v, 1 ≤ a) (n : ℕ) :
    |∫ x, blockCount (cfCylinder v) n x ^ 2 ∂gaussMeasure -
        (n * (gaussMeasure (cfCylinder v)).toReal) ^ 2| ≤
      (8 * v.length + 80) * n * (gaussMeasure (cfCylinder v)).toReal := by
  have hμnn : 0 ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
  have hVmeas : MeasurableSet (cfCylinder v) := measurableSet_cfCylinder v
  -- `(n·μ)²` as a double sum of `μ²`
  have h2 : ((n : ℝ) * (gaussMeasure (cfCylinder v)).toReal) ^ 2 =
      ∑ _j ∈ Finset.range n, ∑ _j' ∈ Finset.range n,
        (gaussMeasure (cfCylinder v)).toReal ^ 2 := by
    rw [show (n : ℝ) * (gaussMeasure (cfCylinder v)).toReal =
        ∑ _j ∈ Finset.range n, (gaussMeasure (cfCylinder v)).toReal by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul], pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro j' _; rw [pow_two]
  rw [integral_blockCount_sq (cfCylinder v) hVmeas n, h2]
  calc |∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder v ∩ (gaussMap^[j']) ⁻¹' cfCylinder v) -
        ∑ _j ∈ Finset.range n, ∑ _j' ∈ Finset.range n,
          (gaussMeasure (cfCylinder v)).toReal ^ 2|
      = |∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          (gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder v ∩ (gaussMap^[j']) ⁻¹' cfCylinder v) -
            (gaussMeasure (cfCylinder v)).toReal ^ 2)| := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl; intro j _
        rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          |gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder v ∩ (gaussMap^[j']) ⁻¹' cfCylinder v) -
            (gaussMeasure (cfCylinder v)).toReal ^ 2| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum; intro j _
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          4 * (gaussMeasure (cfCylinder v)).toReal *
            ((9 : ℝ) / 10) ^ (Nat.dist j j' - v.length) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro j' _
        exact abs_cov_pair_le v hpos j j'
    _ ≤ ∑ _j ∈ Finset.range n, (8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal := by
        apply Finset.sum_le_sum; intro j hj
        rw [Finset.mem_range] at hj
        rw [← Finset.mul_sum]
        have hinner : ∑ j' ∈ Finset.range n, ((9 : ℝ) / 10) ^ (Nat.dist j j' - v.length)
            ≤ 2 * ((v.length : ℝ) + 10) := by
          calc ∑ j' ∈ Finset.range n, ((9 : ℝ) / 10) ^ (Nat.dist j j' - v.length)
              ≤ 2 * ∑ d ∈ Finset.range n, ((9 : ℝ) / 10) ^ (d - v.length) :=
                sum_range_dist_le (fun m => ((9 : ℝ) / 10) ^ (m - v.length))
                  (fun d => by positivity) n j hj
            _ ≤ 2 * ((v.length : ℝ) + 10) := by
                have := geom_trunc_sum_le v.length n; linarith
        calc 4 * (gaussMeasure (cfCylinder v)).toReal *
              ∑ j' ∈ Finset.range n, ((9 : ℝ) / 10) ^ (Nat.dist j j' - v.length)
            ≤ 4 * (gaussMeasure (cfCylinder v)).toReal * (2 * ((v.length : ℝ) + 10)) :=
              mul_le_mul_of_nonneg_left hinner (by positivity)
          _ = (8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal := by push_cast; ring
    _ = (8 * v.length + 80) * n * (gaussMeasure (cfCylinder v)).toReal := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

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
      (8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n) := by
  have hVmeas : MeasurableSet (cfCylinder v) := measurableSet_cfCylinder v
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSmeas : Measurable (blockCount (cfCylinder v) n) :=
    measurable_blockCount (cfCylinder v) hVmeas n
  -- `0 ≤ S_n ≤ n`, hence `MemLp 2`
  have hind0 : ∀ y, 0 ≤ blockIndic (cfCylinder v) y := fun y =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have hind1 : ∀ y, blockIndic (cfCylinder v) y ≤ 1 := fun y => by
    unfold blockIndic
    by_cases h : y ∈ cfCylinder v
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hSbound : ∀ x, ‖blockCount (cfCylinder v) n x‖ ≤ n := by
    intro x
    rw [Real.norm_eq_abs, blockCount_apply,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => hind0 _)]
    calc ∑ k ∈ Finset.range n, blockIndic (cfCylinder v) (gaussMap^[k] x)
        ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => hind1 _
      _ = n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hMem : MemLp (blockCount (cfCylinder v) n) 2 gaussMeasure :=
    MemLp.of_bound hSmeas.aestronglyMeasurable n (Filter.Eventually.of_forall hSbound)
  -- first moment
  have hEX : ∫ x, blockCount (cfCylinder v) n x ∂gaussMeasure =
      n * (gaussMeasure (cfCylinder v)).toReal := by
    rw [integral_blockCount (cfCylinder v) hVmeas n, measureReal_def]
  -- variance bound from `variance_blockCount_le`
  have hVar : ProbabilityTheory.variance (blockCount (cfCylinder v) n) gaussMeasure ≤
      (8 * v.length + 80) * n * (gaussMeasure (cfCylinder v)).toReal := by
    rw [ProbabilityTheory.variance_eq_sub hMem]
    simp only [Pi.pow_apply]
    rw [hEX]
    exact le_trans (le_abs_self _) (variance_blockCount_le v hpos n)
  -- the deviation set, rescaled by `n`
  have hset : {x | δ ≤ |blockCount (cfCylinder v) n x / n -
        (gaussMeasure (cfCylinder v)).toReal|}
      = {x | δ * n ≤ |blockCount (cfCylinder v) n x -
          ∫ y, blockCount (cfCylinder v) n y ∂gaussMeasure|} := by
    ext x
    simp only [Set.mem_setOf_eq, hEX]
    rw [show blockCount (cfCylinder v) n x / n - (gaussMeasure (cfCylinder v)).toReal
        = (blockCount (cfCylinder v) n x - n * (gaussMeasure (cfCylinder v)).toReal) / n by
          field_simp,
      abs_div, abs_of_pos hnR, le_div_iff₀ hnR]
  -- Chebyshev, then arithmetic
  have hδn : 0 < δ * n := mul_pos hδ hnR
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := gaussMeasure) hMem hδn
  calc (gaussMeasure {x | δ ≤ |blockCount (cfCylinder v) n x / n -
          (gaussMeasure (cfCylinder v)).toReal|}).toReal
      ≤ (ENNReal.ofReal (ProbabilityTheory.variance (blockCount (cfCylinder v) n)
          gaussMeasure / (δ * n) ^ 2)).toReal := by
        rw [hset]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = ProbabilityTheory.variance (blockCount (cfCylinder v) n) gaussMeasure /
          (δ * n) ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _)
          (by positivity))
    _ ≤ ((8 * v.length + 80) * n * (gaussMeasure (cfCylinder v)).toReal) / (δ * n) ^ 2 := by
        gcongr
    _ = (8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n) := by
        field_simp

/-! ## Conditioned-on-brick bounds

The Becher–Yuhjtman refinement works *inside the current brick* `I_w`: at each
stage it needs the part of `I_w` whose continuation (after the `|w|` digits of
the brick) has bad `v`-block frequency to have measure `< ¼·γ(I_w)`.  The `g=0`
γ-mixing bound plus the density window `|A| ≤ 2·log 2·γ(A)` turn the
unconditioned Chebyshev bound into exactly this, at the cost of a factor
`1 + 8·log 2 < 7`. -/

/-- Real form of the density window: `|A| ≤ 2·log 2·γ(A)` for `A ⊆ (0,1)`. -/
lemma volume_toReal_le_gaussMeasure (A : Set ℝ) (hA : MeasurableSet A)
    (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    (volume A).toReal ≤ 2 * Real.log 2 * (gaussMeasure A).toReal := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h' := ENNReal.toReal_mono (measure_ne_top gaussMeasure A)
    (volume_le_gaussMeasure A hA hA1)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
  calc (volume A).toReal
      = 2 * Real.log 2 * ((2 * Real.log 2)⁻¹ * (volume A).toReal) := by
        field_simp
    _ ≤ 2 * Real.log 2 * (gaussMeasure A).toReal :=
        mul_le_mul_of_nonneg_left h' (by positivity)

/-- **Brick-conditioned measure bound**: for any brick word `w` and measurable
`A ⊆ (0,1)`, `γ(I_w ∩ T^{-|w|}A) ≤ 7·γ(A)·γ(I_w)`.  This is `g = 0` γ-mixing
plus the density window (`1 + 8·log 2 < 7`). -/
theorem gaussMeasure_brick_inter_le (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a)
    {A : Set ℝ} (hA : MeasurableSet A) (hA1 : A ⊆ Set.Ioo (0 : ℝ) 1) :
    (gaussMeasure (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹' A)).toReal ≤
      7 * (gaussMeasure A).toReal * (gaussMeasure (cfCylinder w)).toReal := by
  have hmix := gaussMeasure_cylinder_mixing w hposw 0 hA hA1
  rw [Nat.add_zero, pow_zero, one_mul] at hmix
  have hvol := volume_toReal_le_gaussMeasure A hA hA1
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hγnn : (0 : ℝ) ≤ (gaussMeasure A).toReal := ENNReal.toReal_nonneg
  have hwnn : (0 : ℝ) ≤ (gaussMeasure (cfCylinder w)).toReal := ENNReal.toReal_nonneg
  have hVnn : (0 : ℝ) ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have h1 := (abs_le.mp hmix).2
  nlinarith [mul_le_mul_of_nonneg_right hvol hwnn,
    mul_nonneg hγnn hwnn]

/-- **Brick-conditioned Chebyshev** — the per-stage Becher–Yuhjtman input:
inside any brick `I_w`, the part whose continuation has bad `v`-block
frequency at time `n` has γ-measure at most
`7·(8|v|+80)·γ(I_v)/(δ²·n)·γ(I_w)`.  With `v` fixed, `δ` fixed and `n` large
this is `< ¼·γ(I_w)`, the stage bound of the construction. -/
theorem chebyshev_blockCount_brick (w v : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a)
    (hpos : ∀ a ∈ v, 1 ≤ a) (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMeasure (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹'
        {x ∈ Set.Ioo (0 : ℝ) 1 | δ ≤ |blockCount (cfCylinder v) n x / n -
          (gaussMeasure (cfCylinder v)).toReal|})).toReal ≤
      7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal /
        (δ ^ 2 * n)) * (gaussMeasure (cfCylinder w)).toReal := by
  have hSmeas : Measurable (blockCount (cfCylinder v) n) :=
    measurable_blockCount (cfCylinder v) (measurableSet_cfCylinder v) n
  have hBadmeas : MeasurableSet {x ∈ Set.Ioo (0 : ℝ) 1 |
      δ ≤ |blockCount (cfCylinder v) n x / n -
        (gaussMeasure (cfCylinder v)).toReal|} :=
    measurableSet_Ioo.inter (measurableSet_le measurable_const
      (((hSmeas.div_const _).sub_const _).abs))
  have hBadsub : {x ∈ Set.Ioo (0 : ℝ) 1 |
      δ ≤ |blockCount (cfCylinder v) n x / n -
        (gaussMeasure (cfCylinder v)).toReal|} ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.sep_subset _ _
  have hγBad : (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
      δ ≤ |blockCount (cfCylinder v) n x / n -
        (gaussMeasure (cfCylinder v)).toReal|}).toReal ≤
      (8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal / (δ ^ 2 * n) := by
    refine le_trans ?_ (chebyshev_blockCount v hpos n hn hδ)
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun x hx => hx.2)
  calc (gaussMeasure (cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹'
          {x ∈ Set.Ioo (0 : ℝ) 1 | δ ≤ |blockCount (cfCylinder v) n x / n -
            (gaussMeasure (cfCylinder v)).toReal|})).toReal
      ≤ 7 * (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
          δ ≤ |blockCount (cfCylinder v) n x / n -
            (gaussMeasure (cfCylinder v)).toReal|}).toReal *
          (gaussMeasure (cfCylinder w)).toReal :=
        gaussMeasure_brick_inter_le w hposw hBadmeas hBadsub
    _ ≤ 7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal /
          (δ ^ 2 * n)) * (gaussMeasure (cfCylinder w)).toReal := by
        gcongr

end NormalNumbers
