import NormalNumbers.CFAeNormal
import NormalNumbers.CFLogTail

/-!
# a.e. Khinchin-typicality (toward the image-Khinchin B6 stretch)

Goal: `∀ᵐ x ∂gaussMeasure, KhinchinTypical x` — the geometric mean of the CF
digits tends to Khinchin's constant `K₀` for a.e. `x`.  This is the missing
co-null set that, intersected with the affine-family co-null sets
(`CFAffineFamily.lean`), upgrades the B6 witness to be Khinchin-typical too.

## The reduction (why this is tractable without a general ergodic theorem)

By `khinchinTypical_iff_log_tendsto`, `KhinchinTypical x` is equivalent to the
log-average `(1/n) Σ_{i<n} log(a_i(x)) → log K₀`.  Split each digit-log at a
FIXED cutoff `K`:

  `Σ_{i<n} log a_i  =  Σ_{a=1}^{K} log a · #{i<n : a_i = a}  +  logBirkhoffSum K n x`,

where the tail `logBirkhoffSum K n x = Σ_{i<n} log(a_i)·1[a_i > K]` is exactly
the log-tail Birkhoff sum of `CFLogTail`.  Dividing by `n`:

* **bounded part** `Σ_{a≤K} log a · (blockCount (cfCylinder [a]) n x / n)` →
  `Σ_{a≤K} log a · γ([a]) = Σ_{k<K} logTailG k` a.e., a FINITE sum of the
  singleton-digit frequency limits `ae_orbit_freq [a]` (already proved).
* **tail part** `logBirkhoffSum K n x / n → ∫ logTailFn K dγ` a.e. — the one new
  analytic input (`ae_tail_average_tendsto`).

Their limits ADD to `(Σ_{k<K} logTailG k) + ∫ logTailFn K dγ = log K₀` EXACTLY
(`integral_logTailFn_eq_of_hasSum` with `HasSum logTailG (log K₀)`), for ANY
fixed `K` — no `K → ∞` limiting needed.  So the whole crux collapses onto the
single tail-average lemma.

## Status
`ae_digitCount_tendsto` (bounded-part leaf) is PROVED here.  The tail-average
lemma `ae_tail_average_tendsto` is the disclosed crux: it is the L²→a.e.
Borel–Cantelli argument (mirroring `ae_orbit_freq`) applied to `logBirkhoffSum`,
using a variance bound for the log-tail Birkhoff sum (to be built from the Gauss
mixing engine — `logTailFn K = Σ_{a>K} log a · 1_{cfCylinder [a]}` decomposes it
into the same two-point correlations behind `variance_blockCount_le`), plus the
MONOTONE gap-squeeze available because `logTailFn K ≥ 0`.  See `PENDING_WORK.md`.
-/

namespace NormalNumbers

open MeasureTheory Filter Set

/-- **Bounded-part leaf.**  For each digit value `a ≥ 1`, the frequency of digit
`a` among the first `n` CF digits converges a.e. to `γ([a])`.  Direct
specialization of `ae_orbit_freq` to the singleton word `v = [a]`. -/
theorem ae_digitCount_tendsto (a : ℕ) (ha : 1 ≤ a) :
    ∀ᵐ x ∂gaussMeasure,
      Tendsto (fun n => blockCount (cfCylinder [a]) n x / (n : ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder [a])).toReal) := by
  refine ae_orbit_freq [a] (by simp) ?_
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact ha

/-! ## Foundation bricks for the tail variance bound

`logTailFn K = Σ_{a>K} log a · 1_{cfCylinder [a]}`, so the second moment of
`logBirkhoffSum K n` expands into TWO-different-cylinder correlations
`γ(T^{-j}[a] ∩ T^{-j'}[b])`.  These two bricks generalize the single-cylinder
`gaussMeasureReal_pair_shift` / `abs_cov_pair_le` (`CFBlockFreq.lean`) to two
distinct cylinders, which is exactly what the log-tail variance sum needs. -/

/-- **Two-set pair invariance**: `γ(T^{-j}A ∩ T^{-(j+m)}B) = γ(A ∩ T^{-m}B)`.
Generalizes `gaussMeasureReal_pair_shift` to two distinct measurable sets. -/
theorem gaussMeasureReal_pair_shift₂ (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (j m : ℕ) :
    gaussMeasure.real ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j + m]) ⁻¹' B) =
      gaussMeasure.real (A ∩ (gaussMap^[m]) ⁻¹' B) := by
  have hmp := measurePreserving_gaussMap
  have hmm : MeasurableSet ((gaussMap^[m]) ⁻¹' B) := (measurable_gaussMap.iterate m) hB
  rw [preimage_iterate_add B j m, ← Set.preimage_inter]
  exact (hmp.iterate j).measureReal_preimage (hA.inter hmm).nullMeasurableSet

/-- **Aligned two-cylinder mixing** at gap `m ≥ 1`: for singleton digit words
`[a]`, `[b]`, the correlation `γ([a] ∩ T^{-m}[b])` deviates from `γ([a])·γ([b])`
by at most `(9/10)^{m-1}·4·|[b]|·γ([a])`.  Direct application of
`gaussMeasure_cylinder_mixing` with `v = [a]` and the arbitrary-set slot
`A = cfCylinder [b]`. -/
theorem abs_cov_two_cyl_le (a b : ℕ) (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    |(gaussMeasure (cfCylinder [a] ∩ (gaussMap^[m]) ⁻¹' cfCylinder [b])).toReal -
        (gaussMeasure (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal| ≤
      ((9 : ℝ) / 10) ^ (m - 1) * (4 * (volume (cfCylinder [b])).toReal) *
        (gaussMeasure (cfCylinder [a])).toReal := by
  have hposa : ∀ x ∈ [a], 1 ≤ x := by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ha
  obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hlen : ([a] : List ℕ).length + g = 1 + g := by simp
  have hmix := gaussMeasure_cylinder_mixing [a] hposa g
    (measurableSet_cfCylinder [b]) (cfCylinder_subset_Ioo [b])
  rw [hlen] at hmix
  simpa using hmix

/-- **Variance-constant summability.**  `Σ_a log(a+1)·|cfCylinder [a+1]|` converges
— the `volume`-weighted analogue of `summable_gaussKuzmin_log` (`Σ_a
log(a+1)·γ([a+1])`), by the `volume ≤ 2·log2·γ` domination on `(0,1)`.  This is the
finite constant `Σ_b log b · |[b]|` that appears in the log-tail correlation bound
`|Cov(f, f∘Tᵐ)| ≤ (9/10)^{m∸1}·4·(Σ log·γ)·(Σ log·vol)`. -/
lemma summable_logMul_vol_cfCylinder :
    Summable (fun a : ℕ => Real.log ((a : ℝ) + 1) * (volume (cfCylinder [a + 1])).toReal) := by
  have hlog2 : (0 : ℝ) ≤ 2 * Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
  refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_)
    (summable_gaussKuzmin_log.mul_left (2 * Real.log 2))
  · have h1 : (0 : ℝ) ≤ Real.log ((a : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) a; linarith)
    positivity
  · -- `log(a+1)·vol([a+1]) ≤ 2log2 · (γ([a+1])·log(a+1)) = 2log2·logTailG a`
    have hlogn : (0 : ℝ) ≤ Real.log ((a : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) a; linarith)
    have hdom : (volume (cfCylinder [a + 1])).toReal
        ≤ 2 * Real.log 2 * (gaussMeasure (cfCylinder [a + 1])).toReal := by
      have hle := volume_le_ofReal_mul_gaussMeasure (cfCylinder [a + 1])
        (measurableSet_cfCylinder _) (cfCylinder_subset_Ioo _)
      have := ENNReal.toReal_mono (by
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hle
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog2] at this
    calc Real.log ((a : ℝ) + 1) * (volume (cfCylinder [a + 1])).toReal
        ≤ Real.log ((a : ℝ) + 1) * (2 * Real.log 2 * (gaussMeasure (cfCylinder [a + 1])).toReal) :=
          mul_le_mul_of_nonneg_left hdom hlogn
      _ = 2 * Real.log 2 * logTailG a := by unfold logTailG; ring

/-- Elementary: `(log x)² ≤ 16·√x` for `x ≥ 1` (write `x = s⁴` with `s = √√x`,
then `log x = 4 log s ≤ 4s` and square). -/
lemma sq_log_le_sixteen_sqrt {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set s : ℝ := Real.sqrt (Real.sqrt x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx0)
  have hssq : s ^ 2 = Real.sqrt x := by rw [hs, sq, Real.mul_self_sqrt (Real.sqrt_nonneg x)]
  have hs4 : s ^ 4 = x := by
    have : (s ^ 2) ^ 2 = x := by
      rw [hssq, sq, Real.mul_self_sqrt hx0.le]
    rwa [← pow_mul] at this
  have hlogx : Real.log x = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]; push_cast; ring
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have hlogxnn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hbound : Real.log x ≤ 4 * s := by rw [hlogx]; nlinarith [hlogs]
  calc (Real.log x) ^ 2 ≤ (4 * s) ^ 2 := by
        apply sq_le_sq'
        · nlinarith [hlogxnn, hs0]
        · exact hbound
    _ = 16 * Real.sqrt x := by rw [mul_pow]; rw [← hssq]; ring

/-- **Second-moment summability.**  `Σ_a (log(a+1))²·γ([a+1])` converges — needed
for `∫ g² dγ < ∞` where `g(x) = log(cfDigit x 0)` is the full log-digit function
(the `g`-direct route to a.e. Khinchin; `g ≥ 0`, `∫ g = log K₀`).  Comparison to
`1/(k+1)^{3/2}` via `(log)² ≤ 16√·` and the Gauss–Kuzmin digit-cylinder mass
`γ([k+1]) = logb 2(1 + 1/((k+1)(k+3))) ≤ (1/log2)/((k+1)(k+3))`. -/
lemma summable_sqLog_gaussMeasure_cfCylinder :
    Summable (fun a : ℕ => (Real.log ((a : ℝ) + 1)) ^ 2 * (gaussMeasure (cfCylinder [a + 1])).toReal) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmaj : Summable (fun k : ℕ => (16 / Real.log 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))) := by
    have hp : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
      have h := (Real.summable_one_div_nat_rpow (p := (3 : ℝ) / 2)).2 (by norm_num)
      have h1 := (summable_nat_add_iff 1).2 h
      refine h1.congr (fun k => by push_cast; ring)
    exact hp.mul_left _
  refine Summable.of_nonneg_of_le (fun a => by positivity) (fun k => ?_) hmaj
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  -- digit-cylinder mass closed form + `log(1+t) ≤ t`
  have hmass : (gaussMeasure (cfCylinder [k + 1])).toReal
      ≤ (1 / Real.log 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) := by
    rw [gaussMeasure_digit_cylinder (k + 1) (by omega),
      ENNReal.toReal_ofReal (Real.logb_nonneg (by norm_num) (le_add_of_nonneg_right (by positivity)))]
    rw [Real.logb, div_eq_inv_mul, ← one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    push_cast
    rw [show ((k : ℝ) + 1 + 2) = (k : ℝ) + 3 from by ring]
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) by positivity)
    linarith
  have hsqlog : (Real.log ((k : ℝ) + 1)) ^ 2 ≤ 16 * Real.sqrt ((k : ℝ) + 1) :=
    sq_log_le_sixteen_sqrt hk1
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
  have hmassnn : (0 : ℝ) ≤ (gaussMeasure (cfCylinder [k + 1])).toReal := ENNReal.toReal_nonneg
  -- combine: (log)²·γ ≤ 16√(k+1)·(1/log2)/((k+1)(k+3))
  calc (Real.log ((k : ℝ) + 1)) ^ 2 * (gaussMeasure (cfCylinder [k + 1])).toReal
      ≤ (16 * Real.sqrt ((k : ℝ) + 1)) *
          ((1 / Real.log 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))) := by
        apply mul_le_mul hsqlog hmass hmassnn (by positivity)
    _ ≤ (16 / Real.log 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
        rw [Real.sqrt_eq_rpow]
        rw [show (16 : ℝ) * ((k : ℝ) + 1) ^ ((1 : ℝ) / 2) *
              ((1 / Real.log 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))))
            = (16 / Real.log 2) * (((k : ℝ) + 1) ^ ((1 : ℝ) / 2) / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
            by ring]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hpow : ((k : ℝ) + 1) ^ ((1 : ℝ) / 2) * ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)
            = ((k : ℝ) + 1) ^ 2 := by
          rw [← Real.rpow_add (by linarith), show (1 : ℝ) / 2 + 3 / 2 = 2 by norm_num, Real.rpow_two]
        rw [hpow]; nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-! ## Two-cylinder second-moment machinery (the log-tail variance decorrelation core)

`logBirkhoffSum K n = Σ_{a>K} log a · blockCount [a] n` (a.e.), so its second moment
expands into CROSS block-count products `∫ blockCount [a] n · blockCount [b] n`.  These two
bricks generalize the single-cylinder `integral_blockCount_sq` / `abs_cov_pair_le`
(`CFBlockFreq.lean`) to two DISTINCT cylinders, which is exactly what the log-tail variance
needs. -/

/-- Product of two shifted indicators of DISTINCT sets is the indicator of the
intersection of the two preimages (cross version of `blockIndic_iterate_mul`). -/
lemma blockIndic_iterate_mul₂ (A B : Set ℝ) (j j' : ℕ) (x : ℝ) :
    blockIndic A (gaussMap^[j] x) * blockIndic B (gaussMap^[j'] x) =
      (((gaussMap^[j]) ⁻¹' A) ∩ ((gaussMap^[j']) ⁻¹' B)).indicator (1 : ℝ → ℝ) x := by
  rw [blockIndic_iterate, blockIndic_iterate]
  show ((gaussMap^[j]) ⁻¹' A).indicator (1 : ℝ → ℝ) x *
      ((gaussMap^[j']) ⁻¹' B).indicator (1 : ℝ → ℝ) x = _
  rw [← Pi.mul_apply, ← Set.inter_indicator_one]

/-- The product of two shifted indicators of distinct sets is integrable. -/
lemma integrable_blockIndic_iterate_mul₂ (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (j j' : ℕ) :
    Integrable (fun x =>
      blockIndic A (gaussMap^[j] x) * blockIndic B (gaussMap^[j'] x)) gaussMeasure := by
  have hmeas : MeasurableSet ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' B) :=
    ((measurable_gaussMap.iterate j) hA).inter ((measurable_gaussMap.iterate j') hB)
  have heq : (fun x =>
      blockIndic A (gaussMap^[j] x) * blockIndic B (gaussMap^[j'] x))
      = ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' B).indicator (1 : ℝ → ℝ) := by
    funext x; exact blockIndic_iterate_mul₂ A B j j' x
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator hmeas

/-- **Cross second-moment identity** (brick 1): the product of two block counts
integrates to the double sum of two-preimage intersection masses.  Generalizes
`integral_blockCount_sq` (the `A = B` case). -/
theorem integral_blockCount_cross (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) :
    ∫ x, blockCount A n x * blockCount B n x ∂gaussMeasure =
      ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        gaussMeasure.real ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' B) := by
  have hprod : (fun x => blockCount A n x * blockCount B n x) =
      fun x => ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        blockIndic A (gaussMap^[j] x) * blockIndic B (gaussMap^[j'] x) := by
    funext x
    rw [blockCount_apply, blockCount_apply, Finset.sum_mul_sum]
  rw [hprod,
    integral_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun j' _ => integrable_blockIndic_iterate_mul₂ A B hA hB j j'))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun j' _ => integrable_blockIndic_iterate_mul₂ A B hA hB j j')]
  apply Finset.sum_congr rfl
  intro j' _
  have hmj : MeasurableSet ((gaussMap^[j]) ⁻¹' A) := (measurable_gaussMap.iterate j) hA
  have hmj' : MeasurableSet ((gaussMap^[j']) ⁻¹' B) := (measurable_gaussMap.iterate j') hB
  calc ∫ x, blockIndic A (gaussMap^[j] x) * blockIndic B (gaussMap^[j'] x) ∂gaussMeasure
      = ∫ x, (((gaussMap^[j]) ⁻¹' A) ∩ ((gaussMap^[j']) ⁻¹' B)).indicator
          (1 : ℝ → ℝ) x ∂gaussMeasure := by
        apply integral_congr_ae
        filter_upwards with x
        exact blockIndic_iterate_mul₂ A B j j' x
    _ = gaussMeasure.real ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j']) ⁻¹' B) :=
        integral_indicator_one (hmj.inter hmj')

/-- **General two-cylinder covariance bound** (brick 2): for DISTINCT time indices
`i ≠ j`, the correlation `γ(T⁻ⁱ[a] ∩ T⁻ʲ[b])` deviates from `γ[a]·γ[b]` by at most
`4·(9/10)^{dist(i,j)∸1}·(|[b]|·γ[a] + |[a]|·γ[b])`.  Symmetric in `(a,i)↔(b,j)` so it
covers both `i<j` and `i>j`.  From `gaussMeasureReal_pair_shift₂` (reduce to gap
`m = dist`) + `abs_cov_two_cyl_le` (aligned gap `m ≥ 1`). -/
theorem abs_cov_two_cyl_pair_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) {i j : ℕ}
    (hij : i ≠ j) :
    |gaussMeasure.real ((gaussMap^[i]) ⁻¹' cfCylinder [a] ∩ (gaussMap^[j]) ⁻¹' cfCylinder [b]) -
        (gaussMeasure (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal| ≤
      4 * ((9 : ℝ) / 10) ^ (Nat.dist i j - 1) *
        ((volume (cfCylinder [b])).toReal * (gaussMeasure (cfCylinder [a])).toReal +
         (volume (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal) := by
  have hb0 : 0 ≤ (volume (cfCylinder [b])).toReal := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ (volume (cfCylinder [a])).toReal := ENNReal.toReal_nonneg
  have hga0 : 0 ≤ (gaussMeasure (cfCylinder [a])).toReal := ENNReal.toReal_nonneg
  have hgb0 : 0 ≤ (gaussMeasure (cfCylinder [b])).toReal := ENNReal.toReal_nonneg
  have hpow : 0 ≤ ((9 : ℝ) / 10) ^ (Nat.dist i j - 1) := by positivity
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- i < j, gap m = j - i
    rw [Nat.dist_eq_sub_of_le hlt.le]
    have hps := gaussMeasureReal_pair_shift₂ (cfCylinder [a]) (cfCylinder [b])
      (measurableSet_cfCylinder [a]) (measurableSet_cfCylinder [b]) i (j - i)
    rw [Nat.add_sub_cancel' hlt.le] at hps
    rw [hps]
    have hcov := abs_cov_two_cyl_le a b ha (j - i) (by omega)
    rw [MeasureTheory.measureReal_def]
    calc |(gaussMeasure (cfCylinder [a] ∩ (gaussMap^[j - i]) ⁻¹' cfCylinder [b])).toReal -
            (gaussMeasure (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal|
        ≤ ((9 : ℝ) / 10) ^ (j - i - 1) * (4 * (volume (cfCylinder [b])).toReal) *
            (gaussMeasure (cfCylinder [a])).toReal := hcov
      _ ≤ 4 * ((9 : ℝ) / 10) ^ (j - i - 1) *
            ((volume (cfCylinder [b])).toReal * (gaussMeasure (cfCylinder [a])).toReal +
             (volume (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal) := by
          have hpow' : 0 ≤ ((9 : ℝ) / 10) ^ (j - i - 1) := by positivity
          nlinarith [mul_nonneg ha0 hgb0, mul_nonneg hpow' (mul_nonneg ha0 hgb0)]
  · -- i > j, gap m = i - j
    rw [Nat.dist_eq_sub_of_le_right hgt.le, Set.inter_comm]
    have hps := gaussMeasureReal_pair_shift₂ (cfCylinder [b]) (cfCylinder [a])
      (measurableSet_cfCylinder [b]) (measurableSet_cfCylinder [a]) j (i - j)
    rw [Nat.add_sub_cancel' hgt.le] at hps
    rw [hps]
    have hcov := abs_cov_two_cyl_le b a hb (i - j) (by omega)
    rw [MeasureTheory.measureReal_def, mul_comm (gaussMeasure (cfCylinder [a])).toReal]
    calc |(gaussMeasure (cfCylinder [b] ∩ (gaussMap^[i - j]) ⁻¹' cfCylinder [a])).toReal -
            (gaussMeasure (cfCylinder [b])).toReal * (gaussMeasure (cfCylinder [a])).toReal|
        ≤ ((9 : ℝ) / 10) ^ (i - j - 1) * (4 * (volume (cfCylinder [a])).toReal) *
            (gaussMeasure (cfCylinder [b])).toReal := hcov
      _ ≤ 4 * ((9 : ℝ) / 10) ^ (i - j - 1) *
            ((volume (cfCylinder [b])).toReal * (gaussMeasure (cfCylinder [a])).toReal +
             (volume (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal) := by
          have hpow' : 0 ≤ ((9 : ℝ) / 10) ^ (i - j - 1) := by positivity
          nlinarith [mul_nonneg hb0 hga0, mul_nonneg hpow' (mul_nonneg hb0 hga0)]

/-! ## The g-direct bridges (reduce `ae_khinchinTypical` to the `K=0` tail average)

`g(x) = log(cfDigit x 0)` is `logTailFn 0` a.e. (the first digit is `≥ 1` a.e.),
its integral is `log K₀`, and `logBirkhoffSum 0 n x = Σ_{i<n} log(a_i)` a.e.  So
`ae_khinchinTypical` follows from `ae_tail_average_tendsto 0` alone. -/

/-- `∫ logTailFn 0 dγ = log K₀` (the `K = 0` tail integral is the full
Gauss–Kuzmin log-sum). -/
lemma integral_logTailFn_zero :
    ∫ x, logTailFn 0 x ∂gaussMeasure = Real.log khinchinK₀ := by
  have h := integral_logTailFn_eq_of_hasSum 0 gaussKuzmin_logsum_hasSum
  simpa using h

/-- a.e., `logTailFn 0 x = log (cfDigit x 0)` — the first CF digit is `≥ 1`. -/
lemma logTailFn_zero_ae_eq :
    ∀ᵐ x ∂gaussMeasure, logTailFn 0 x = Real.log ((cfDigit x 0 : ℕ) : ℝ) := by
  filter_upwards [ae_irrational, ae_mem_Ioo] with x hirr hx
  have h1 : 1 ≤ cfDigit x 0 := one_le_cfDigit x hirr hx 0
  unfold logTailFn
  rw [if_pos (by omega)]

/-- **The tail-average crux (disclosed).**  For a fixed cutoff `K`, the
normalized log-tail Birkhoff sum converges a.e. to the tail integral.  Route:
L²→a.e. Borel–Cantelli (as in `ae_orbit_freq`) via a variance bound for
`logBirkhoffSum K` from Gauss mixing, plus the monotone gap-squeeze
(`logBirkhoffSum K n x` is nondecreasing in `n`, since `logTailFn K ≥ 0`). -/
theorem ae_tail_average_tendsto (K : ℕ) :
    ∀ᵐ x ∂gaussMeasure,
      Tendsto (fun n => logBirkhoffSum K n x / (n : ℝ)) atTop
        (nhds (∫ y, logTailFn K y ∂gaussMeasure)) := by
  sorry

/-- **a.e. Khinchin-typicality** (modulo the disclosed tail-average crux at `K=0`).
`ae_tail_average_tendsto 0` gives the log-average of the CF digits `→ log K₀` a.e.;
`khinchinTypical_iff_log_tendsto` turns that into `KhinchinTypical`.  All the glue
(digit identity, `∫ logTailFn 0 = log K₀`, first-digit positivity) is discharged. -/
theorem ae_khinchinTypical : ∀ᵐ x ∂gaussMeasure, KhinchinTypical x := by
  filter_upwards [ae_irrational, ae_mem_Ioo, ae_tail_average_tendsto 0] with x hirr hx htend
  rw [integral_logTailFn_zero] at htend
  have hpos : ∀ i, 1 ≤ cfDigit x i := fun i => one_le_cfDigit x hirr hx i
  have hbirk : ∀ n, logBirkhoffSum 0 n x = ∑ i ∈ Finset.range n, Real.log ((cfDigit x i : ℕ) : ℝ) := by
    intro n
    rw [logBirkhoffSum_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hd : cfDigit (gaussMap^[k] x) 0 = cfDigit x k := by
      unfold cfDigit; rw [Function.iterate_zero_apply]
    unfold logTailFn
    rw [hd, if_pos (by have := hpos k; omega)]
  rw [khinchinTypical_iff_log_tendsto x hpos]
  refine htend.congr (fun n => ?_)
  rw [hbirk n, finset_sum_range_eq_list_sum]
  ring

end NormalNumbers
