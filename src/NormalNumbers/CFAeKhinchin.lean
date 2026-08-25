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

/-! ## The truncated log-tail Birkhoff sum and its variance (Approach B)

`S_n^M := Σ_{a<M} log(K+1+a)·blockCount [K+1+a] n` is a FINITE linear combination of
block counts (= `Σ_{i<n} f_M∘gaussMapⁱ` for `f_M = Σ_{a<M} logTailTerm K a`).  Its
second moment is a finite double sum of two-cylinder correlations, giving a variance
bound UNIFORM in `M`; the MCT limit `M → ∞` then transfers it to `logBirkhoffSum K n`. -/

/-- Truncated log-tail Birkhoff sum. -/
noncomputable def logBirkhoffTrunc (K M n : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.range M, Real.log ((K : ℝ) + 1 + a) * blockCount (cfCylinder [K + 1 + a]) n x

/-- Truncated log-tail mean: `Σ_{a<M} log(K+1+a)·γ([K+1+a])`.  Equals `∫ logBirkhoffTrunc / n`. -/
noncomputable def logTruncMean (K M : ℕ) : ℝ :=
  ∑ a ∈ Finset.range M, Real.log ((K : ℝ) + 1 + a) * (gaussMeasure (cfCylinder [K + 1 + a])).toReal

/-- The product of two block counts is integrable (finite sum of bounded indicator products). -/
lemma integrable_blockCount_mul (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (n : ℕ) : Integrable (fun x => blockCount A n x * blockCount B n x) gaussMeasure := by
  have heq : (fun x => blockCount A n x * blockCount B n x)
      = fun x => ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          blockIndic A (gaussMap^[j] x) * blockIndic B (gaussMap^[j'] x) := by
    funext x; rw [blockCount_apply, blockCount_apply, Finset.sum_mul_sum]
  rw [heq]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun j' _ =>
    integrable_blockIndic_iterate_mul₂ A B hA hB j j'))

/-- **Sub-lemma (a): truncated second-moment expansion.**  `∫(S_n^M)²` is the finite
double sum over `(a,b)` of `log·log` times the cross second moment (brick 1). -/
lemma integral_logBirkhoffTrunc_sq (K M n : ℕ) :
    ∫ x, (logBirkhoffTrunc K M n x) ^ 2 ∂gaussMeasure =
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
          ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
            gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
              (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) := by
  have hsq : (fun x => (logBirkhoffTrunc K M n x) ^ 2) =
      fun x => ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
          (blockCount (cfCylinder [K + 1 + a]) n x * blockCount (cfCylinder [K + 1 + b]) n x) := by
    funext x
    rw [logBirkhoffTrunc, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [hsq,
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
      ((integrable_blockCount_mul (cfCylinder [K + 1 + a]) (cfCylinder [K + 1 + b])
        (measurableSet_cfCylinder _) (measurableSet_cfCylinder _) n)).const_mul
        (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b))))]
  apply Finset.sum_congr rfl; intro a _
  rw [integral_finsetSum _ (fun b _ =>
      ((integrable_blockCount_mul (cfCylinder [K + 1 + a]) (cfCylinder [K + 1 + b])
        (measurableSet_cfCylinder _) (measurableSet_cfCylinder _) n)).const_mul
        (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)))]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_const_mul,
    integral_blockCount_cross _ _ (measurableSet_cfCylinder _) (measurableSet_cfCylinder _) n]

/-- **Sub-lemma (b): the squared truncated mean as a matching double sum.** -/
lemma sq_logTruncMean_eq (K M n : ℕ) :
    ((n : ℝ) * logTruncMean K M) ^ 2 =
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
          ∑ _j ∈ Finset.range n, ∑ _j' ∈ Finset.range n,
            (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + b])).toReal := by
  have hexp : logTruncMean K M ^ 2 =
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        (Real.log ((K : ℝ) + 1 + a) * (gaussMeasure (cfCylinder [K + 1 + a])).toReal) *
        (Real.log ((K : ℝ) + 1 + b) * (gaussMeasure (cfCylinder [K + 1 + b])).toReal) := by
    rw [pow_two, logTruncMean, Finset.sum_mul_sum]
  rw [mul_pow, hexp, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-! ### M-independent variance constants (tails of the landed summability bricks) -/

/-- `C₁(K) = Σ_{a} log(K+1+a)·γ([K+1+a])` — equals `∫ logTailFn K`. -/
noncomputable def logTailC1 (K : ℕ) : ℝ :=
  ∑' a : ℕ, Real.log ((K : ℝ) + 1 + a) * (gaussMeasure (cfCylinder [K + 1 + a])).toReal

/-- `C₂(K) = Σ_{a} log(K+1+a)·|[K+1+a]|`. -/
noncomputable def logTailC2 (K : ℕ) : ℝ :=
  ∑' a : ℕ, Real.log ((K : ℝ) + 1 + a) * (volume (cfCylinder [K + 1 + a])).toReal

/-- `C₃(K) = Σ_{a} log(K+1+a)²·γ([K+1+a])`. -/
noncomputable def logTailC3 (K : ℕ) : ℝ :=
  ∑' a : ℕ, (Real.log ((K : ℝ) + 1 + a)) ^ 2 * (gaussMeasure (cfCylinder [K + 1 + a])).toReal

lemma summable_logTailC1 (K : ℕ) :
    Summable (fun a : ℕ => Real.log ((K : ℝ) + 1 + a) * (gaussMeasure (cfCylinder [K + 1 + a])).toReal) := by
  have h := (summable_nat_add_iff K).2 summable_gaussKuzmin_log
  refine h.congr (fun a => ?_)
  unfold logTailG
  have hidx : a + K + 1 = K + 1 + a := by omega
  rw [hidx]; push_cast; ring

lemma summable_logTailC2 (K : ℕ) :
    Summable (fun a : ℕ => Real.log ((K : ℝ) + 1 + a) * (volume (cfCylinder [K + 1 + a])).toReal) := by
  have h := (summable_nat_add_iff K).2 summable_logMul_vol_cfCylinder
  refine h.congr (fun a => ?_)
  have hidx : a + K + 1 = K + 1 + a := by omega
  rw [hidx]; push_cast; ring

lemma summable_logTailC3 (K : ℕ) :
    Summable (fun a : ℕ => (Real.log ((K : ℝ) + 1 + a)) ^ 2 * (gaussMeasure (cfCylinder [K + 1 + a])).toReal) := by
  have h := (summable_nat_add_iff K).2 summable_sqLog_gaussMeasure_cfCylinder
  refine h.congr (fun a => ?_)
  have hidx : a + K + 1 = K + 1 + a := by omega
  rw [hidx]; push_cast; ring

lemma logTailC1_nonneg (K : ℕ) : 0 ≤ logTailC1 K :=
  tsum_nonneg (fun a => mul_nonneg (Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) a; linarith)) ENNReal.toReal_nonneg)

lemma logTailC2_nonneg (K : ℕ) : 0 ≤ logTailC2 K :=
  tsum_nonneg (fun a => mul_nonneg (Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) a; linarith)) ENNReal.toReal_nonneg)

lemma logTailC3_nonneg (K : ℕ) : 0 ≤ logTailC3 K :=
  tsum_nonneg (fun a => mul_nonneg (by positivity) ENNReal.toReal_nonneg)

/-- The overall (M-independent) variance constant `C₃ + C₁² + 176·C₁·C₂`. -/
noncomputable def logVarConst (K : ℕ) : ℝ :=
  logTailC3 K + (logTailC1 K) ^ 2 + 176 * logTailC1 K * logTailC2 K

/-- **Disjointness collapse**: distinct singleton cylinders are disjoint, so the
`(a,b)` double sum of `log·log·γ([a]∩[b])` collapses to the diagonal `Σ log²·γ([a])`. -/
lemma sum_logMul_gaussMeasure_inter (K M : ℕ) :
    ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
      Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
        (gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal =
      ∑ a ∈ Finset.range M, (Real.log ((K : ℝ) + 1 + a)) ^ 2 *
        (gaussMeasure (cfCylinder [K + 1 + a])).toReal := by
  apply Finset.sum_congr rfl; intro a ha
  rw [Finset.sum_eq_single a]
  · rw [Set.inter_self]; ring
  · intro b _ hba
    have hne : ([K + 1 + a] : List ℕ) ≠ [K + 1 + b] := by
      simp only [ne_eq, List.cons.injEq, and_true]; omega
    have hdisj : cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b] = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (cfCylinder_disjoint rfl hne)
    rw [hdisj]; simp
  · intro ha'; exact absurd ha ha'

/-- **Per-pair inner bound** (the covariance fold): for fixed digits `[K+1+a]`, `[K+1+b]`,
the inner `(j,j')` double sum of centered correlations is bounded by `O(n)`.  Diagonal
`j=j'` gives the `γ(A∩B)+γ_aγ_b` term (measure-preserving); off-diagonal folds brick 2
via `sum_range_dist_le` + `geom_trunc_sum_le`. -/
lemma inner_pair_bound (K a b n : ℕ) :
    |∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        (gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
            (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
          (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
            (gaussMeasure (cfCylinder [K + 1 + b])).toReal)|
      ≤ (n : ℝ) * ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
            (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + b])).toReal) +
        88 * (n : ℝ) * ((volume (cfCylinder [K + 1 + b])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + a])).toReal +
            (volume (cfCylinder [K + 1 + a])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + b])).toReal) := by
  have hmp := measurePreserving_gaussMap
  have hmA : MeasurableSet (cfCylinder [K + 1 + a]) := measurableSet_cfCylinder _
  have hmB : MeasurableSet (cfCylinder [K + 1 + b]) := measurableSet_cfCylinder _
  have hγAnn : (0 : ℝ) ≤ (gaussMeasure (cfCylinder [K + 1 + a])).toReal := ENNReal.toReal_nonneg
  have hγBnn : (0 : ℝ) ≤ (gaussMeasure (cfCylinder [K + 1 + b])).toReal := ENNReal.toReal_nonneg
  have hγABnn : (0 : ℝ) ≤ (gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal :=
    ENNReal.toReal_nonneg
  set C : ℝ := (volume (cfCylinder [K + 1 + b])).toReal *
        (gaussMeasure (cfCylinder [K + 1 + a])).toReal +
      (volume (cfCylinder [K + 1 + a])).toReal *
        (gaussMeasure (cfCylinder [K + 1 + b])).toReal with hC
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  -- diagonal correlation is `γ(A∩B)`, independent of `j`
  have hdiag : ∀ j : ℕ, gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
        (gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + b]) =
      (gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal := by
    intro j
    rw [← Set.preimage_inter,
      (hmp.iterate j).measureReal_preimage (hmA.inter hmB).nullMeasurableSet]
    rfl
  -- per-row bound (peel the diagonal `j'=j`, fold the rest via brick 2)
  have hrow : ∀ j ∈ Finset.range n,
      ∑ j' ∈ Finset.range n, |gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
            (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
          (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
            (gaussMeasure (cfCylinder [K + 1 + b])).toReal|
        ≤ ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
              (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                (gaussMeasure (cfCylinder [K + 1 + b])).toReal) +
          ∑ j' ∈ Finset.range n, 4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C := by
    intro j hj
    rw [← Finset.add_sum_erase (Finset.range n) _ hj]
    apply add_le_add
    · rw [hdiag j, abs_le]
      exact ⟨by nlinarith [hγABnn, mul_nonneg hγAnn hγBnn],
             by nlinarith [hγABnn, mul_nonneg hγAnn hγBnn]⟩
    · refine le_trans (Finset.sum_le_sum ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun i _ _ => by positivity))
      intro j' hj'
      have hjj' : j ≠ j' := (Finset.ne_of_mem_erase hj').symm
      have hbrick := abs_cov_two_cyl_pair_le (K + 1 + a) (K + 1 + b) (by omega) (by omega) hjj'
      rw [hC]; exact hbrick
  calc |∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          (gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
              (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
            (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + b])).toReal)|
      ≤ ∑ j ∈ Finset.range n, |∑ j' ∈ Finset.range n,
          (gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
              (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
            (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + b])).toReal)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          |gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
              (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
            (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
              (gaussMeasure (cfCylinder [K + 1 + b])).toReal| :=
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ Finset.range n,
          (((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
              (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                (gaussMeasure (cfCylinder [K + 1 + b])).toReal) +
            ∑ j' ∈ Finset.range n, 4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C) :=
        Finset.sum_le_sum hrow
    _ = (n : ℝ) * ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
              (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                (gaussMeasure (cfCylinder [K + 1 + b])).toReal) +
          ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
            4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
              (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                (gaussMeasure (cfCylinder [K + 1 + b])).toReal) +
          88 * (n : ℝ) * C := by
        have hgeom : ∀ j ∈ Finset.range n,
            ∑ j' ∈ Finset.range n, 4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C ≤ 88 * C := by
          intro j hj
          have hsum : ∑ j' ∈ Finset.range n, ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) ≤ 22 := by
            calc ∑ j' ∈ Finset.range n, ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1)
                ≤ 2 * ∑ d ∈ Finset.range n, ((9 : ℝ) / 10) ^ (d - 1) :=
                  sum_range_dist_le (fun m => ((9 : ℝ) / 10) ^ (m - 1)) (fun d => by positivity)
                    n j (Finset.mem_range.mp hj)
              _ ≤ 2 * (1 + 10) := by have := geom_trunc_sum_le 1 n; push_cast at this; linarith
              _ = 22 := by norm_num
          calc ∑ j' ∈ Finset.range n, 4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C
              = 4 * C * ∑ j' ∈ Finset.range n, ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j' _; ring
            _ ≤ 4 * C * 22 := by apply mul_le_mul_of_nonneg_left hsum (by positivity)
            _ = 88 * C := by ring
        have hfold : ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
              4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C ≤ 88 * (n : ℝ) * C := by
          calc ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
                4 * ((9 : ℝ) / 10) ^ (Nat.dist j j' - 1) * C
              ≤ ∑ _j ∈ Finset.range n, 88 * C := Finset.sum_le_sum hgeom
            _ = 88 * (n : ℝ) * C := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        linarith [hfold]

/-- **Brick 3: uniform-in-M truncated variance bound.**  `|∫(S_n^M)² − (n·μ_M)²| ≤ n·logVarConst K`,
with `logVarConst K = C₃ + C₁² + 176·C₁·C₂` INDEPENDENT of `M` (the finite partial sums are
dominated by the tsum constants).  Assembles sub-lemmas (a),(b), the disjointness collapse, and
`inner_pair_bound`. -/
theorem variance_truncated_le (K M n : ℕ) :
    |∫ x, (logBirkhoffTrunc K M n x) ^ 2 ∂gaussMeasure - ((n : ℝ) * logTruncMean K M) ^ 2|
      ≤ (n : ℝ) * logVarConst K := by
  have hlog : ∀ c : ℕ, 0 ≤ Real.log ((K : ℝ) + 1 + c) := fun c =>
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) K; have := Nat.cast_nonneg (α := ℝ) c; linarith)
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- partial-sum ≤ tsum bounds for the three constants
  have hμle : logTruncMean K M ≤ logTailC1 K := by
    unfold logTruncMean logTailC1
    exact (summable_logTailC1 K).sum_le_tsum (Finset.range M)
      (fun i _ => mul_nonneg (hlog i) ENNReal.toReal_nonneg)
  have hμnn : (0 : ℝ) ≤ logTruncMean K M :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hlog i) ENNReal.toReal_nonneg)
  set νM : ℝ := ∑ a ∈ Finset.range M, Real.log ((K : ℝ) + 1 + a) * (volume (cfCylinder [K + 1 + a])).toReal
    with hνMdef
  have hνle : νM ≤ logTailC2 K := by
    rw [hνMdef]; unfold logTailC2
    exact (summable_logTailC2 K).sum_le_tsum (Finset.range M)
      (fun i _ => mul_nonneg (hlog i) ENNReal.toReal_nonneg)
  have hνnn : (0 : ℝ) ≤ νM := by
    rw [hνMdef]; exact Finset.sum_nonneg (fun i _ => mul_nonneg (hlog i) ENNReal.toReal_nonneg)
  have hC3le : (∑ a ∈ Finset.range M, (Real.log ((K : ℝ) + 1 + a)) ^ 2 *
        (gaussMeasure (cfCylinder [K + 1 + a])).toReal) ≤ logTailC3 K := by
    unfold logTailC3
    exact (summable_logTailC3 K).sum_le_tsum (Finset.range M)
      (fun i _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg)
  -- `Σ_{a,b} L·γ_aγ_b = (logTruncMean)²`
  have hsq2 : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
      (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
        ((gaussMeasure (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)
      = (logTruncMean K M) ^ 2 := by
    rw [logTruncMean, pow_two, Finset.sum_mul_sum]
    exact (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))).symm
  -- `Σ_{a,b} L·vol_bγ_a = μ_M·ν_M`
  have hmn : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
      (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
        ((volume (cfCylinder [K + 1 + b])).toReal * (gaussMeasure (cfCylinder [K + 1 + a])).toReal)
      = (logTruncMean K M) * νM := by
    rw [logTruncMean, hνMdef, Finset.sum_mul_sum]
    exact (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))).symm
  -- `Σ_{a,b} L·vol_aγ_b = ν_M·μ_M`
  have hnm : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
      (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
        ((volume (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)
      = νM * (logTruncMean K M) := by
    rw [logTruncMean, hνMdef, Finset.sum_mul_sum]
    exact (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))).symm
  -- diagonal (γ(A∩B)) contribution collapses
  have hAlpha : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
      (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
        ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
         (gaussMeasure (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)
      ≤ logTailC3 K + (logTailC1 K) ^ 2 := by
    have heq : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
          ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
           (gaussMeasure (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)
        = (∑ a ∈ Finset.range M, (Real.log ((K : ℝ) + 1 + a)) ^ 2 *
              (gaussMeasure (cfCylinder [K + 1 + a])).toReal) + (logTruncMean K M) ^ 2 := by
      rw [← sum_logMul_gaussMeasure_inter K M, ← hsq2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [heq]
    have hsq : (logTruncMean K M) ^ 2 ≤ (logTailC1 K) ^ 2 := by
      have := logTailC1_nonneg K; nlinarith [hμle, hμnn]
    linarith [hC3le, hsq]
  -- off-diagonal (vol) contribution
  have hBeta : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
      (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
        ((volume (cfCylinder [K + 1 + b])).toReal * (gaussMeasure (cfCylinder [K + 1 + a])).toReal +
         (volume (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)
      ≤ 2 * logTailC1 K * logTailC2 K := by
    have heq : ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
          ((volume (cfCylinder [K + 1 + b])).toReal * (gaussMeasure (cfCylinder [K + 1 + a])).toReal +
           (volume (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)
        = (logTruncMean K M) * νM + νM * (logTruncMean K M) := by
      rw [← hmn, ← hnm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [heq]
    have hC1 := logTailC1_nonneg K
    have hC2 := logTailC2_nonneg K
    nlinarith [hμle, hμnn, hνle, hνnn, hC1, hC2]
  -- centered double-sum identity
  have hΔ : ∫ x, (logBirkhoffTrunc K M n x) ^ 2 ∂gaussMeasure - ((n : ℝ) * logTruncMean K M) ^ 2
      = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
          Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
            ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
              (gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
                  (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
                (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                  (gaussMeasure (cfCylinder [K + 1 + b])).toReal) := by
    rw [integral_logBirkhoffTrunc_sq, sq_logTruncMean_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_sub_distrib])
  rw [hΔ]
  calc |∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
          Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
            ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
              (gaussMeasure.real ((gaussMap^[j]) ⁻¹' cfCylinder [K + 1 + a] ∩
                  (gaussMap^[j']) ⁻¹' cfCylinder [K + 1 + b]) -
                (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                  (gaussMeasure (cfCylinder [K + 1 + b])).toReal)|
      ≤ ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
          Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
            ((n : ℝ) * ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
                  (gaussMeasure (cfCylinder [K + 1 + a])).toReal *
                    (gaussMeasure (cfCylinder [K + 1 + b])).toReal) +
              88 * (n : ℝ) * ((volume (cfCylinder [K + 1 + b])).toReal *
                    (gaussMeasure (cfCylinder [K + 1 + a])).toReal +
                  (volume (cfCylinder [K + 1 + a])).toReal *
                    (gaussMeasure (cfCylinder [K + 1 + b])).toReal)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => ?_))
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hlog a) (hlog b))]
        exact mul_le_mul_of_nonneg_left (inner_pair_bound K a b n) (mul_nonneg (hlog a) (hlog b))
    _ = (n : ℝ) * (∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
          (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
            ((gaussMeasure (cfCylinder [K + 1 + a] ∩ cfCylinder [K + 1 + b])).toReal +
             (gaussMeasure (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal))
        + 88 * (n : ℝ) * (∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
          (Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b)) *
            ((volume (cfCylinder [K + 1 + b])).toReal * (gaussMeasure (cfCylinder [K + 1 + a])).toReal +
             (volume (cfCylinder [K + 1 + a])).toReal * (gaussMeasure (cfCylinder [K + 1 + b])).toReal)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun b _ => by ring)
    _ ≤ (n : ℝ) * (logTailC3 K + (logTailC1 K) ^ 2) + 88 * (n : ℝ) * (2 * logTailC1 K * logTailC2 K) := by
        gcongr
    _ = (n : ℝ) * logVarConst K := by unfold logVarConst; ring

/-! ### Brick 4: the M→∞ MCT limit — `variance_logBirkhoffSum_le`

The truncated variance bound `variance_truncated_le` is uniform in the cutoff `M`.
We push it to `M → ∞` by monotone convergence, obtaining the genuine variance
bound for the (unbounded) log-tail Birkhoff sum, with mean `μ = logTailC1 K`. -/

/-- Finite partial sum of the log-tail singleton indicators:
`Σ_{a<M} log(K+1+a)·1_{[K+1+a]}`.  The one-step integrand whose Birkhoff sum is
`logBirkhoffTrunc`, and whose `M→∞` limit is `logTailFn K`. -/
noncomputable def partialTail (K M : ℕ) (y : ℝ) : ℝ :=
  ∑ a ∈ Finset.range M, Real.log ((K : ℝ) + 1 + a) * blockIndic (cfCylinder [K + 1 + a]) y

lemma partialTail_nonneg (K M : ℕ) (y : ℝ) : 0 ≤ partialTail K M y :=
  Finset.sum_nonneg fun a _ => mul_nonneg
    (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) K; have := Nat.cast_nonneg (α := ℝ) a; linarith))
    (Set.indicator_nonneg (fun _ _ => zero_le_one) y)

lemma partialTail_mono (K : ℕ) (y : ℝ) : Monotone (fun M => partialTail K M y) := by
  intro M M' hMM'
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun a ha => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha) hMM')) ?_
  intro a _ _
  exact mul_nonneg
    (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) K; have := Nat.cast_nonneg (α := ℝ) a; linarith))
    (Set.indicator_nonneg (fun _ _ => zero_le_one) y)

/-- For `y ∈ (0,1)` the partial tail is eventually constant (at most one singleton
cylinder contains `y`), hence converges to `logTailFn K y`. -/
lemma partialTail_tendsto (K : ℕ) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun M => partialTail K M y) atTop (nhds (logTailFn K y)) := by
  by_cases hd : K < cfDigit y 0
  · obtain ⟨a₀, ha₀⟩ := Nat.exists_eq_add_of_lt hd
    refine tendsto_atTop_of_eventually_const (i₀ := a₀ + 1) (fun M hM => ?_)
    unfold partialTail logTailFn
    rw [if_pos hd, Finset.sum_eq_single a₀]
    · have hmem : y ∈ cfCylinder [K + 1 + a₀] :=
        mem_cfCylinder_singleton.mpr ⟨hy, by omega⟩
      rw [blockIndic, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      congr 1
      have hval : ((K : ℝ) + 1 + a₀) = (cfDigit y 0 : ℝ) := by rw [ha₀]; push_cast; ring
      rw [hval]
    · intro b _ hb
      have hnotmem : y ∉ cfCylinder [K + 1 + b] := by
        intro hmem
        have h2 := (mem_cfCylinder_singleton.mp hmem).2
        omega
      rw [blockIndic, Set.indicator_of_notMem hnotmem, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.2 (by omega)) hcon
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) (fun M _ => ?_)
    unfold partialTail logTailFn
    rw [if_neg hd]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    have hnotmem : y ∉ cfCylinder [K + 1 + a] := by
      intro hmem
      have h2 := (mem_cfCylinder_singleton.mp hmem).2
      omega
    rw [blockIndic, Set.indicator_of_notMem hnotmem, mul_zero]

/-- `logBirkhoffTrunc` is the Birkhoff sum of `partialTail` over the Gauss orbit. -/
lemma logBirkhoffTrunc_eq_sum_partialTail (K M n : ℕ) (x : ℝ) :
    logBirkhoffTrunc K M n x = ∑ i ∈ Finset.range n, partialTail K M (gaussMap^[i] x) := by
  unfold logBirkhoffTrunc partialTail
  simp_rw [blockCount_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma logBirkhoffTrunc_nonneg (K M n : ℕ) (x : ℝ) : 0 ≤ logBirkhoffTrunc K M n x := by
  rw [logBirkhoffTrunc_eq_sum_partialTail]
  exact Finset.sum_nonneg (fun i _ => partialTail_nonneg K M _)

lemma logBirkhoffTrunc_mono (K n : ℕ) (x : ℝ) :
    Monotone (fun M => logBirkhoffTrunc K M n x) := by
  intro M M' h
  simp_rw [logBirkhoffTrunc_eq_sum_partialTail]
  exact Finset.sum_le_sum (fun i _ => partialTail_mono K _ h)

lemma measurable_logBirkhoffTrunc (K M n : ℕ) : Measurable (logBirkhoffTrunc K M n) := by
  unfold logBirkhoffTrunc
  exact Finset.measurable_sum _ (fun a _ =>
    (measurable_blockCount _ (measurableSet_cfCylinder _) n).const_mul _)

/-- For a full-orbit point, `logBirkhoffTrunc K M n x → logBirkhoffSum K n x`. -/
lemma logBirkhoffTrunc_tendsto (K n : ℕ) {x : ℝ}
    (hx : ∀ i, gaussMap^[i] x ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun M => logBirkhoffTrunc K M n x) atTop (nhds (logBirkhoffSum K n x)) := by
  simp_rw [logBirkhoffTrunc_eq_sum_partialTail]
  rw [logBirkhoffSum_apply]
  exact tendsto_finsetSum _ (fun i _ => partialTail_tendsto K (hx i))

/-- `(logBirkhoffTrunc K M n)²` is integrable (a finite double sum of block-count
products). -/
lemma integrable_logBirkhoffTrunc_sq (K M n : ℕ) :
    Integrable (fun x => (logBirkhoffTrunc K M n x) ^ 2) gaussMeasure := by
  have hsq : (fun x => (logBirkhoffTrunc K M n x) ^ 2) =
      fun x => ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        Real.log ((K : ℝ) + 1 + a) * Real.log ((K : ℝ) + 1 + b) *
          (blockCount (cfCylinder [K + 1 + a]) n x * blockCount (cfCylinder [K + 1 + b]) n x) := by
    funext x
    rw [logBirkhoffTrunc, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [hsq]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    ((integrable_blockCount_mul (cfCylinder [K + 1 + a]) (cfCylinder [K + 1 + b])
      (measurableSet_cfCylinder _) (measurableSet_cfCylinder _) n)).const_mul _))

/-- The truncated mean converges to the full log-tail integral constant. -/
lemma logTruncMean_tendsto (K : ℕ) :
    Tendsto (fun M => logTruncMean K M) atTop (nhds (logTailC1 K)) :=
  (summable_logTailC1 K).hasSum.tendsto_sum_nat

/-- **`logTailC1 K = ∫ logTailFn K dγ`** — the variance constant `μ` is the
genuine mean of the (unbounded) one-step log-tail. -/
lemma logTailC1_eq_integral (K : ℕ) :
    logTailC1 K = ∫ x, logTailFn K x ∂gaussMeasure := by
  rw [integral_logTailFn_eq_of_hasSum K summable_gaussKuzmin_log.hasSum]
  have hsplit : (∑' n, logTailG n) - ∑ k ∈ Finset.range K, logTailG k
      = ∑' a : ℕ, logTailG (a + K) := by
    have h := summable_gaussKuzmin_log.sum_add_tsum_nat_add K
    linarith [h]
  rw [hsplit, logTailC1]
  refine tsum_congr (fun a => ?_)
  unfold logTailG
  have h1 : a + K + 1 = K + 1 + a := by omega
  have h2 : ((a : ℝ) + K) + 1 = (K : ℝ) + 1 + a := by ring
  rw [h1]
  push_cast
  rw [h2]
  ring

/-- Everywhere-monotone truncated squares — the `M→∞` monotone family. -/
private lemma monotone_logBirkhoffTrunc_sq (K n : ℕ) (x : ℝ) :
    Monotone (fun M => (logBirkhoffTrunc K M n x) ^ 2) := by
  intro M M' h
  have h1 := logBirkhoffTrunc_mono K n x h
  have h0 := logBirkhoffTrunc_nonneg K M n x
  nlinarith [h0, h1]

/-- a.e. every Gauss orbit point stays in `(0,1)`. -/
private lemma ae_orbit_mem_Ioo :
    ∀ᵐ x ∂gaussMeasure, ∀ i, gaussMap^[i] x ∈ Set.Ioo (0 : ℝ) 1 := by
  filter_upwards [ae_irrational, ae_mem_Ioo] with x hirr hx
  exact fun i => (irrational_orbit x hirr hx i).2

/-- Uniform (in `M`) upper bound on the truncated second moment. -/
private lemma integral_logBirkhoffTrunc_sq_le (K n M : ℕ) :
    ∫ x, (logBirkhoffTrunc K M n x) ^ 2 ∂gaussMeasure
      ≤ ((n : ℝ) * logTailC1 K) ^ 2 + (n : ℝ) * logVarConst K := by
  have hlog : ∀ c : ℕ, 0 ≤ Real.log ((K : ℝ) + 1 + c) := fun c =>
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) K; have := Nat.cast_nonneg (α := ℝ) c; linarith)
  have hv := (abs_le.mp (variance_truncated_le K M n)).2
  have hμle : logTruncMean K M ≤ logTailC1 K := by
    unfold logTruncMean logTailC1
    exact (summable_logTailC1 K).sum_le_tsum (Finset.range M)
      (fun i _ => mul_nonneg (hlog i) ENNReal.toReal_nonneg)
  have hμnn : (0 : ℝ) ≤ logTruncMean K M := by
    unfold logTruncMean
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hlog i) ENNReal.toReal_nonneg)
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n : ℝ) * logTruncMean K M) ^ 2 ≤ ((n : ℝ) * logTailC1 K) ^ 2 := by
    have hle : (n : ℝ) * logTruncMean K M ≤ (n : ℝ) * logTailC1 K :=
      mul_le_mul_of_nonneg_left hμle hnn
    have hge : (0 : ℝ) ≤ (n : ℝ) * logTruncMean K M := mul_nonneg hnn hμnn
    nlinarith [hle, hge]
  linarith [hv, hsq]

/-- **`(logBirkhoffSum K n)²` is integrable** — the monotone `M→∞` limit of the
truncated squares, whose integrals are uniformly bounded by `variance_truncated_le`,
so its `lintegral` is finite (`lintegral_iSup`). -/
lemma integrable_logBirkhoffSum_sq (K n : ℕ) :
    Integrable (fun x => (logBirkhoffSum K n x) ^ 2) gaussMeasure := by
  have hmonoSq := monotone_logBirkhoffTrunc_sq K n
  have hgmono : Monotone (fun M => fun x => ENNReal.ofReal ((logBirkhoffTrunc K M n x) ^ 2)) :=
    fun M M' h x => ENNReal.ofReal_le_ofReal (hmonoSq x h)
  have hgmeas : ∀ M, Measurable (fun x => ENNReal.ofReal ((logBirkhoffTrunc K M n x) ^ 2)) :=
    fun M => ((measurable_logBirkhoffTrunc K M n).pow_const 2).ennreal_ofReal
  have hsup : ∀ᵐ x ∂gaussMeasure,
      (⨆ M, ENNReal.ofReal ((logBirkhoffTrunc K M n x) ^ 2))
        = ENNReal.ofReal ((logBirkhoffSum K n x) ^ 2) := by
    filter_upwards [ae_orbit_mem_Ioo] with x hx
    have htend : Tendsto (fun M => ENNReal.ofReal ((logBirkhoffTrunc K M n x) ^ 2)) atTop
        (nhds (ENNReal.ofReal ((logBirkhoffSum K n x) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((logBirkhoffTrunc_tendsto K n hx).pow 2)
    have hmono' : Monotone (fun M => ENNReal.ofReal ((logBirkhoffTrunc K M n x) ^ 2)) :=
      fun M M' h => ENNReal.ofReal_le_ofReal (hmonoSq x h)
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono') htend
  have hlint : ∫⁻ x, ENNReal.ofReal ((logBirkhoffSum K n x) ^ 2) ∂gaussMeasure
      ≤ ENNReal.ofReal (((n : ℝ) * logTailC1 K) ^ 2 + (n : ℝ) * logVarConst K) := by
    rw [← lintegral_congr_ae hsup, lintegral_iSup hgmeas hgmono]
    refine iSup_le (fun M => ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_logBirkhoffTrunc_sq K M n)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (integral_logBirkhoffTrunc_sq_le K n M)
  have hne : ∫⁻ x, ENNReal.ofReal ((logBirkhoffSum K n x) ^ 2) ∂gaussMeasure ≠ (⊤ : ENNReal) :=
    ne_of_lt (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_logBirkhoffSum K n).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp hne

/-- **Brick 4 — the genuine variance bound.**  `|∫(S_n)² − (n·μ)²| ≤ n·logVarConst K`
with `μ = logTailC1 K = ∫ logTailFn K`, for the unbounded log-tail Birkhoff sum
`S_n = logBirkhoffSum K n`.  Proof: MCT (`M → ∞`) on `variance_truncated_le`. -/
theorem variance_logBirkhoffSum_le (K n : ℕ) :
    |∫ x, (logBirkhoffSum K n x) ^ 2 ∂gaussMeasure - ((n : ℝ) * logTailC1 K) ^ 2|
      ≤ (n : ℝ) * logVarConst K := by
  -- MCT: the truncated second moments converge to the full second moment
  have hMCT : Tendsto (fun M => ∫ x, (logBirkhoffTrunc K M n x) ^ 2 ∂gaussMeasure) atTop
      (nhds (∫ x, (logBirkhoffSum K n x) ^ 2 ∂gaussMeasure)) := by
    refine integral_tendsto_of_tendsto_of_monotone
      (fun M => integrable_logBirkhoffTrunc_sq K M n) (integrable_logBirkhoffSum_sq K n)
      (Filter.Eventually.of_forall (fun x => monotone_logBirkhoffTrunc_sq K n x)) ?_
    filter_upwards [ae_orbit_mem_Ioo] with x hx
    exact (logBirkhoffTrunc_tendsto K n hx).pow 2
  -- truncated means → μ
  have hmeanTend : Tendsto (fun M => ((n : ℝ) * logTruncMean K M) ^ 2) atTop
      (nhds (((n : ℝ) * logTailC1 K) ^ 2)) :=
    (tendsto_const_nhds.mul (logTruncMean_tendsto K)).pow 2
  -- pass the uniform bound through the limit
  have hdiffTend : Tendsto
      (fun M => |∫ x, (logBirkhoffTrunc K M n x) ^ 2 ∂gaussMeasure
        - ((n : ℝ) * logTruncMean K M) ^ 2|) atTop
      (nhds (|∫ x, (logBirkhoffSum K n x) ^ 2 ∂gaussMeasure - ((n : ℝ) * logTailC1 K) ^ 2|)) :=
    (hMCT.sub hmeanTend).abs
  exact le_of_tendsto hdiffTend
    (Filter.Eventually.of_forall (fun M => variance_truncated_le K M n))

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

/-- **Chebyshev for the log-tail Birkhoff sum.**  `γ{ |S_n/n − μ| ≥ δ } ≤
logVarConst K / (δ²·n)`, `μ = logTailC1 K`.  Markov on `(S_n − nμ)²` via the
genuine variance bound `variance_logBirkhoffSum_le`. -/
theorem chebyshev_logBirkhoffSum (K n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussMeasure {x | δ ≤ |logBirkhoffSum K n x / n - logTailC1 K|}).toReal ≤
      logVarConst K / (δ ^ 2 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSmeas : Measurable (logBirkhoffSum K n) := measurable_logBirkhoffSum K n
  have hMem : MemLp (logBirkhoffSum K n) 2 gaussMeasure :=
    (memLp_two_iff_integrable_sq hSmeas.aestronglyMeasurable).2 (integrable_logBirkhoffSum_sq K n)
  have hEX : ∫ x, logBirkhoffSum K n x ∂gaussMeasure = n * logTailC1 K := by
    rw [integral_logBirkhoffSum K n, logTailC1_eq_integral]
  have hVar : ProbabilityTheory.variance (logBirkhoffSum K n) gaussMeasure ≤ n * logVarConst K := by
    rw [ProbabilityTheory.variance_eq_sub hMem]
    simp only [Pi.pow_apply]
    rw [hEX]
    exact le_trans (le_abs_self _) (variance_logBirkhoffSum_le K n)
  have hset : {x | δ ≤ |logBirkhoffSum K n x / n - logTailC1 K|}
      = {x | δ * n ≤ |logBirkhoffSum K n x - ∫ y, logBirkhoffSum K n y ∂gaussMeasure|} := by
    ext x
    simp only [Set.mem_setOf_eq, hEX]
    rw [show logBirkhoffSum K n x / n - logTailC1 K
        = (logBirkhoffSum K n x - n * logTailC1 K) / n by field_simp,
      abs_div, abs_of_pos hnR, le_div_iff₀ hnR]
  have hδn : 0 < δ * n := mul_pos hδ hnR
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := gaussMeasure) hMem hδn
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  calc (gaussMeasure {x | δ ≤ |logBirkhoffSum K n x / n - logTailC1 K|}).toReal
      ≤ (ENNReal.ofReal (ProbabilityTheory.variance (logBirkhoffSum K n)
          gaussMeasure / (δ * n) ^ 2)).toReal := by
        rw [hset]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = ProbabilityTheory.variance (logBirkhoffSum K n) gaussMeasure / (δ * n) ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (by positivity))
    _ ≤ ((n : ℝ) * logVarConst K) / (δ * n) ^ 2 := by gcongr
    _ = logVarConst K / (δ ^ 2 * n) := by field_simp

/-- **The tail-average crux.**  For a fixed cutoff `K`, the normalized log-tail
Birkhoff sum converges a.e. to the tail integral.  Route: L²→a.e. Borel–Cantelli
(as in `ae_orbit_freq`) via `chebyshev_logBirkhoffSum` along `p = (k+1)²`, plus
the monotone gap-squeeze (`logBirkhoffSum K n x` is nondecreasing in `n`). -/
theorem ae_tail_average_tendsto (K : ℕ) :
    ∀ᵐ x ∂gaussMeasure,
      Tendsto (fun n => logBirkhoffSum K n x / (n : ℝ)) atTop
        (nhds (∫ y, logTailFn K y ∂gaussMeasure)) := by
  rw [← logTailC1_eq_integral]
  set μ := logTailC1 K with hμdef
  -- bad set family (`p = (k+1)²`, `δ = 1/(m+1)`)
  set E : ℕ → ℕ → Set ℝ := fun m k =>
    {x | (1 : ℝ) / (m + 1) ≤
      |logBirkhoffSum K ((k + 1) ^ 2) x / (((k + 1) ^ 2 : ℕ) : ℝ) - μ|} with hE
  have hfin : ∀ m : ℕ, (∑' k, gaussMeasure (E m k)) ≠ ⊤ := by
    intro m
    set δ : ℝ := 1 / (m + 1) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    set g : ℕ → ℝ := fun k =>
      logVarConst K / (δ ^ 2 * (((k + 1) ^ 2 : ℕ) : ℝ)) with hg
    have hVC : 0 ≤ logVarConst K := by
      unfold logVarConst
      have := logTailC1_nonneg K; have := logTailC2_nonneg K; have := logTailC3_nonneg K
      positivity
    have hgnn : ∀ k, 0 ≤ g k := by intro k; rw [hg]; positivity
    have hgsum : Summable g := by
      have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
        have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
          Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
        have := (summable_nat_add_iff 1).mpr h2
        simpa using this
      have hδ0 : δ ≠ 0 := hδpos.ne'
      have heq : g = fun k : ℕ =>
          (logVarConst K / δ ^ 2) * ((1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
        funext k
        have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
        simp only [hg]; push_cast; field_simp
      rw [heq]; exact hbase.mul_left _
    have hbound : ∀ k, gaussMeasure (E m k) ≤ ENNReal.ofReal (g k) := by
      intro k
      have hn : 0 < (k + 1) ^ 2 := by positivity
      have hcheb := chebyshev_logBirkhoffSum K ((k + 1) ^ 2) hn hδpos
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (hgnn k)).mpr hcheb
    have hle : (∑' k, gaussMeasure (E m k)) ≤ ENNReal.ofReal (∑' k, g k) := by
      refine (ENNReal.tsum_le_tsum hbound).trans ?_
      rw [ENNReal.ofReal_tsum_of_nonneg hgnn hgsum]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae : ∀ᵐ y ∂gaussMeasure, ∀ m : ℕ, ∀ᶠ k in atTop, y ∉ E m k := by
    rw [MeasureTheory.ae_all_iff]
    exact fun m => MeasureTheory.ae_eventually_notMem (hfin m)
  filter_upwards [hae] with y hy
  set a : ℕ → ℝ := fun k => logBirkhoffSum K ((k + 1) ^ 2) y / (((k + 1) ^ 2 : ℕ) : ℝ) with ha
  have hsub : Tendsto a atTop (nhds μ) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨Kk, hK⟩ := (hy m).exists_forall_of_atTop
    refine ⟨Kk, fun k hk => ?_⟩
    have hnot := hK k hk
    rw [hE] at hnot
    simp only [Set.mem_setOf_eq, not_le] at hnot
    rw [Real.dist_eq]
    calc |a k - μ|
        = |logBirkhoffSum K ((k + 1) ^ 2) y / (((k + 1) ^ 2 : ℕ) : ℝ) - μ| := by
          simp only [ha]
      _ < 1 / (m + 1) := hnot
      _ < ε := hm
  have hmono : ∀ {p q : ℕ}, p ≤ q → logBirkhoffSum K p y ≤ logBirkhoffSum K q y := by
    intro p q hpq
    simp only [logBirkhoffSum_apply]
    have hsub' : Finset.range p ⊆ Finset.range q := fun i hi =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hpq)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub'
    intro i _ _; exact logTailFn_nonneg_pointwise K _
  have hnn : ∀ p, 0 ≤ logBirkhoffSum K p y := fun p => logBirkhoffSum_nonneg K p y
  set Lfun : ℕ → ℝ := fun p =>
    logBirkhoffSum K ((Nat.sqrt p) ^ 2) y / ((((Nat.sqrt p) + 1) ^ 2 : ℕ) : ℝ) with hLfun
  set Ufun : ℕ → ℝ := fun p =>
    logBirkhoffSum K ((Nat.sqrt p + 1) ^ 2) y / (((Nat.sqrt p) ^ 2 : ℕ) : ℝ) with hUfun
  have hsqrt : Tendsto (fun p => Nat.sqrt p) atTop atTop := by
    rw [tendsto_atTop_atTop]
    exact fun b => ⟨b ^ 2, fun n hn => Nat.le_sqrt'.mpr hn⟩
  have hbase : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hrat1 : Tendsto (fun k : ℕ => ((k : ℝ)) ^ 2 / (((k : ℝ)) + 1) ^ 2) atTop (nhds 1) := by
    have := hbase.pow 2
    simpa [div_pow] using this
  have hrat2 : Tendsto (fun k : ℕ => (((k : ℝ)) + 1) ^ 2 / ((k : ℝ)) ^ 2) atTop (nhds 1) := by
    have hb2 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (nhds 1) := by
      have := hbase.inv₀ (one_ne_zero)
      simpa [inv_div] using this
    have := hb2.pow 2
    simpa [div_pow] using this
  have hsub1 : Tendsto (fun p => a (Nat.sqrt p - 1)) atTop (nhds μ) := by
    have hsub_shift : Tendsto (fun k => a (k - 1)) atTop (nhds μ) :=
      hsub.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun n hn => by omega⟩)
    exact hsub_shift.comp hsqrt
  have hsubj : Tendsto (fun p => a (Nat.sqrt p)) atTop (nhds μ) := hsub.comp hsqrt
  have hLprod : Tendsto (fun p => a (Nat.sqrt p - 1) *
      (((Nat.sqrt p : ℝ)) ^ 2 / (((Nat.sqrt p : ℝ)) + 1) ^ 2)) atTop (nhds μ) := by
    have := hsub1.mul (hrat1.comp hsqrt)
    simpa using this
  have hUprod : Tendsto (fun p => a (Nat.sqrt p) *
      ((((Nat.sqrt p : ℝ)) + 1) ^ 2 / ((Nat.sqrt p : ℝ)) ^ 2)) atTop (nhds μ) := by
    have := hsubj.mul (hrat2.comp hsqrt)
    simpa using this
  have hLeq : ∀ᶠ p in atTop, Lfun p =
      a (Nat.sqrt p - 1) * (((Nat.sqrt p : ℝ)) ^ 2 / (((Nat.sqrt p : ℝ)) + 1) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with p hp
    have hj1 : 1 ≤ Nat.sqrt p := Nat.le_sqrt'.mpr (by simpa using hp)
    have hjr : (0 : ℝ) < (Nat.sqrt p : ℝ) := by exact_mod_cast hj1
    have h1 : (Nat.sqrt p : ℝ) ≠ 0 := hjr.ne'
    have h2 : (Nat.sqrt p : ℝ) + 1 ≠ 0 := by positivity
    simp only [hLfun, ha]
    rw [show Nat.sqrt p - 1 + 1 = Nat.sqrt p from Nat.sub_add_cancel hj1]
    push_cast
    field_simp
  have hUeq : ∀ᶠ p in atTop, Ufun p =
      a (Nat.sqrt p) * ((((Nat.sqrt p : ℝ)) + 1) ^ 2 / ((Nat.sqrt p : ℝ)) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with p hp
    have hj1 : 1 ≤ Nat.sqrt p := Nat.le_sqrt'.mpr (by simpa using hp)
    have hjr : (0 : ℝ) < (Nat.sqrt p : ℝ) := by exact_mod_cast hj1
    have h1 : (Nat.sqrt p : ℝ) ≠ 0 := hjr.ne'
    have h2 : (Nat.sqrt p : ℝ) + 1 ≠ 0 := by positivity
    simp only [hUfun, ha]
    push_cast
    field_simp
  have hLtend : Tendsto Lfun atTop (nhds μ) := hLprod.congr' (hLeq.mono fun p h => h.symm)
  have hUtend : Tendsto Ufun atTop (nhds μ) := hUprod.congr' (hUeq.mono fun p h => h.symm)
  have hlow : ∀ᶠ p in atTop, Lfun p ≤ logBirkhoffSum K p y / (p : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with p hp
    set j := Nat.sqrt p with hj
    have hj1 : 1 ≤ j := Nat.le_sqrt'.mpr (by simpa using hp)
    have hj2p : j ^ 2 ≤ p := Nat.sqrt_le' p
    have hpj1 : p < (j + 1) ^ 2 := Nat.lt_succ_sqrt' p
    have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hd1 : (0 : ℝ) < (((j + 1) ^ 2 : ℕ) : ℝ) := by positivity
    simp only [hLfun, ← hj]
    calc logBirkhoffSum K (j ^ 2) y / ((((j + 1) ^ 2 : ℕ) : ℝ))
        ≤ logBirkhoffSum K p y / ((((j + 1) ^ 2 : ℕ) : ℝ)) := by
          gcongr
          exact hmono hj2p
      _ ≤ logBirkhoffSum K p y / (p : ℝ) := by
          rw [div_eq_mul_one_div (logBirkhoffSum K p y) ((((j + 1) ^ 2 : ℕ) : ℝ)),
            div_eq_mul_one_div (logBirkhoffSum K p y) (p : ℝ)]
          exact mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le hpr (by exact_mod_cast hpj1.le)) (hnn p)
  have hup : ∀ᶠ p in atTop, logBirkhoffSum K p y / (p : ℝ) ≤ Ufun p := by
    filter_upwards [eventually_ge_atTop 1] with p hp
    set j := Nat.sqrt p with hj
    have hj1 : 1 ≤ j := Nat.le_sqrt'.mpr (by simpa using hp)
    have hj2p : j ^ 2 ≤ p := Nat.sqrt_le' p
    have hpj1 : p < (j + 1) ^ 2 := Nat.lt_succ_sqrt' p
    have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hjr2 : (0 : ℝ) < (((j ^ 2 : ℕ)) : ℝ) := by
      have : 0 < j ^ 2 := by positivity
      exact_mod_cast this
    simp only [hUfun, ← hj]
    calc logBirkhoffSum K p y / (p : ℝ)
        ≤ logBirkhoffSum K p y / (((j ^ 2 : ℕ) : ℝ)) := by
          rw [div_eq_mul_one_div (logBirkhoffSum K p y) (p : ℝ),
            div_eq_mul_one_div (logBirkhoffSum K p y) ((((j ^ 2 : ℕ)) : ℝ))]
          exact mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le hjr2 (by exact_mod_cast hj2p)) (hnn p)
      _ ≤ logBirkhoffSum K ((j + 1) ^ 2) y / (((j ^ 2 : ℕ) : ℝ)) := by
          gcongr
          exact hmono hpj1.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLtend hUtend hlow hup

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
