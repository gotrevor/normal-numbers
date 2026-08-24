/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFBlockFreq

/-!
# The Khinchin log-tail bad zone (route B′/C′ machinery, khinchinK₀-free)

This file is UPSTREAM of `Headline.lean`/`Khinchin.lean` (it imports only
`CFBlockFreq`) precisely so its machinery is available where the
Becher–Yuhjtman schedule construction lives (`TBrick.lean` and downstream),
not just where `khinchinK₀` is defined. Everything here is provable from the
single-digit Gauss–Kuzmin law (`gaussMeasure_digit_cylinder`) alone — no
reference to `khinchinK₀`'s VALUE, only to the summability of its defining
series (`summable_gaussKuzmin_log`, reproving `Khinchin.lean`'s
`khinchinK₀_summable_log` argument from scratch here).

* `logTailFn K x = if K < cfDigit x 0 then log(cfDigit x 0) else 0` — the
  single-digit tail indicator.
* `integral_logTailFn_eq_of_hasSum` — its integral, GENERIC in the target
  `HasSum` (instantiated with `khinchinK₀`'s series downstream).
* `integrable_logTailFn` — integrability (khinchinK₀-free).
* `logBirkhoffSum K n = Σ_{i<n} logTailFn K ∘ Tⁱ` — the `n`-step Birkhoff sum,
  `integral_logBirkhoffSum` — its first moment.
* `logBadZone`, `markov_logBadZone_brick` — the Markov bad-zone bound,
  mirroring `cfBadZone`/`chebyshev_blockCount_brick` (`CFBlockFreq.lean`),
  UNIFORM in `n`.
-/

namespace NormalNumbers

open Filter MeasureTheory

/-! ## Summability of the Gauss–Kuzmin log-series (khinchinK₀-free) -/

private lemma gaussKuzminLogSeries_term_pos (k : ℕ) :
    0 < (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1) :=
  Real.rpow_pos_of_pos (by positivity) _

private lemma real_log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h0 : (0 : ℝ) < x := by linarith
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 h0
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt h0.le]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  nlinarith

private lemma summable_gaussKuzminLogSeries :
    Summable (fun k : ℕ => Real.log
      ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1))) := by
  have hterm : ∀ k : ℕ, Real.log
      ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1))
      = Real.logb 2 ((k : ℝ) + 1)
          * Real.log (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) := by
    intro k
    rw [Real.log_rpow (by positivity)]
  simp only [hterm]
  have hnonneg : ∀ k : ℕ, 0 ≤ Real.logb 2 ((k : ℝ) + 1)
      * Real.log (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) := by
    intro k
    apply mul_nonneg
    · exact Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    · exact Real.log_nonneg (by
        have : (0 : ℝ) ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by positivity
        linarith)
  have hmaj : Summable (fun k : ℕ => (2 / Real.log 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))) := by
    have hp : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
      have h := (Real.summable_one_div_nat_rpow (p := (3 : ℝ) / 2)).2 (by norm_num)
      have h1 := (summable_nat_add_iff 1).2 h
      apply h1.congr
      intro k
      push_cast
      ring
    exact hp.mul_left _
  apply Summable.of_nonneg_of_le hnonneg (fun k => ?_) hmaj
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlogb_le : Real.logb 2 ((k : ℝ) + 1) ≤ 2 * Real.sqrt ((k : ℝ) + 1) / Real.log 2 := by
    rw [Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
    exact real_log_le_two_sqrt hk1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloginner_le : Real.log (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
      ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) by positivity)
    linarith
  have hsq_pos : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
  have hr0 : (0 : ℝ) < ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hkey : Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) = ((k : ℝ) + 1) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith),
      show (1 : ℝ) / 2 + 3 / 2 = 2 by norm_num, Real.rpow_two]
  have hle : Real.sqrt ((k : ℝ) + 1) * (((k : ℝ) + 1) * ((k : ℝ) + 3))⁻¹
      ≤ 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hr0]
    have hb : Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤
        (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by rw [hkey]; nlinarith
    calc Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ _ := hb
      _ = _ := by ring
  calc Real.logb 2 ((k : ℝ) + 1) * Real.log (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
      ≤ (2 * Real.sqrt ((k : ℝ) + 1) / Real.log 2)
          * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) := by
        apply mul_le_mul hlogb_le hloginner_le
          (Real.log_nonneg (by
            have : (0 : ℝ) ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by positivity
            linarith))
          (div_nonneg (by positivity) hlog2pos.le)
    _ = (2 / Real.log 2) * (Real.sqrt ((k : ℝ) + 1) * (((k : ℝ) + 1) * ((k : ℝ) + 3))⁻¹) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ (2 / Real.log 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hle (div_nonneg (by norm_num) hlog2pos.le)

/-- The Gauss–Kuzmin log-series term, `logTailG k = γ([k+1])·log(k+1)`. -/
noncomputable def logTailG : ℕ → ℝ :=
  fun k => (gaussMeasure (cfCylinder [k + 1])).toReal * Real.log ((k : ℝ) + 1)

/-- **`logTailG` is summable** — no reference to `khinchinK₀`'s VALUE, only
the same `1/(k+1)^{3/2}`-comparison `khinchinK₀_summable_log` (`Khinchin.lean`)
uses, reproven here from `gaussMeasure_digit_cylinder` directly. -/
theorem summable_gaussKuzmin_log : Summable logTailG := by
  have key : ∀ k : ℕ, logTailG k
      = Real.log ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1)) := by
    intro k
    unfold logTailG
    rw [gaussMeasure_digit_cylinder (k + 1) (by omega),
      ENNReal.toReal_ofReal (Real.logb_nonneg (by norm_num)
        (le_add_of_nonneg_right (by positivity))),
      Real.log_rpow (by positivity)]
    push_cast
    simp only [Real.logb]
    ring
  rw [show logTailG = fun k : ℕ => Real.log
      ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1))
    from funext key]
  exact summable_gaussKuzminLogSeries

/-! ## The single-digit tail indicator -/

/-- Single digit-value indicator term: value `log(K+1+n)` on the cylinder
`[K+1+n]`, `0` elsewhere. -/
private noncomputable def logTailTerm (K n : ℕ) : ℝ → ℝ :=
  (cfCylinder [K + 1 + n]).indicator (fun _ => Real.log ((K : ℝ) + 1 + n))

private lemma logTailTerm_value_nonneg (K n : ℕ) : (0 : ℝ) ≤ Real.log ((K : ℝ) + 1 + n) :=
  Real.log_nonneg (by
    have hK := Nat.cast_nonneg (α := ℝ) K
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith)

private lemma logTailTerm_nonneg (K n : ℕ) (x : ℝ) : 0 ≤ logTailTerm K n x := by
  unfold logTailTerm
  by_cases hmem : x ∈ cfCylinder [K + 1 + n]
  · rw [Set.indicator_of_mem hmem]; exact logTailTerm_value_nonneg K n
  · rw [Set.indicator_of_notMem hmem]

/-- The single-digit tail indicator: `log(cfDigit x 0)` when the digit exceeds
`K`, else `0`. -/
noncomputable def logTailFn (K : ℕ) : ℝ → ℝ :=
  fun x => if K < cfDigit x 0 then Real.log (cfDigit x 0 : ℝ) else 0

lemma logTailFn_nonneg_pointwise (K : ℕ) (x : ℝ) : 0 ≤ logTailFn K x := by
  unfold logTailFn
  split
  · exact Real.log_natCast_nonneg _
  · exact le_refl 0

private lemma logTailTerm_integrable (K n : ℕ) :
    Integrable (logTailTerm K n) gaussMeasure :=
  (integrable_const (Real.log ((K : ℝ) + 1 + n))).indicator
    (measurableSet_cfCylinder [K + 1 + n])

/-- Norm-integral of a single term is exactly the Gauss–Kuzmin series term,
shifted by `K`. -/
private lemma integral_norm_logTailTerm (K n : ℕ) :
    ∫ x, ‖logTailTerm K n x‖ ∂gaussMeasure
      = (gaussMeasure (cfCylinder [K + 1 + n])).toReal * Real.log (((K : ℝ) + n) + 1) := by
  have hlog0 : (0:ℝ) ≤ Real.log ((K:ℝ) + 1 + n) :=
    Real.log_nonneg (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) n])
  have heq : (fun x => ‖logTailTerm K n x‖)
      = (cfCylinder [K + 1 + n]).indicator (fun _ => Real.log ((K : ℝ) + 1 + n)) := by
    funext x
    unfold logTailTerm
    by_cases h : x ∈ cfCylinder [K + 1 + n]
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg hlog0]
    · rw [Set.indicator_of_notMem h, norm_zero]
  rw [heq, MeasureTheory.integral_indicator_const _ (measurableSet_cfCylinder [K + 1 + n]),
    smul_eq_mul, MeasureTheory.measureReal_def]
  congr 2
  push_cast
  ring

/-- Direct (non-`norm`) integral of a single term: same value as
`integral_norm_logTailTerm` since the term is already nonnegative. -/
private lemma integral_logTailTerm (K n : ℕ) :
    ∫ x, logTailTerm K n x ∂gaussMeasure
      = (gaussMeasure (cfCylinder [K + 1 + n])).toReal * Real.log (((K : ℝ) + n) + 1) := by
  unfold logTailTerm
  rw [MeasureTheory.integral_indicator_const _ (measurableSet_cfCylinder [K + 1 + n]),
    smul_eq_mul, MeasureTheory.measureReal_def]
  congr 2
  push_cast
  ring

/-- `gaussMeasure` gives zero mass to the complement of `(0,1)` (it is a
`withDensity` of `volume.restrict (0,1)`). -/
private lemma gaussMeasure_compl_Ioo : gaussMeasure (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
  have hac : gaussMeasure ≪ (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  apply hac
  rw [Measure.restrict_apply' measurableSet_Ioo]
  simp

private lemma ae_mem_Ioo_gaussMeasure : ∀ᵐ x ∂gaussMeasure, x ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [MeasureTheory.ae_iff]
  exact gaussMeasure_compl_Ioo

/-- `logTailG (n + K) = ∫ logTailTerm K n` (and its `norm`), the reindexing
identity used for the integrability input and the final `tsum` collapse. -/
private lemma logTailG_shift (K n : ℕ) : logTailG (n + K) =
    (gaussMeasure (cfCylinder [K + 1 + n])).toReal * Real.log (((K : ℝ) + n) + 1) := by
  unfold logTailG
  have hidx : n + K + 1 = K + 1 + n := by omega
  rw [hidx]
  congr 1
  push_cast
  ring

/-- Pointwise a.e. collapse of the tsum of terms to `logTailFn`. -/
private lemma logTailTerm_tsum_ae_eq (K : ℕ) :
    ∀ᵐ x ∂gaussMeasure, ∑' n, logTailTerm K n x = logTailFn K x := by
  filter_upwards [ae_mem_Ioo_gaussMeasure] with x hx
  unfold logTailFn
  by_cases hd : K < cfDigit x 0
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hd
    have hkey : K + 1 + m = cfDigit x 0 := by omega
    rw [if_pos hd, tsum_eq_single m]
    · unfold logTailTerm
      rw [Set.indicator_of_mem (mem_cfCylinder_singleton.mpr ⟨hx, hkey.symm⟩)]
      rw [← hkey]
      push_cast
      ring
    · intro n hne
      unfold logTailTerm
      rw [Set.indicator_of_notMem]
      rw [mem_cfCylinder_singleton]
      rintro ⟨-, hcd⟩
      exact hne (by omega)
  · rw [if_neg hd]
    have hzero : (fun n => logTailTerm K n x) = fun _ => (0 : ℝ) := by
      funext n
      unfold logTailTerm
      rw [Set.indicator_of_notMem]
      rw [mem_cfCylinder_singleton]
      rintro ⟨-, hcd⟩
      omega
    rw [hzero, tsum_zero]

private lemma logTailTerm_summable_norm_integral (K : ℕ) :
    Summable (fun n => ∫ x, ‖logTailTerm K n x‖ ∂gaussMeasure) := by
  have heq : (fun n => ∫ x, ‖logTailTerm K n x‖ ∂gaussMeasure) = fun n => logTailG (n + K) := by
    funext n
    rw [integral_norm_logTailTerm, logTailG_shift]
  rw [heq]
  exact (summable_nat_add_iff K).2 summable_gaussKuzmin_log

/-- **First-moment tail integral, GENERIC in the target `HasSum`**: given
`HasSum logTailG L` (instantiated downstream with `L = log khinchinK₀` via
`gaussKuzmin_logsum_hasSum`), `∫ logTailFn K dγ = L − Σ_{k<K} logTailG k`. -/
theorem integral_logTailFn_eq_of_hasSum (K : ℕ) {L : ℝ} (hL : HasSum logTailG L) :
    ∫ x, logTailFn K x ∂gaussMeasure = L - ∑ k ∈ Finset.range K, logTailG k := by
  have hInt : ∀ n, Integrable (logTailTerm K n) gaussMeasure := logTailTerm_integrable K
  have hSumNorm := logTailTerm_summable_norm_integral K
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSumNorm
  have hlhs : ∑' n, ∫ x, logTailTerm K n x ∂gaussMeasure = ∑' n, logTailG (n + K) := by
    refine tsum_congr fun n => ?_
    rw [integral_logTailTerm, logTailG_shift]
  have htail : HasSum (fun n => logTailG (n + K)) (L - ∑ k ∈ Finset.range K, logTailG k) :=
    (hasSum_nat_add_iff' K).2 hL
  rw [hlhs, htail.tsum_eq] at hswap
  rw [← MeasureTheory.integral_congr_ae (logTailTerm_tsum_ae_eq K), hswap]

/-- **The tail integral vanishes as `K → ∞`, KHINCHINK₀-FREE.** Instantiates
`integral_logTailFn_eq_of_hasSum` at `L = ∑' n, logTailG n` (`logTailG`'s own
sum, via `summable_gaussKuzmin_log` — no reference to `khinchinK₀`'s VALUE),
so `∫ logTailFn K dγ` is exactly the `K`-tail of a summable series, which
`HasSum.tendsto_sum_nat` sends to `0`.  This is the layering-safe route: it
lives upstream of `Headline.lean`/`khinchinK₀` (unlike `Khinchin.lean`'s
`integral_logTailFn_tendsto`, which proves the same fact via
`gaussKuzmin_logtail_tendsto` but needs `khinchinK₀` to STATE the intermediate
value `log khinchinK₀`), so it is what `KhinchinBrick.lean`'s `K`-selection
uses to stay upstream of `CFSchedule.lean`. -/
theorem integral_logTailFn_tendsto_zero :
    Filter.Tendsto (fun K : ℕ => ∫ x, logTailFn K x ∂gaussMeasure)
      Filter.atTop (nhds 0) := by
  have hL : HasSum logTailG (∑' n, logTailG n) := summable_gaussKuzmin_log.hasSum
  have heq : ∀ K : ℕ, ∫ x, logTailFn K x ∂gaussMeasure
      = (∑' n, logTailG n) - ∑ k ∈ Finset.range K, logTailG k :=
    fun K => integral_logTailFn_eq_of_hasSum K hL
  simp_rw [heq]
  have hpartial := hL.tendsto_sum_nat
  have hsub := Filter.Tendsto.const_sub (∑' n, logTailG n) hpartial
  simpa using hsub

/-- `logTailFn K` is measurable: `cfDigit · 0` is measurable and the
post-composition with the (discrete-domain) threshold/`log` map is
automatically measurable. -/
private lemma measurable_logTailFn (K : ℕ) : Measurable (logTailFn K) := by
  have hd : Measurable (fun x => cfDigit x 0) := measurable_cfDigit 0
  have hg : Measurable (fun d : ℕ => if K < d then Real.log (d : ℝ) else 0) :=
    measurable_from_top
  exact hg.comp hd

/-- **`logTailFn K` is integrable.** Nonneg + measurable + a finite `lintegral`
computed by the SAME tsum-swap route as `integral_logTailFn_eq_of_hasSum`, but
in `ℝ≥0∞` via `lintegral_tsum` (unconditional — no summability side-condition
needed there, unlike the Bochner swap). KHINCHINK₀-FREE — only needs
`summable_gaussKuzmin_log`. -/
theorem integrable_logTailFn (K : ℕ) : Integrable (logTailFn K) gaussMeasure := by
  have hnonneg : 0 ≤ᵐ[gaussMeasure] logTailFn K := by
    filter_upwards with x
    unfold logTailFn
    split
    · exact Real.log_natCast_nonneg _
    · exact le_refl (0 : ℝ)
  refine ⟨(measurable_logTailFn K).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg]
  have hstep1 : ∫⁻ x, ENNReal.ofReal (logTailFn K x) ∂gaussMeasure
      = ∫⁻ x, ENNReal.ofReal (∑' n, logTailTerm K n x) ∂gaussMeasure := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [logTailTerm_tsum_ae_eq K] with x hx
    rw [hx]
  have hpt : ∀ x, ENNReal.ofReal (∑' n, logTailTerm K n x)
      = ∑' n, ENNReal.ofReal (logTailTerm K n x) := by
    intro x
    have hloc : Summable (fun n => logTailTerm K n x) := by
      unfold logTailTerm
      by_cases hcase : ∃ n, x ∈ cfCylinder [K + 1 + n]
      · obtain ⟨n₀, hn₀⟩ := hcase
        apply summable_of_ne_finset_zero (s := {n₀})
        intro n hn
        simp only [Finset.mem_singleton] at hn
        rw [Set.indicator_of_notMem]
        intro hmem
        apply hn
        have h1 := (mem_cfCylinder_singleton.mp hn₀).2
        have h2 := (mem_cfCylinder_singleton.mp hmem).2
        omega
      · push_neg at hcase
        simp only [Set.indicator_of_notMem (hcase _)]
        exact summable_zero
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => logTailTerm_nonneg K n x) hloc
  have hstep2 : ∫⁻ x, ENNReal.ofReal (∑' n, logTailTerm K n x) ∂gaussMeasure
      = ∫⁻ x, ∑' n, ENNReal.ofReal (logTailTerm K n x) ∂gaussMeasure := by
    exact MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpt)
  have hstep3 : ∫⁻ x, ∑' n, ENNReal.ofReal (logTailTerm K n x) ∂gaussMeasure
      = ∑' n, ∫⁻ x, ENNReal.ofReal (logTailTerm K n x) ∂gaussMeasure := by
    refine MeasureTheory.lintegral_tsum fun n => ?_
    exact (measurable_const.indicator (measurableSet_cfCylinder [K + 1 + n])).aemeasurable.ennreal_ofReal
  have hstep4 : ∀ n, ∫⁻ x, ENNReal.ofReal (logTailTerm K n x) ∂gaussMeasure
      = ENNReal.ofReal (∫ x, logTailTerm K n x ∂gaussMeasure) := by
    intro n
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (logTailTerm_integrable K n)]
    filter_upwards with x
    exact logTailTerm_nonneg K n x
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ ∫ x, logTailTerm K n x ∂gaussMeasure := fun n =>
    MeasureTheory.integral_nonneg (logTailTerm_nonneg K n)
  have hstep5 : ∑' n, ENNReal.ofReal (∫ x, logTailTerm K n x ∂gaussMeasure)
      = ENNReal.ofReal (∑' n, ∫ x, logTailTerm K n x ∂gaussMeasure) := by
    refine (ENNReal.ofReal_tsum_of_nonneg hterm_nonneg
      ((logTailTerm_summable_norm_integral K).congr fun n => ?_)).symm
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (logTailTerm_nonneg K n x)]
  rw [hstep1, hstep2, hstep3]
  simp_rw [hstep4]
  rw [hstep5]
  exact ENNReal.ofReal_lt_top

/-! ## The `n`-step log-tail Birkhoff sum (route B′)

`logBirkhoffSum K n x = Σ_{i<n} logTailFn K (Tⁱx)`, the empirical log-tail
mass over `n` steps.  Mirrors `blockCount`'s Birkhoff-sum machinery
(`CFBlockFreq.lean`) with the unbounded weight `logTailFn K` in place of a
`{0,1}`-valued indicator; `integral_logTailFn_eq_of_hasSum`/`integrable_logTailFn`
supply exactly the per-step input `integral_blockCount`'s proof needs. -/

/-- The `n`-step log-tail Birkhoff sum. -/
noncomputable def logBirkhoffSum (K n : ℕ) : ℝ → ℝ :=
  birkhoffSum gaussMap (logTailFn K) n

lemma logBirkhoffSum_apply (K n : ℕ) (x : ℝ) :
    logBirkhoffSum K n x = ∑ k ∈ Finset.range n, logTailFn K (gaussMap^[k] x) := rfl

-- Each shifted term is integrable: `logTailFn K` is integrable
-- (`integrable_logTailFn`) and `gaussMap^[k]` is measure-preserving.
set_option maxHeartbeats 800000 in
private lemma integrable_logTailFn_iterate (K k : ℕ) :
    Integrable (fun x => logTailFn K (gaussMap^[k] x)) gaussMeasure := by
  have h := (measurePreserving_gaussMap.iterate k).integrable_comp_of_integrable
    (integrable_logTailFn K)
  exact h

-- Each shifted term has the SAME integral as the base step (measure
-- preservation): `∫ logTailFn K ∘ Tᵏ dγ = ∫ logTailFn K dγ`.
set_option maxHeartbeats 800000 in
private lemma integral_logTailFn_iterate (K k : ℕ) :
    ∫ x, logTailFn K (gaussMap^[k] x) ∂gaussMeasure
      = ∫ x, logTailFn K x ∂gaussMeasure := by
  conv_rhs => rw [← (measurePreserving_gaussMap.iterate k).map_eq]
  exact (integral_map (measurePreserving_gaussMap.iterate k).measurable.aemeasurable
    (measurable_logTailFn K).aestronglyMeasurable).symm

/-- `logBirkhoffSum K n` is measurable. -/
lemma measurable_logBirkhoffSum (K n : ℕ) : Measurable (logBirkhoffSum K n) := by
  have heq : logBirkhoffSum K n
      = fun x => ∑ k ∈ Finset.range n, logTailFn K (gaussMap^[k] x) := rfl
  rw [heq]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_logTailFn K).comp (measurable_gaussMap.iterate k)

/-- **First moment of the `n`-step log-tail Birkhoff sum**: `∫ logBirkhoffSum
K n dγ = n · ∫ logTailFn K dγ`.  Same route as `integral_blockCount`: split
the finite sum, use measure preservation per step. -/
theorem integral_logBirkhoffSum (K n : ℕ) :
    ∫ x, logBirkhoffSum K n x ∂gaussMeasure
      = n * ∫ x, logTailFn K x ∂gaussMeasure := by
  calc ∫ x, logBirkhoffSum K n x ∂gaussMeasure
      = ∑ k ∈ Finset.range n, ∫ x, logTailFn K (gaussMap^[k] x) ∂gaussMeasure := by
        rw [show (fun x => logBirkhoffSum K n x)
            = fun x => ∑ k ∈ Finset.range n, logTailFn K (gaussMap^[k] x) from
          funext (logBirkhoffSum_apply K n)]
        exact integral_finsetSum _ (fun k _ => integrable_logTailFn_iterate K k)
    _ = ∑ _k ∈ Finset.range n, ∫ x, logTailFn K x ∂gaussMeasure :=
        Finset.sum_congr rfl fun k _ => integral_logTailFn_iterate K k
    _ = n * ∫ x, logTailFn K x ∂gaussMeasure := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `logBirkhoffSum` is pointwise nonnegative (each term is). -/
lemma logBirkhoffSum_nonneg (K n : ℕ) (x : ℝ) : 0 ≤ logBirkhoffSum K n x := by
  rw [logBirkhoffSum_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  unfold logTailFn
  split
  · exact Real.log_natCast_nonneg _
  · exact le_refl 0

/-- `logBirkhoffSum K n` is integrable (finite sum of integrable shifted
terms). -/
private lemma integrable_logBirkhoffSum (K n : ℕ) :
    Integrable (logBirkhoffSum K n) gaussMeasure := by
  have heq : logBirkhoffSum K n
      = fun x => ∑ k ∈ Finset.range n, logTailFn K (gaussMap^[k] x) := rfl
  rw [heq]
  exact integrable_finsetSum _ (fun k _ => integrable_logTailFn_iterate K k)

/-! ## The Khinchin log-tail bad zone (route B′/C′)

`logBadZone w n K η`: points of the brick `I_w` whose orbit's `n`-step
log-tail mass (past cutoff `K`) exceeds `η·n`.  Mirrors `cfBadZone`
(`TBrick.lean`) with `logBirkhoffSum K n` in place of `blockCount`; the
Markov bound below is the analogue of `chebyshev_blockCount_brick`
(`CFBlockFreq.lean`), using the FIRST moment only (`integral_logBirkhoffSum`)
since `logBirkhoffSum` is nonnegative — no second-moment/variance input
needed. -/

/-- The **Khinchin log-tail bad zone** of a brick `I_w`: points whose
orbit's `n`-step log-tail mass past cutoff `K` exceeds `η·n`. -/
def logBadZone (w : List ℕ) (n K : ℕ) (η : ℝ) : Set ℝ :=
  cfCylinder w ∩ (gaussMap^[w.length]) ⁻¹'
    {x ∈ Set.Ioo (0 : ℝ) 1 | η * n < logBirkhoffSum K n x}

lemma measurableSet_logBadZone (w : List ℕ) (n K : ℕ) (η : ℝ) :
    MeasurableSet (logBadZone w n K η) := by
  have hset : MeasurableSet {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ η * n < logBirkhoffSum K n x} := by
    rw [Set.setOf_and]
    exact measurableSet_Ioo.inter (measurableSet_lt measurable_const (measurable_logBirkhoffSum K n))
  exact (measurableSet_cfCylinder w).inter ((measurable_gaussMap.iterate w.length) hset)

/-- **Markov bound on the raw bad set**: `γ({x ∈ (0,1) | η·n < S_n(x)}) ≤
(∫ logTailFn K dγ)/η`, uniformly in `n` (the `n` in the threshold and the
`n` in the first moment `integral_logBirkhoffSum` CANCEL). This is the
route-B′ punchline: dividing by `n` removes ALL `n`-dependence from the
bound, leaving only a `K`-dependent tail that a downstream `→ 0` fact
(`Khinchin.lean`'s `integral_logTailFn_tendsto`) sends to `0`. -/
theorem gaussMeasure_logBadZone_raw_le (n K : ℕ) {η : ℝ} (hη : 0 < η) :
    (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 | η * (n : ℝ) < logBirkhoffSum K n x}).toReal
      ≤ (∫ x, logTailFn K x ∂gaussMeasure) / η := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hempty : {x ∈ Set.Ioo (0 : ℝ) 1 | η * ((0 : ℕ) : ℝ) < logBirkhoffSum K 0 x} = ∅ := by
      ext x
      simp only [Nat.cast_zero, mul_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hlt⟩
      exact absurd hlt (not_lt.2 (logBirkhoffSum_nonneg K 0 x))
    rw [hempty, measure_empty, ENNReal.toReal_zero]
    exact div_nonneg (MeasureTheory.integral_nonneg fun x =>
      logTailFn_nonneg_pointwise K x) hη.le
  have hsub : {x ∈ Set.Ioo (0 : ℝ) 1 | η * (n : ℝ) < logBirkhoffSum K n x}
      ⊆ {x : ℝ | η * (n : ℝ) ≤ logBirkhoffSum K n x} := fun x hx => hx.2.le
  have hnn : 0 ≤ᵐ[gaussMeasure] logBirkhoffSum K n := by
    filter_upwards with x
    exact logBirkhoffSum_nonneg K n x
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn (integrable_logBirkhoffSum K n)
    (η * (n : ℝ))
  rw [integral_logBirkhoffSum] at hmarkov
  have hle : gaussMeasure.real {x ∈ Set.Ioo (0 : ℝ) 1 | η * (n : ℝ) < logBirkhoffSum K n x}
      ≤ gaussMeasure.real {x : ℝ | η * (n : ℝ) ≤ logBirkhoffSum K n x} :=
    MeasureTheory.measureReal_mono hsub (measure_ne_top _ _)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  rw [MeasureTheory.measureReal_def] at hle hmarkov
  rw [le_div_iff₀ hη]
  have hstep : η * (n : ℝ) * (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
      η * (n : ℝ) < logBirkhoffSum K n x}).toReal
      ≤ (n : ℝ) * ∫ x, logTailFn K x ∂gaussMeasure := by
    calc η * (n : ℝ) * (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
          η * (n : ℝ) < logBirkhoffSum K n x}).toReal
        ≤ η * (n : ℝ) * (gaussMeasure {x : ℝ | η * (n : ℝ) ≤ logBirkhoffSum K n x}).toReal :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ (n : ℝ) * ∫ x, logTailFn K x ∂gaussMeasure := hmarkov
  have := (mul_le_mul_iff_of_pos_left hn0).mp (by
    calc (n : ℝ) * ((gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
          η * (n : ℝ) < logBirkhoffSum K n x}).toReal * η)
        = η * (n : ℝ) * (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
            η * (n : ℝ) < logBirkhoffSum K n x}).toReal := by ring
      _ ≤ (n : ℝ) * ∫ x, logTailFn K x ∂gaussMeasure := hstep)
  exact this

/-- **Brick-conditioned Markov bound on the Khinchin bad zone**: inside any
brick `I_w`, the part whose continuation has `n`-step log-tail mass past
cutoff `K` exceeding `η·n` has γ-measure at most `7·(∫ logTailFn K dγ)/η·γ(I_w)`
— UNIFORM in `n`.  Same `gaussMeasure_brick_inter_le` distortion step as
`chebyshev_blockCount_brick`. -/
theorem markov_logBadZone_brick (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (n K : ℕ) {η : ℝ}
    (hη : 0 < η) :
    (gaussMeasure (logBadZone w n K η)).toReal ≤
      7 * ((∫ x, logTailFn K x ∂gaussMeasure) / η) * (gaussMeasure (cfCylinder w)).toReal := by
  have hBadmeas : MeasurableSet {x ∈ Set.Ioo (0 : ℝ) 1 | η * (n : ℝ) < logBirkhoffSum K n x} := by
    rw [Set.setOf_and]
    exact measurableSet_Ioo.inter (measurableSet_lt measurable_const (measurable_logBirkhoffSum K n))
  have hBadsub : {x ∈ Set.Ioo (0 : ℝ) 1 | η * (n : ℝ) < logBirkhoffSum K n x}
      ⊆ Set.Ioo (0 : ℝ) 1 := Set.sep_subset _ _
  calc (gaussMeasure (logBadZone w n K η)).toReal
      ≤ 7 * (gaussMeasure {x ∈ Set.Ioo (0 : ℝ) 1 |
          η * (n : ℝ) < logBirkhoffSum K n x}).toReal
          * (gaussMeasure (cfCylinder w)).toReal :=
        gaussMeasure_brick_inter_le w hposw hBadmeas hBadsub
    _ ≤ 7 * ((∫ x, logTailFn K x ∂gaussMeasure) / η) * (gaussMeasure (cfCylinder w)).toReal := by
        gcongr
        exact gaussMeasure_logBadZone_raw_le n K hη

end NormalNumbers
