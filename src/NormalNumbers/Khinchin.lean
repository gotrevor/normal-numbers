/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline
import NormalNumbers.CFDigitLaw
import NormalNumbers.CFBlockFreq

/-!
# W6 — Khinchin-typicality of `xstar` (Tier 2)

Track B's expedition headline (`KHINCHIN.md`): additionally to Tier 1
(absolutely normal ∧ CF-normal, LOCKED — `Headline.lean`), show `xstar`'s CF
digits are **Khinchin-typical**: the geometric mean `(∏_{i<n} aᵢ)^{1/n} →
K₀`.

Route insight (this expedition, `PENDING_WORK.md` 2026-08-26): the schedule's
existing continuant payload `cfK(uSched s) ≤ exp(goodC·n)` already bounds the
average `log`-digit per stage (`prod_le_cfK`, `uSched_log_sum_le`,
`wSched_log_sum_le` in `CFCorrect.lean`) — **no digit-cap re-plumb of the
schedule is needed**, contrary to the original W6 sizing.  What remains is
the analytic assembly: match the (now uniformly bounded) log-digit average
against the Gauss–Kuzmin frequencies already proved via
`xstar_cf_freq_tendsto`.

This file starts that assembly with the elementary reduction (geometric mean
limit ⟺ log-average limit), fully proved, and isolates the one remaining
purely-elementary gap (`khinchinK₀` is a genuine positive real, i.e. its
defining `tprod` is `Multipliable`) as a named `sorry`.
-/

namespace NormalNumbers

open Filter MeasureTheory

/-- `Finset.range`-sum of any list-indexed function equals the `List.range`
`map`+`sum` form — the elementary bridge between the CF-schedule module's
`List`-based bookkeeping and `KhinchinTypical`'s `Finset.sum` statement. -/
theorem finset_sum_range_eq_list_sum {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
      simp

private lemma khinchinK₀_term_pos (k : ℕ) :
    0 < (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1) :=
  Real.rpow_pos_of_pos (by positivity) _

private lemma khinchinK₀_log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h0 : (0 : ℝ) < x := by linarith
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 h0
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt h0.le]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  nlinarith

private lemma khinchinK₀_summable_log :
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
    exact khinchinK₀_log_le_two_sqrt hk1
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

/-- **Second moment of `log a₁` under the Gauss measure is finite**: the
Gauss–Kuzmin-weighted series `Σₐ γ([a])·(log a)²` converges, where `γ([a]) =
logb 2 (1 + 1/(a(a+2)))` is the single-digit Gauss–Kuzmin law
(`gaussMeasure_digit_cylinder`), `k`-indexed with `a = k + 1`.  This is the
moment condition `E[(log a₁)²] < ∞` that a Chebyshev/variance bound on the
log-digit sum `Σ_{i<n} log aᵢ` requires — the analytic seed of the Khinchin
concentration bad zone (`DIRECTION.md` 2026-08-24 route, the step-2 crux).
Comparison with `1/(k+1)^{3/2}`, in the style of `khinchinK₀_summable_log`:
`γ([a]) ≤ 1/(log 2·(k+1)²)` (from `log(1+x) ≤ x`) and `(log(k+1))² ≤ 16·√(k+1)`
(from `log y ≤ 4·y^{1/4}`, i.e. `khinchinK₀_log_le_two_sqrt` applied at `√y`). -/
theorem summable_gaussKuzmin_logsq :
    Summable (fun k : ℕ =>
      Real.logb 2 (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
        * (Real.log ((k : ℝ) + 1)) ^ 2) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- nonnegativity of each term
  have hnonneg : ∀ k : ℕ, 0 ≤ Real.logb 2 (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
      * (Real.log ((k : ℝ) + 1)) ^ 2 := by
    intro k
    apply mul_nonneg
    · exact Real.logb_nonneg (by norm_num) (by
        have : (0 : ℝ) ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by positivity
        linarith)
    · positivity
  -- summable majorant `(16/log 2)·1/(k+1)^{3/2}`
  have hmaj : Summable (fun k : ℕ => (16 / Real.log 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2))) := by
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
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  -- bound the logb factor: γ([a]) ≤ 1/(log 2·(k+1)²)
  have hlogb_le : Real.logb 2 (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
      ≤ (1 / (((k : ℝ) + 1) ^ 2)) / Real.log 2 := by
    rw [Real.logb, div_le_div_iff_of_pos_right hlog2pos]
    have hinner : Real.log (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)))
        ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by
      have := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) by positivity)
      linarith
    have hmono : 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) ≤ 1 / (((k : ℝ) + 1) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  -- bound the squared-log factor: (log(k+1))² ≤ 16·√(k+1)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) :=
    Real.one_le_sqrt.2 hk1
  have hlog4 : Real.log ((k : ℝ) + 1) ≤ 4 * Real.sqrt (Real.sqrt ((k : ℝ) + 1)) := by
    have h1 : Real.log (Real.sqrt ((k : ℝ) + 1)) ≤ 2 * Real.sqrt (Real.sqrt ((k : ℝ) + 1)) :=
      khinchinK₀_log_le_two_sqrt hsqrt1
    rw [Real.log_sqrt hk1pos.le] at h1
    linarith
  have hlognn : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hk1
  have hlogsq_le : (Real.log ((k : ℝ) + 1)) ^ 2 ≤ 16 * Real.sqrt ((k : ℝ) + 1) := by
    have h4nn : (0 : ℝ) ≤ 4 * Real.sqrt (Real.sqrt ((k : ℝ) + 1)) := by positivity
    have hsq : (Real.log ((k : ℝ) + 1)) ^ 2 ≤ (4 * Real.sqrt (Real.sqrt ((k : ℝ) + 1))) ^ 2 := by
      apply sq_le_sq' (by linarith) hlog4
    have hss : Real.sqrt (Real.sqrt ((k : ℝ) + 1)) ^ 2 = Real.sqrt ((k : ℝ) + 1) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    nlinarith [hss]
  -- combine, then simplify √(k+1)/(k+1)² = 1/(k+1)^{3/2}
  have hr0 : (0 : ℝ) < ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hk1pos _
  have hkey : Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) = ((k : ℝ) + 1) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk1pos,
      show (1 : ℝ) / 2 + 3 / 2 = 2 by norm_num, Real.rpow_two]
  have hfrac : Real.sqrt ((k : ℝ) + 1) / (((k : ℝ) + 1) ^ 2) = 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
    rw [div_eq_div_iff (by positivity : (0:ℝ) < ((k:ℝ)+1)^2).ne' hr0.ne', one_mul]
    exact hkey
  calc Real.logb 2 (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) * (Real.log ((k : ℝ) + 1)) ^ 2
      ≤ ((1 / (((k : ℝ) + 1) ^ 2)) / Real.log 2) * (16 * Real.sqrt ((k : ℝ) + 1)) := by
        apply mul_le_mul hlogb_le hlogsq_le (by positivity)
          (div_nonneg (by positivity) hlog2pos.le)
    _ = (16 / Real.log 2) * (Real.sqrt ((k : ℝ) + 1) / (((k : ℝ) + 1) ^ 2)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    _ = (16 / Real.log 2) * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by rw [hfrac]

/-- **Khinchin's constant is a genuine positive real**: its defining `tprod`
converges (`Multipliable`), and the value of ANY convergent product of
positive terms via `Real.hasProd_of_hasSum_log` is `exp` of the log-sum, so
positive automatically — the summability of the K₀-exponent series `Σₐ
log₂(a)·log(1 + 1/(a(a+2)))` (by comparison with `log(a)/a^{3/2}`, in the
style of `CFDigitLaw.lean`'s `summable_digitLog`) is the only real content. -/
theorem khinchinK₀_pos : 0 < khinchinK₀ := by
  have hfn := khinchinK₀_term_pos
  have hsum := khinchinK₀_summable_log
  have hprod := Real.hasProd_of_hasSum_log hfn hsum.hasSum
  rw [khinchinK₀]
  rw [hprod.tprod_eq]
  exact Real.exp_pos _

/-- **The Gauss–Kuzmin log-average equals `log K₀`** (`Σₐ γ([a])·log a =
log khinchinK₀`, as a `HasSum` over `k`-indexed digit values `a = k + 1`).
This is the identity that makes Khinchin's constant the target of the
log-digit average: the single-digit Gauss–Kuzmin weight `γ([a]) = logb 2
(1 + 1/(a(a+2)))` (`gaussMeasure_digit_cylinder`) times `log a`, summed, is
`log K₀`.  Both sides are `(1/log 2)·Σₖ log(k+1)·log(1 + 1/((k+1)(k+3)))` —
the `logb`-vs-`log` factors swap, so this reuses `khinchinK₀_summable_log`'s
series verbatim (term-by-term equal). -/
theorem gaussKuzmin_logsum_hasSum :
    HasSum (fun k : ℕ => (gaussMeasure (cfCylinder [k + 1])).toReal * Real.log ((k : ℝ) + 1))
      (Real.log khinchinK₀) := by
  have hfn := khinchinK₀_term_pos
  have hsum := khinchinK₀_summable_log
  have hprod := Real.hasProd_of_hasSum_log hfn hsum.hasSum
  have hlogK0 : Real.log khinchinK₀
      = ∑' k : ℕ, Real.log ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1)) := by
    rw [khinchinK₀, hprod.tprod_eq, Real.log_exp]
  have key : ∀ k : ℕ,
      (gaussMeasure (cfCylinder [k + 1])).toReal * Real.log ((k : ℝ) + 1)
        = Real.log ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1)) := by
    intro k
    rw [gaussMeasure_digit_cylinder (k + 1) (by omega),
      ENNReal.toReal_ofReal (Real.logb_nonneg (by norm_num)
        (le_add_of_nonneg_right (by positivity))),
      Real.log_rpow (by positivity)]
    push_cast
    simp only [Real.logb]
    ring
  rw [show (fun k : ℕ => (gaussMeasure (cfCylinder [k + 1])).toReal * Real.log ((k : ℝ) + 1))
      = (fun k : ℕ => Real.log ((1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) ^ Real.logb 2 ((k : ℝ) + 1)))
    from funext key, hlogK0]
  exact hsum.hasSum

/-- `Finset.Icc 1 K` sum reindexed to a `Finset.range K` sum shifted by one. -/
private lemma sum_Icc_one_eq_sum_range {β : Type*} [AddCommMonoid β] (F : ℕ → β) (K : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, F a = ∑ k ∈ Finset.range K, F (k + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 K), ih, Finset.sum_range_succ]

/-- The `K → ∞` limit of the truncated Gauss–Kuzmin log-average: the partial
sums `Σ_{a=1}^{K} γ([a])·log a → log K₀` (the target that
`xstar_log_digit_avg_truncated_tendsto` converges to for each fixed `K`, now
as `K → ∞`).  Reindexes `gaussKuzmin_logsum_hasSum`'s `range`-partial-sums to
`Finset.Icc 1 K`. -/
theorem gaussKuzmin_logsum_tendsto :
    Filter.Tendsto
      (fun K : ℕ => ∑ a ∈ Finset.Icc 1 K,
        (gaussMeasure (cfCylinder [a])).toReal * Real.log (a : ℝ))
      Filter.atTop (nhds (Real.log khinchinK₀)) := by
  have h := gaussKuzmin_logsum_hasSum.tendsto_sum_nat
  refine h.congr (fun K => ?_)
  rw [sum_Icc_one_eq_sum_range
    (fun a => (gaussMeasure (cfCylinder [a])).toReal * Real.log (a : ℝ)) K]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring

/-- **The Gauss–Kuzmin log-tail vanishes**: `Σ_{a>K} γ([a])·log a → 0` as
`K → ∞` (written as `log K₀ − Σ_{a≤K} γ([a])·log a`, the tail of the
convergent series `gaussKuzmin_logsum_hasSum`).  This is the `K`-selection
input for the Markov bound on the Khinchin log-tail bad zone: the bad zone
`{x : Σ_{i<n, digit>K} log(digit) > η·n}` has Gauss measure `≤ (1/η)·(this
tail)` by Markov + `integral_blockCount` (first moment only — the tail is
nonnegative, so no variance/Chebyshev is needed), which → 0 as `K → ∞`. -/
theorem gaussKuzmin_logtail_tendsto :
    Filter.Tendsto
      (fun K : ℕ => Real.log khinchinK₀
        - ∑ k ∈ Finset.range K,
            (gaussMeasure (cfCylinder [k + 1])).toReal * Real.log ((k : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  have hpartial := gaussKuzmin_logsum_hasSum.tendsto_sum_nat
  have h := (tendsto_const_nhds (x := Real.log khinchinK₀)).sub hpartial
  simpa using h

/-- **Elementary reduction**: `KhinchinTypical x` (the geometric mean of the
CF digits `→ K₀`) is equivalent to the corresponding `log`-average tending to
`log K₀` — the standard exp/log swap, using that every CF digit of an
irrational `x ∈ (0,1)` is `≥ 1 > 0` and `K₀ > 0`.  Isolates the actual
Khinchin content (matching the log-average against the Gauss–Kuzmin
frequencies) from this bookkeeping. -/
theorem khinchinTypical_iff_log_tendsto (x : ℝ) (hpos : ∀ i, 1 ≤ cfDigit x i) :
    KhinchinTypical x ↔
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * ((List.range n).map (fun i => Real.log (cfDigit x i : ℝ))).sum)
        Filter.atTop (nhds (Real.log khinchinK₀)) := by
  have hK0 : (0 : ℝ) < khinchinK₀ := khinchinK₀_pos
  have hdpos : ∀ i, (0 : ℝ) < (cfDigit x i : ℝ) := fun i => by
    exact_mod_cast lt_of_lt_of_le one_pos (hpos i)
  have hann : ∀ n : ℕ, (0 : ℝ) < ∏ i ∈ Finset.range n, (cfDigit x i : ℝ) := fun n =>
    Finset.prod_pos (fun i _ => hdpos i)
  have hgeomdef : ∀ n : ℕ,
      (∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ))
        > 0 := fun n => Real.rpow_pos_of_pos (hann n) _
  have hlogeq : ∀ n : ℕ,
      Real.log ((∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ)))
        = (1 / (n : ℝ)) * ((List.range n).map (fun i => Real.log (cfDigit x i : ℝ))).sum := by
    intro n
    rw [Real.log_rpow (hann n), Real.log_prod (fun i _ => (hdpos i).ne'),
      finset_sum_range_eq_list_sum]
  constructor
  · intro h
    have hlog : Filter.Tendsto
        (fun n => Real.log ((∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ))))
        Filter.atTop (nhds (Real.log khinchinK₀)) := h.log hK0.ne'
    exact hlog.congr hlogeq
  · intro h
    have hlog : Filter.Tendsto
        (fun n => Real.log ((∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ))))
        Filter.atTop (nhds (Real.log khinchinK₀)) := h.congr (fun n => (hlogeq n).symm)
    have hexp : Filter.Tendsto
        (fun n => Real.exp (Real.log ((∏ i ∈ Finset.range n, (cfDigit x i : ℝ)) ^ (1 / (n : ℝ)))))
        Filter.atTop (nhds (Real.exp (Real.log khinchinK₀))) :=
      (Real.continuous_exp.tendsto _).comp hlog
    rw [Real.exp_log hK0] at hexp
    refine hexp.congr (fun n => ?_)
    exact Real.exp_log (hgeomdef n)

/-! ## Step 2 (open): the log-average / frequency assembly — ROUTE SETTLED

The remaining crux: the empirical log-average `(1/n)·Σ_{i<n} log aᵢ →
log K₀`.  The `liminf ≥ log K₀` direction is free from CF-normality
(`xstar_cf_freq_tendsto` + `xstar_log_digit_avg_truncated_tendsto`); the
`limsup ≤ log K₀` direction is the genuine content and needs **uniform
tail control** of the log-digit average (no mass escaping to large digits).

**REFUTED route** (`44fb8bb`/`e018429` "route insight", now retracted —
`DIRECTION.md` 2026-08-26 review): the total-mass bound `wSched_log_sum_le`
(`Σ log aᵢ ≤ goodC·n`) does NOT suffice.  Quantitatively (PENDING_WORK
2026-08-24): via the complement split, `limsup(1/n)Σ_{aᵢ>K} log aᵢ ≤
goodC − Σ_{a≤K} γ([a])log a → goodC − log K₀`, and `goodC` is an unrelated
Markov constant with genuine slack over `log K₀`, so this floor never
reaches `0`.  Pattern-frequency data alone provably cannot close it either
(`KHINCHIN.md` "Both expansions at once" counterexample — density-zero
large-digit planting preserves all frequencies yet breaks the mean).

**CONFIRMED route** (the step-2 crux, now authorized per `DIRECTION.md`):
enforce the tail control *in the construction* by adding a Khinchin
log-concentration **bad zone** to the schedule's union-bound selection
(`exists_good_avoiding_bad`, `TBrick.lean`), **additively** — a
`logBadZone w n η := {x | |Σ_{i<n} log(digit_i) − n·log K₀| ≥ η·n}` whose
Gauss/Lebesgue measure is small by a **Chebyshev/variance** bound on
`Σ log aᵢ` under the existing γ-mixing machinery (`CFGammaMixing`,
`CFBlockFreq`), exactly as `cfBadZone` is handled for indicators but with
the observable `log a₁` in place of a cylinder indicator.  The moment
condition that bound needs, `E[(log a₁)²] = Σₐ γ([a])·(log a)² < ∞`, is
`summable_gaussKuzmin_logsq` above (proved this lap).  This is the ORIGINAL
`KHINCHIN.md` W6 digit-cap plan; the frozen headline is witness-existence
form precisely so a schedule extension discharges it (`Headline.lean` doc).
Invariant: additive only — no existing Tier-1 declaration modified, Tier-1
`#print axioms` stays `[propext, Classical.choice, Quot.sound]`. -/

/-- **Finite-truncation convergence** (real sub-piece of the step-2
assembly): for any fixed cutoff `K`, the `≤ K` slice of the empirical
log-digit average tends to the matching finite Gauss–Kuzmin sum. Direct
consequence of `xstar_cf_freq_tendsto` at each `a ∈ [1,K]` (finitely many
digit values), via `tendsto_finsetSum`. Does NOT yet connect to the full
empirical average `(1/n)·Σ_{i<n} log(digit i)` from
`xstar_log_digit_avg_tendsto` — that needs (a) the list-sum-by-value-count
identity `Σ_{i<n} log(digit i) = Σ_a countOccurrences [a] (cfPrefix n) ·
log a` and (b) the uniform tail control past `K`, both still open. -/
theorem xstar_log_digit_avg_truncated_tendsto (K : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) *
          ∑ a ∈ Finset.Icc 1 K, (countOccurrences [a] (cfPrefix n) : ℝ) * Real.log a)
      Filter.atTop
      (nhds (∑ a ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [a])).toReal * Real.log a)) := by
  have hterm : ∀ a ∈ Finset.Icc 1 K,
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * ((countOccurrences [a] (cfPrefix n) : ℝ) * Real.log a))
        Filter.atTop (nhds ((gaussMeasure (cfCylinder [a])).toReal * Real.log a)) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.1 ha).1
    have h := xstar_cf_freq_tendsto [a] (by simp) (by simpa using ha1)
    have h2 := h.mul_const (Real.log a)
    refine h2.congr (fun n => ?_)
    rw [cfPrefix]
    ring
  have hsum := tendsto_finsetSum (Finset.Icc 1 K) hterm
  refine hsum.congr (fun n => ?_)
  rw [Finset.mul_sum]

/-- Single-digit window count is the ordinary list `count`: `countOccurrences
[a] l = l.count a`. -/
theorem countOccurrences_singleton (a : ℕ) (l : List ℕ) :
    countOccurrences [a] l = l.count a := by
  induction l with
  | nil => simp [countOccurrences_nil]
  | cons b t ih =>
      rw [countOccurrences_cons, ih, List.count_cons]
      by_cases h : a = b
      · subst h; simp [List.isPrefixOf]
      · simp [List.isPrefixOf, h, Ne.symm h]

/-- **Log-tail = full minus low-truncation** (list form, by induction): for a
list `w` of positive digits, the total log-mass minus its `≤ K`
value-truncation equals the log-mass of the entries `> K`.  This is the
value-count bookkeeping that turns a bound on the tail log-mass into the
`xstar_log_tail_uniform` statement. -/
theorem logTail_list_eq (K : ℕ) (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    (w.map (fun a : ℕ => Real.log a)).sum
        - ∑ a ∈ Finset.Icc 1 K, (w.count a : ℝ) * Real.log a
      = (w.map (fun a : ℕ => if K < a then Real.log a else 0)).sum := by
  induction w with
  | nil => simp
  | cons b t ih =>
      have hb : 1 ≤ b := hpos b (List.mem_cons_self ..)
      have hpos' : ∀ a ∈ t, 1 ≤ a := fun a ha => hpos a (List.mem_cons_of_mem b ha)
      have hcount : ∑ a ∈ Finset.Icc 1 K, ((b :: t).count a : ℝ) * Real.log a
          = (∑ a ∈ Finset.Icc 1 K, (t.count a : ℝ) * Real.log a)
            + (if b ∈ Finset.Icc 1 K then Real.log b else 0) := by
        rw [← Finset.sum_ite_eq' (Finset.Icc 1 K) b (fun _ => Real.log b),
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [List.count_cons]
        simp only [beq_iff_eq]
        by_cases h : a = b
        · subst h; simp only [if_pos rfl]; push_cast; ring
        · rw [if_neg (fun hh => h hh.symm), if_neg h]; push_cast; ring
      rw [List.map_cons, List.sum_cons, hcount, List.map_cons, List.sum_cons]
      have hmem : (b ∈ Finset.Icc 1 K) ↔ ¬ (K < b) := by
        rw [Finset.mem_Icc]
        omega
      by_cases h : K < b
      · rw [if_pos h, if_neg (by rw [hmem]; simpa using h)]
        linarith [ih hpos']
      · rw [if_neg h, if_pos (by rw [hmem]; simpa using h)]
        linarith [ih hpos']

/-- **The tail bridge for `xstar`**: the difference inside `xstar_log_tail_uniform`
is exactly the empirical log-mass of digits `> K`.  Specializes
`logTail_list_eq` to `w = cfPrefix n` (positive CF digits), converting between
the `countOccurrences`/`Finset` bookkeeping and the list form. -/
theorem xstar_logTail_eq (K n : ℕ) :
    ((List.range n).map (fun i => Real.log (cfDigit xstar i : ℝ))).sum
        - ∑ a ∈ Finset.Icc 1 K, (countOccurrences [a] (cfPrefix n) : ℝ) * Real.log a
      = ∑ i ∈ Finset.range n,
          (if K < cfDigit xstar i then Real.log (cfDigit xstar i : ℝ) else 0) := by
  have hpos : ∀ a ∈ cfPrefix n, 1 ≤ a := by
    intro a ha
    rw [cfPrefix, List.mem_map] at ha
    obtain ⟨i, _, rfl⟩ := ha
    exact one_le_cfDigit xstar xstar_irrational xstar_mem_Ioo i
  have hcount : ∀ a, countOccurrences [a] (cfPrefix n) = (cfPrefix n).count a :=
    fun a => countOccurrences_singleton a (cfPrefix n)
  have hkey := logTail_list_eq K (cfPrefix n) hpos
  simp only [hcount]
  rw [show ((List.range n).map (fun i => Real.log (cfDigit xstar i : ℝ)))
      = (cfPrefix n).map (fun a : ℕ => Real.log a) by rw [cfPrefix, List.map_map]; rfl]
  rw [hkey, cfPrefix, List.map_map, finset_sum_range_eq_list_sum]
  rfl

/-! ## First-moment integral of the log-digit tail (Markov input, route A′)

The single-digit tail indicator `logTailFn K x = if K < cfDigit x 0 then
log(cfDigit x 0) else 0` integrates to EXACTLY the Gauss–Kuzmin log-tail
`log K₀ − Σ_{k<K} γ([k+1])·log(k+1)`, which `gaussKuzmin_logtail_tendsto`
already shows `→ 0`.  This is the first-moment computation `integral_blockCount`
generalizes (a Birkhoff-sum-style average against `gaussMeasure`), specialized
to a single step (`n = 1`) with the (unbounded, digit-valued) weight `log a`
instead of an indicator.  Route: split the tail sum by digit value into a
countable family of disjoint-cylinder indicators, swap `∫` with `∑'`
(`integral_tsum_of_summable_integral_norm`, license from `Summable`), then
collapse the resulting `tsum` via `hasSum_nat_add_iff'` against
`gaussKuzmin_logsum_hasSum`. -/

/-- Single digit-value indicator term: value `log(K+1+n)` on the cylinder
`[K+1+n]`, `0` elsewhere. -/
private noncomputable def logTailTerm (K n : ℕ) : ℝ → ℝ :=
  (cfCylinder [K + 1 + n]).indicator (fun _ => Real.log ((K : ℝ) + 1 + n))

/-- The single-digit tail indicator: `log(cfDigit x 0)` when the digit exceeds
`K`, else `0`. -/
private noncomputable def logTailFn (K : ℕ) : ℝ → ℝ :=
  fun x => if K < cfDigit x 0 then Real.log (cfDigit x 0 : ℝ) else 0

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

/-- **First-moment tail integral**: `∫ logTailFn K dγ = log K₀ − Σ_{k<K}
γ([k+1])·log(k+1)`, the Gauss–Kuzmin log-tail. -/
theorem integral_logTailFn_eq (K : ℕ) :
    ∫ x, logTailFn K x ∂gaussMeasure
      = Real.log khinchinK₀
          - ∑ k ∈ Finset.range K, (gaussMeasure (cfCylinder [k + 1])).toReal
              * Real.log ((k : ℝ) + 1) := by
  set G : ℕ → ℝ := fun k => (gaussMeasure (cfCylinder [k + 1])).toReal * Real.log ((k : ℝ) + 1)
    with hGdef
  have hGsum : HasSum G (Real.log khinchinK₀) := by
    simpa [hGdef] using gaussKuzmin_logsum_hasSum
  -- `G (n + K) = ∫ logTailTerm K n` (and its `norm`), the reindexing identity
  -- used for both the integrability input and the final `tsum` collapse.
  have hGshift : ∀ n : ℕ, G (n + K) =
      (gaussMeasure (cfCylinder [K + 1 + n])).toReal * Real.log (((K : ℝ) + n) + 1) := by
    intro n
    simp only [hGdef]
    have hidx : n + K + 1 = K + 1 + n := by omega
    rw [hidx]
    congr 1
    push_cast
    ring
  -- Pointwise a.e. collapse of the tsum of terms to `logTailFn`.
  have htsum_eq : ∀ᵐ x ∂gaussMeasure, ∑' n, logTailTerm K n x = logTailFn K x := by
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
  -- Integrability + summable-norm inputs for the tsum-integral swap.
  have hInt : ∀ n, Integrable (logTailTerm K n) gaussMeasure := logTailTerm_integrable K
  have hSumNorm : Summable (fun n => ∫ x, ‖logTailTerm K n x‖ ∂gaussMeasure) := by
    have heq : (fun n => ∫ x, ‖logTailTerm K n x‖ ∂gaussMeasure) = fun n => G (n + K) := by
      funext n
      rw [integral_norm_logTailTerm, hGshift]
    rw [heq]
    exact (summable_nat_add_iff K).2 hGsum.summable
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSumNorm
  -- Assemble: `∑' n, ∫ term = ∫ ∑' n, term = ∫ logTailFn K = LHS`; the middle
  -- `∑'` collapses via `hasSum_nat_add_iff'` against `hGsum`.
  have hlhs : ∑' n, ∫ x, logTailTerm K n x ∂gaussMeasure = ∑' n, G (n + K) := by
    refine tsum_congr fun n => ?_
    rw [integral_logTailTerm, hGshift]
  have htail : HasSum (fun n => G (n + K))
      (Real.log khinchinK₀ - ∑ k ∈ Finset.range K, G k) :=
    (hasSum_nat_add_iff' K).2 hGsum
  rw [hlhs, htail.tsum_eq] at hswap
  rw [← MeasureTheory.integral_congr_ae htsum_eq, hswap]

/-- **The tail integral vanishes as `K → ∞`**: `∫ logTailFn K dγ → 0`, the
`K`-selection input for the Markov bound powering `logBadZone` (route B′).
Immediate from `integral_logTailFn_eq` + `gaussKuzmin_logtail_tendsto`. -/
theorem integral_logTailFn_tendsto :
    Filter.Tendsto (fun K : ℕ => ∫ x, logTailFn K x ∂gaussMeasure)
      Filter.atTop (nhds 0) := by
  refine gaussKuzmin_logtail_tendsto.congr (fun K => ?_)
  rw [integral_logTailFn_eq]

/-- **Uniform log-digit tail control** (the sole SCHEDULE-DEPENDENT crux of
Tier 2, now isolated).  For every `ε > 0` there is a cutoff `K₀` such that for
ALL cutoffs `K ≥ K₀` and ALL prefix lengths `n`, the empirical log-average
`(1/n)·Σ_{i<n} log aᵢ` differs from its `≤ K`-truncation
`(1/n)·Σ_{a≤K} count[a]·log a` by at most `ε`.  Equivalently (via
`xstar_logTail_eq`): the average log-mass carried by digits `> K`,
`(1/n)·Σ_{i<n, aᵢ>K} log aᵢ`, is `≤ ε` uniformly in `n`.  This is exactly
what pattern frequencies + the `goodC` total-mass bound provably CANNOT give
(`DIRECTION.md` route note); it is delivered by the W6 log-concentration bad
zone in the schedule (a MARKOV first-moment bound — the tail is nonnegative —
with input `gaussKuzmin_logtail_tendsto`).  DISCLOSED `sorry`: the analytic
assembly above reduces the whole Tier-2 headline to this one statement;
`xstar_logTail_eq` further reduces it to bounding the nonnegative empirical
tail, which the additive `logBadZone` in the schedule construction delivers. -/
theorem xstar_log_tail_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ,
      |(1 / (n : ℝ)) * ((List.range n).map (fun i => Real.log (cfDigit xstar i : ℝ))).sum
          - (1 / (n : ℝ)) * ∑ a ∈ Finset.Icc 1 K,
              (countOccurrences [a] (cfPrefix n) : ℝ) * Real.log a|
        ≤ ε := by
  sorry

/-- **Target of the Tier-2 assembly** (`Headline.lean`'s obligation via
`khinchinTypical_iff_log_tendsto`): `xstar`'s empirical CF log-digit average
tends to `log khinchinK₀`.  PROVED modulo the single schedule-dependent crux
`xstar_log_tail_uniform`: a `3ε` interchange combining the finite-truncation
convergence (`xstar_log_digit_avg_truncated_tendsto`, for each fixed `K`), the
`K → ∞` limit of the truncated Gauss–Kuzmin target (`gaussKuzmin_logsum_tendsto`),
and the uniform tail control. -/
theorem xstar_log_digit_avg_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) * ((List.range n).map (fun i => Real.log (cfDigit xstar i : ℝ))).sum)
      Filter.atTop (nhds (Real.log khinchinK₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / 3 := by linarith
  obtain ⟨K₀, htail⟩ := xstar_log_tail_uniform hδ
  obtain ⟨K_g, hgauss⟩ :=
    (Metric.tendsto_atTop.1 gaussKuzmin_logsum_tendsto) (ε / 3) hδ
  set K := max K₀ K_g with hKdef
  have hKtail : K₀ ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKg : K_g ≤ K := by rw [hKdef]; exact le_max_right _ _
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 (xstar_log_digit_avg_truncated_tendsto K)) (ε / 3) hδ
  refine ⟨N, fun n hn => ?_⟩
  have h1 := htail K hKtail n
  have h2 := hN n hn
  have h3 := hgauss K hKg
  rw [Real.dist_eq] at h2 h3 ⊢
  set A := (1 / (n : ℝ)) * ((List.range n).map (fun i => Real.log (cfDigit xstar i : ℝ))).sum
  set B := (1 / (n : ℝ)) * ∑ a ∈ Finset.Icc 1 K,
      (countOccurrences [a] (cfPrefix n) : ℝ) * Real.log a
  set C := ∑ a ∈ Finset.Icc 1 K, (gaussMeasure (cfCylinder [a])).toReal * Real.log a
  have htri : |A - Real.log khinchinK₀|
      ≤ |A - B| + |B - C| + |C - Real.log khinchinK₀| := by
    have t1 := abs_sub_le A B (Real.log khinchinK₀)
    have t2 := abs_sub_le B C (Real.log khinchinK₀)
    linarith
  linarith [htri, h1, h2, h3]

/-- **`xstar` is Khinchin-typical** (the geometric mean of its CF digits →
`K₀`), modulo the schedule-dependent crux `xstar_log_tail_uniform`.  Converts
`xstar_log_digit_avg_tendsto` through the elementary reduction
`khinchinTypical_iff_log_tendsto` (digit positivity from `one_le_cfDigit` at
the irrational `xstar ∈ (0,1)`).  This is the Tier-2 conjunct that, together
with the LOCKED Tier-1 legs, discharges the frozen headline
`exists_absolutely_normal_cf_normal_khinchin` — the last assembly step is a
layering refactor (the frozen `KhinchinTypical`/`khinchinK₀` defs live in
`Headline.lean`, which this module imports; moving them upstream lets
`Headline.lean` close its `sorry`). -/
theorem xstar_khinchinTypical : KhinchinTypical xstar := by
  have hpos : ∀ i, 1 ≤ cfDigit xstar i :=
    fun i => one_le_cfDigit xstar xstar_irrational xstar_mem_Ioo i
  rw [khinchinTypical_iff_log_tendsto xstar hpos]
  exact xstar_log_digit_avg_tendsto

end NormalNumbers
