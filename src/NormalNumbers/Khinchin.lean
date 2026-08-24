/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline
import NormalNumbers.CFDigitLaw

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

open Filter

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

/-- **Target of the Tier-2 assembly** (`Headline.lean:136`'s obligation via
`khinchinTypical_iff_log_tendsto`): `xstar`'s empirical CF log-digit average
tends to `log khinchinK₀`. See the module docstring above for the attack
decomposition; not yet attempted beyond the route confirmation. -/
theorem xstar_log_digit_avg_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) * ((List.range n).map (fun i => Real.log (cfDigit xstar i : ℝ))).sum)
      Filter.atTop (nhds (Real.log khinchinK₀)) := by
  sorry

end NormalNumbers
