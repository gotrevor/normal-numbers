/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFPsiPin

/-!
# Total variation of the CF branch weights in the log metric

`PENDING_WORK.md` (2026-09-27) isolates the one ingredient still owed for the crux of
Vandehey 2017 Theorem 1.1, `VandeheyState.stateHorizonIntegral_pin`: the Doeblin minorization
`VandeheyState.stateStepIter_ge_word` contracts the **state** direction of the refined transfer
operator, but the elementary two-sided Doeblin estimate leaves a term
`β · Σ_t osc_τ (Φ(t,·))`, so the **tail-parameter** oscillation inside a fixed state must decay
too.  `CFPsiPin.stepOp_logLipschitz` proves that for a *single* `φ`, but its Abel-resummed
`B`-series does not survive the passage to a `k`-indexed family `ψ k = Φ(δ d (k+1), ·)`.

This file supplies the replacement, and it is *sharper* than an Abel resummation: because
`Σ_k w_τ(k) = 1` for every `τ`, the `B`-series
`Σ_k (w_τ(k) − w_{τ'}(k)) · ψ k (·)` may have **any constant subtracted from `ψ`**, so it is
bounded by `½ · osc(ψ) · Σ_k |w_τ(k) − w_{τ'}(k)|`.  The whole family question therefore
collapses to a single scalar quantity: the **ℓ¹ modulus of continuity of the weight sequence in
the log metric**, `tsum_abs_stepWeight_sub_le`.

## The mechanism

Write `a = 1 + τ`, `b = 1 + τ'` with `b ≤ a` in `[1,2]`.  Then

* `w_τ(k) − w_{τ'}(k) = (a − b)(k² + k − ab) / ((k+a)(k+1+a)(k+b)(k+1+b))` — an exact
  factorization (`stepWeight_sub_eq`).  Its sign is the sign of `k² + k − ab`, so for `k ≥ 2`
  (where `k² + k ≥ 6 > 4 ≥ ab`) **every term is nonnegative**.
* Since `Σ_k (w_τ(k) − w_{τ'}(k)) = 0`, the tail `Σ_{k ≥ 2}` equals `−Δ₀ − Δ₁`, whence
  `Σ_k |Δ_k| ≤ 2|Δ₀| + 2|Δ₁|`: the ℓ¹ norm is carried entirely by the two lowest branches.
* `|Δ₀| ≤ ¼ d(τ,τ')` and `|Δ₁| ≤ (1/30) d(τ,τ')`, both from
  `Real.le_log_one_add_of_nonneg` (`log t ≥ 2(t−1)/(t+1)`) plus an algebraic inequality —
  `(a−1)(b−1) ≥ 0` for the first, a two-case `nlinarith` for the second.

Total: `Σ_k |w_τ(k) − w_{τ'}(k)| ≤ (17/30)·d(τ,τ') ≤ (3/5)·d(τ,τ')`.

The constant matters: the joint (state × tail) contraction needs `½ · (3/5) · log 2 < ¼`, i.e.
`3/5 < 1/(2 log 2) ≈ 0.7213`, and `17/30 ≈ 0.567` clears it.
-/

namespace NormalNumbers

open Real

namespace WeightTV

/-! ## The exact difference -/

/-- `w_t(k) − w_{t'}(k) = (a−b)(k²+k−ab)/((k+a)(k+1+a)(k+b)(k+1+b))` with `a = 1+t`, `b = 1+t'`. -/
lemma stepWeight_sub_eq {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (k : ℕ) :
    stepWeight t k - stepWeight t' k
      = (t - t') * ((k : ℝ) ^ 2 + k - (1 + t) * (1 + t')) /
          ((((k : ℝ) + 1 + t) * ((k : ℝ) + 2 + t)) * (((k : ℝ) + 1 + t') * ((k : ℝ) + 2 + t'))) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have d1 : ((k : ℝ) + 1 + t) ≠ 0 := by positivity
  have d2 : ((k : ℝ) + 2 + t) ≠ 0 := by positivity
  have d3 : ((k : ℝ) + 1 + t') ≠ 0 := by positivity
  have d4 : ((k : ℝ) + 2 + t') ≠ 0 := by positivity
  rw [stepWeight, stepWeight]
  field_simp
  ring

/-- For `k ≥ 2` the weight is monotone in the tail parameter on `[0,1]`. -/
lemma stepWeight_mono_two_le {t t' : ℝ} (ht' : 0 ≤ t') (htt' : t' ≤ t) (ht1 : t ≤ 1)
    {k : ℕ} (hk2 : 2 ≤ k) :
    0 ≤ stepWeight t k - stepWeight t' k := by
  have ht : (0 : ℝ) ≤ t := ht'.trans htt'
  have ht1' : t' ≤ 1 := htt'.trans' le_rfl |>.trans ht1
  have hk : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  rw [stepWeight_sub_eq ht ht' k]
  have hnum : 0 ≤ (k : ℝ) ^ 2 + k - (1 + t) * (1 + t') := by nlinarith
  have hden : 0 < (((k : ℝ) + 1 + t) * ((k : ℝ) + 2 + t)) *
      (((k : ℝ) + 1 + t') * ((k : ℝ) + 2 + t')) := by positivity
  positivity

/-! ## The log-metric bound on the two lowest branches -/

/-- The midpoint log inequality in the form used here:
`2(t − t')/(2 + t + t') ≤ log(1+t) − log(1+t')`. -/
lemma two_mul_sub_div_le_log_sub {t t' : ℝ} (ht' : 0 ≤ t') (htt' : t' ≤ t) :
    2 * (t - t') / (2 + t + t') ≤ Real.log (1 + t) - Real.log (1 + t') := by
  have hb : (0 : ℝ) < 1 + t' := by linarith
  set x : ℝ := (t - t') / (1 + t') with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hone : (1 : ℝ) + x = (1 + t) / (1 + t') := by
    rw [hx]; field_simp; ring
  have hlog : Real.log (1 + t) - Real.log (1 + t') = Real.log (1 + x) := by
    rw [hone, Real.log_div (by linarith) hb.ne']
  rw [hlog]
  refine le_trans ?_ (Real.le_log_one_add_of_nonneg hx0)
  have hxv : 2 * x / (x + 2) = 2 * (t - t') / (2 + t + t') := by
    rw [hx]; field_simp; ring
  exact hxv.ge

/-- `|Δ₀| ≤ ¼ · d(t,t')`:  `w_·(0) = 1/(2+·)`, and `2(a+b) ≤ (1+a)(1+b)` on `a,b ≥ 1`. -/
lemma abs_stepWeight_zero_sub_le {t t' : ℝ} (ht' : 0 ≤ t') (htt' : t' ≤ t) (ht1 : t ≤ 1) :
    |stepWeight t 0 - stepWeight t' 0| ≤
      (1 / 4) * (Real.log (1 + t) - Real.log (1 + t')) := by
  have ht : (0 : ℝ) ≤ t := ht'.trans htt'
  have hw : ∀ s : ℝ, 0 ≤ s → stepWeight s 0 = 1 / (2 + s) := by
    intro s hs
    rw [stepWeight]
    have h1 : (0 : ℝ) < 1 + s := by linarith
    field_simp
    ring
  rw [hw t ht, hw t' ht']
  have hd : (1 : ℝ) / (2 + t) - 1 / (2 + t') = -((t - t') / ((2 + t) * (2 + t'))) := by
    field_simp; ring
  rw [hd, abs_neg, abs_of_nonneg (by positivity)]
  have hlog := two_mul_sub_div_le_log_sub ht' htt'
  have hkey : (t - t') / ((2 + t) * (2 + t')) ≤ (1 / 4) * (2 * (t - t') / (2 + t + t')) := by
    rw [div_le_iff₀ (by positivity)]
    have h : (1 / 4) * (2 * (t - t') / (2 + t + t')) * ((2 + t) * (2 + t'))
        = (t - t') * ((2 + t) * (2 + t')) / (2 * (2 + t + t')) := by
      field_simp; ring
    rw [h, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr htt') (mul_nonneg ht ht')]
  refine hkey.trans ?_
  exact mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- `|Δ₁| ≤ (1/30) · d(t,t')`:  the exact numerator is `(a−b)(2−ab)` with `a,b ∈ [1,2]`, and
`15(a+b)|2−ab| ≤ (1+a)(2+a)(1+b)(2+b)` there. -/
lemma abs_stepWeight_one_sub_le {t t' : ℝ} (ht' : 0 ≤ t') (htt' : t' ≤ t) (ht1 : t ≤ 1) :
    |stepWeight t 1 - stepWeight t' 1| ≤
      (1 / 30) * (Real.log (1 + t) - Real.log (1 + t')) := by
  have ht : (0 : ℝ) ≤ t := ht'.trans htt'
  have ht1' : t' ≤ 1 := htt'.trans ht1
  have hsub := stepWeight_sub_eq ht ht' 1
  norm_num at hsub
  have hden : 0 < ((2 : ℝ) + t) * (3 + t) * (((2 : ℝ) + t') * (3 + t')) := by
    positivity
  have hlog := two_mul_sub_div_le_log_sub ht' htt'
  -- reduce to the algebraic inequality
  have hgoal : |stepWeight t 1 - stepWeight t' 1|
      ≤ (1 / 30) * (2 * (t - t') / (2 + t + t')) := by
    rw [hsub, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have habs : |(t - t') * (2 - (1 + t) * (1 + t'))|
        = (t - t') * |2 - (1 + t) * (1 + t')| := by
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr htt')]
    rw [habs]
    have hrw : (1 : ℝ) / 30 * (2 * (t - t') / (2 + t + t')) *
        (((2 : ℝ) + t) * (3 + t) * (((2 : ℝ) + t') * (3 + t')))
        = (t - t') * (((2 + t) * (3 + t) * ((2 + t') * (3 + t'))) / (15 * (2 + t + t'))) := by
      field_simp; ring
    rw [hrw]
    refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr htt')
    rw [le_div_iff₀ (by positivity)]
    rcases le_total ((1 + t) * (1 + t')) 2 with hc | hc
    · rw [abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg ht ht', sq_nonneg (t - t'), sq_nonneg (t + t'),
        mul_nonneg (mul_nonneg ht ht') (add_nonneg ht ht'), sq_nonneg (t * t')]
    · rw [abs_of_nonpos (by linarith)]
      nlinarith [mul_nonneg ht ht', sq_nonneg (t - t'), sq_nonneg (t + t'),
        mul_nonneg (mul_nonneg ht ht') (add_nonneg ht ht'), sq_nonneg (t * t'),
        mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht1')]
  refine hgoal.trans ?_
  exact mul_le_mul_of_nonneg_left hlog (by norm_num)

/-! ## The ℓ¹ modulus of continuity -/

/-- Ordered half. -/
lemma tsum_abs_stepWeight_sub_le_aux {t t' : ℝ} (ht' : 0 ≤ t') (htt' : t' ≤ t) (ht1 : t ≤ 1) :
    ∑' k : ℕ, |stepWeight t k - stepWeight t' k|
      ≤ (3 / 5) * (Real.log (1 + t) - Real.log (1 + t')) := by
  have ht : (0 : ℝ) ≤ t := ht'.trans htt'
  set D : ℕ → ℝ := fun k => stepWeight t k - stepWeight t' k with hD
  have hS : Summable D := (summable_stepWeight ht).sub (summable_stepWeight ht')
  have hzero : ∑' k, D k = 0 := by
    rw [hD, (summable_stepWeight ht).tsum_sub (summable_stepWeight ht'),
      tsum_stepWeight ht, tsum_stepWeight ht', sub_self]
  have hpos2 : ∀ k : ℕ, 0 ≤ D (k + 2) :=
    fun k => stepWeight_mono_two_le ht' htt' ht1 (by omega)
  have hS2 : Summable (fun k : ℕ => D (k + 2)) := (summable_nat_add_iff 2).mpr hS
  have hSabs : Summable (fun k : ℕ => |D k|) := by
    rw [← summable_nat_add_iff 2]
    refine hS2.congr fun k => ?_
    exact (abs_of_nonneg (hpos2 k)).symm
  -- peel two terms off each series
  have hpeel : ∀ (f : ℕ → ℝ), Summable f →
      ∑' k, f k = f 0 + f 1 + ∑' k, f (k + 2) := by
    intro f hf
    have h1 : ∑' k, f k = f 0 + ∑' k, f (k + 1) := hf.tsum_eq_zero_add
    have h2 : ∑' k, f (k + 1) = f 1 + ∑' k, f (k + 1 + 1) :=
      ((summable_nat_add_iff 1).mpr hf).tsum_eq_zero_add
    have h3 : (∑' k : ℕ, f (k + 1 + 1)) = ∑' k : ℕ, f (k + 2) := rfl
    rw [h1, h2, h3, add_assoc]
  have hA := hpeel D hS
  have hB := hpeel (fun k => |D k|) hSabs
  have htail : ∑' k, D (k + 2) = -(D 0) - D 1 := by
    rw [hzero] at hA; linarith
  have htailabs : ∑' k : ℕ, |D (k + 2)| = ∑' k : ℕ, D (k + 2) :=
    tsum_congr fun k => abs_of_nonneg (hpos2 k)
  have hfinal : ∑' k, |D k| = |D 0| + |D 1| - D 0 - D 1 := by
    rw [hB]
    rw [show (∑' k : ℕ, |D (k + 2)|) = ∑' k : ℕ, D (k + 2) from htailabs, htail]
    ring
  have h0 := abs_stepWeight_zero_sub_le ht' htt' ht1
  have h1' := abs_stepWeight_one_sub_le ht' htt' ht1
  have hn0 : -(D 0) ≤ |D 0| := neg_le_abs _
  have hn1 : -(D 1) ≤ |D 1| := neg_le_abs _
  have hd0 : |D 0| ≤ (1 / 4) * (Real.log (1 + t) - Real.log (1 + t')) := h0
  have hd1 : |D 1| ≤ (1 / 30) * (Real.log (1 + t) - Real.log (1 + t')) := h1'
  rw [hfinal]
  have : |D 0| + |D 1| - D 0 - D 1 ≤ 2 * |D 0| + 2 * |D 1| := by linarith
  refine this.trans ?_
  have hlogpos : 0 ≤ Real.log (1 + t) - Real.log (1 + t') := by
    have := Real.log_le_log (by linarith : (0:ℝ) < 1 + t') (by linarith : (1:ℝ) + t' ≤ 1 + t)
    linarith
  linarith

/-- **The ℓ¹ modulus of continuity of the CF branch weights in the log metric.**

`Σ_k |w_τ(k) − w_{τ'}(k)| ≤ (3/5)·|log(1+τ) − log(1+τ')|` for `τ, τ' ∈ [0,1]`.

Combined with `Σ_k w_τ(k) = 1` (so any constant may be subtracted from the integrand) this is
what replaces the Abel resummation of `CFPsiPin.stepOp_logLipschitz` when the integrand is a
`k`-indexed FAMILY rather than a single function — exactly the situation created by the
state-refined operator `VandeheyState.stateStepOp`. -/
theorem tsum_abs_stepWeight_sub_le {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    ∑' k : ℕ, |stepWeight t k - stepWeight t' k|
      ≤ (3 / 5) * |Real.log (1 + t) - Real.log (1 + t')| := by
  have habs : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |Real.log (1 + b) - Real.log (1 + a)|
      = Real.log (1 + b) - Real.log (1 + a) := by
    intro a b ha hab
    refine abs_of_nonneg ?_
    have := Real.log_le_log (by linarith : (0:ℝ) < 1 + a) (by linarith : (1:ℝ) + a ≤ 1 + b)
    linarith
  rcases le_total t' t with h | h
  · rw [habs t' t ht'.1 h]
    exact tsum_abs_stepWeight_sub_le_aux ht'.1 h ht.2
  · rw [abs_sub_comm (Real.log (1 + t)), habs t t' ht.1 h]
    have := tsum_abs_stepWeight_sub_le_aux ht.1 h ht'.2
    refine le_trans (le_of_eq ?_) this
    exact tsum_congr fun k => abs_sub_comm _ _

end WeightTV

end NormalNumbers
