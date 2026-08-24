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

end NormalNumbers
