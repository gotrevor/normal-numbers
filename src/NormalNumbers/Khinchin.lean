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

/-- **Khinchin's constant is a genuine positive real** (its defining `tprod`
converges to a positive value; the K₀-exponent series `Σₐ log₂(a)·log(1 +
1/(a(a+2)))` is summable by comparison with `log(a)/a^{3/2}`, in the style of
`CFDigitLaw.lean`'s `summable_digitLog`).  Needed for the log/exp swap in
`khinchinTypical_iff_log_tendsto` below; not yet attempted. -/
theorem khinchinK₀_pos : 0 < khinchinK₀ := by
  sorry

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
