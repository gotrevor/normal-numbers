/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SK: `WidthFreqBound` is Chebyshev on ONE nonnegative scalar

S7-DB charged the current stall age to the height ledger.  That is a *lower* bound on the height,
so it says long stall ⟹ narrow state — **not** the converse, and the converse is false: a single
huge input digit narrows the state at once, with no stall at all.  The honest reduction therefore
goes through the ledger's running slack itself, and it is cleaner than the stall route.

    slack Φ x m  :=  log (runState Φ x (m+2)).d  −  log √(|det Φ|/6)   ≥ 0

(nonnegative by `d_runState_ge`, S7-HT — "the output can never get ahead of the input").  The
whole geometry collapses into one line:

    `width_ge_of_slack_le` :   slack m ≤ S   ⟹   e^(−2S) ≤ width (runState Φ x (m+2))

with an **absolute** exponent — the `|det Φ|` in the height floor and the `|det Φ|` in
`width ≍ |det Φ|/d²` cancel exactly.  Chebyshev on a nonnegative sequence then gives

    widthBadCount Φ x (e^(−2S)) q  ≤  #{m < q : slack m > S}  ≤  (1/S)·Σ_{m<q} slack m ,

so `WidthFreqBound` follows from two scalar inputs and nothing else
(`widthFreqBound_of_meanSlack`):

* **MeanSlack** — `Σ_{m<q} slack m ≤ A·q` eventually (bounded Cesàro average of the log-height);
* **ClockLinear** — `c·q ≤ runClock (q+2)` eventually (Vandehey's Lemma 6.1).

Picking `S = A/(c·ε)` and `η = e^(−2S)` closes it.  No geometry, no cells, no state space, and no
stall combinatorics: one nonnegative scalar walk, reflected at `√(|det Φ|/6)`.
-/
import NormalNumbers.VandeheyS7Debt
import NormalNumbers.VandeheyS7Class

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- The running slack of the height ledger. -/
noncomputable def slack (Φ : MapState) (x : ℝ) (m : ℕ) : ℝ :=
  Real.log ((runState Φ x (m + 2)).d) - Real.log (Real.sqrt (|Φ.det| / 6))

lemma slack_nonneg (Φ : MapState) (x : ℝ) (m : ℕ) : 0 ≤ slack Φ x m := by
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hs : (0:ℝ) < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
  have h := d_runState_ge Φ x m
  have := Real.log_le_log hs h
  simp only [slack]
  linarith

/-- **The one line.**  Small slack forces a width floor, with an absolute exponent. -/
theorem width_ge_of_slack_le (Φ : MapState) (x : ℝ) (m : ℕ) {S : ℝ} (hS : slack Φ x m ≤ S) :
    Real.exp (-(2 * S)) ≤ (runState Φ x (m + 2)).width := by
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hs : (0:ℝ) < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (|Φ.det| / 6) ^ 2 = |Φ.det| / 6 := Real.sq_sqrt (by positivity)
  have hdpos : (0:ℝ) < (runState Φ x (m + 2)).d := (runState Φ x (m + 2)).hd
  set R : ℝ := Real.sqrt (|Φ.det| / 6) * Real.exp S with hR
  have hRpos : 0 < R := by positivity
  have hd : (runState Φ x (m + 2)).d ≤ R := by
    rw [← Real.log_le_log_iff hdpos hRpos, hR, Real.log_mul hs.ne' (Real.exp_ne_zero S),
      Real.log_exp]
    simp only [slack] at hS
    linarith
  have hRsq : R ^ 2 = (|Φ.det| / 6) * Real.exp (2 * S) := by
    rw [hR, mul_pow, hsq, ← Real.exp_nat_mul]
    ring_nf
  have hEq : |Φ.det| / (6 * R ^ 2) = Real.exp (-(2 * S)) := by
    rw [hRsq, Real.exp_neg]
    have hexp : (0:ℝ) < Real.exp (2 * S) := Real.exp_pos _
    field_simp
  exact width_ge_of_d_le hRpos hd (le_of_eq hEq.symm)

/-! ## Chebyshev -/

/-- **Chebyshev on the slack.**  Narrow times are times of large slack. -/
theorem widthBadCount_le_sum_slack (Φ : MapState) (x : ℝ) {S : ℝ} (hS : 0 < S) (q : ℕ) :
    widthBadCount Φ x (Real.exp (-(2 * S))) q ≤ (1 / S) * ∑ m ∈ range q, slack Φ x m := by
  classical
  set T := (range q).filter (fun m => S < slack Φ x m) with hT
  have hcard : widthBadCount Φ x (Real.exp (-(2 * S))) q ≤ (T.card : ℝ) := by
    have hTcard : (T.card : ℝ) = ∑ m ∈ range q, (if S < slack Φ x m then (1:ℝ) else 0) := by
      rw [hT, ← Finset.sum_filter]
      simp
    rw [widthBadCount, hTcard]
    refine Finset.sum_le_sum fun m _ => ?_
    by_cases hw : Real.exp (-(2 * S)) ≤ (runState Φ x (m + 2)).width
    · rw [if_pos hw]
      by_cases hs : S < slack Φ x m
      · rw [if_pos hs]; norm_num
      · rw [if_neg hs]
    · rw [if_neg hw]
      have hs : S < slack Φ x m := by
        by_contra hcon
        push_neg at hcon
        exact hw (width_ge_of_slack_le Φ x m hcon)
      rw [if_pos hs]
      rcases emitIndic_eq_zero_or_one Φ x (m + 2) with h | h <;> rw [h] <;> norm_num
  have hcheb : S * (T.card : ℝ) ≤ ∑ m ∈ range q, slack Φ x m := by
    have h1 : S * (T.card : ℝ) ≤ ∑ m ∈ T, slack Φ x m := by
      have : ∑ _m ∈ T, S = S * (T.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      rw [← this]
      refine Finset.sum_le_sum fun m hm => ?_
      have := (Finset.mem_filter.mp (hT ▸ hm)).2
      linarith
    have h2 : ∑ m ∈ T, slack Φ x m ≤ ∑ m ∈ range q, slack Φ x m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun m _ _ => slack_nonneg Φ x m)
    linarith
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hS]
  calc widthBadCount Φ x (Real.exp (-(2 * S))) q * S ≤ (T.card : ℝ) * S :=
        mul_le_mul_of_nonneg_right hcard hS.le
    _ = S * (T.card : ℝ) := by ring
    _ ≤ ∑ m ∈ range q, slack Φ x m := hcheb

/-! ## The reduction -/

/-- **S7-SK.**  `WidthFreqBound` from two scalar inputs: a bounded Cesàro average of the
log-height, and a linear clock. -/
theorem exists_eventually_widthBad_le (Φ : MapState) (x : ℝ) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q)
    (hclock : ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ q in atTop,
      widthBadCount Φ x η q ≤ ε * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
  set S : ℝ := A / (ε * c) + 1 with hSdef
  have hS : 0 < S := by
    have : 0 ≤ A / (ε * c) := by positivity
    linarith
  refine ⟨Real.exp (-(2 * S)), Real.exp_pos _, ?_⟩
  filter_upwards [hmean, hclock] with q hm hcl
  have hq : (0:ℝ) ≤ (q : ℝ) := by positivity
  have h1 := widthBadCount_le_sum_slack Φ x hS q
  have h2 : (1 / S) * ∑ m ∈ range q, slack Φ x m ≤ (1 / S) * (A * q) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have hAS : A / S ≤ ε * c := by
    have hεc : (0:ℝ) < ε * c := mul_pos hε hc
    rw [div_le_iff₀ hS]
    have hkey : ε * c * S = A + ε * c := by
      rw [hSdef]; field_simp
    rw [hkey]; linarith
  have h3 : (1 / S) * (A * q) ≤ (ε * c) * q := by
    have : (1 / S) * (A * q) = (A / S) * q := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hAS hq
  have h4 : (ε * c) * q ≤ ε * ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    have : (ε * c) * q = ε * (c * q) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hcl hε.le
  linarith

end MapState

section Audit

#print axioms MapState.slack_nonneg
#print axioms MapState.width_ge_of_slack_le
#print axioms MapState.widthBadCount_le_sum_slack
#print axioms MapState.exists_eventually_widthBad_le

end Audit

end NormalNumbers.VandeheyS7
