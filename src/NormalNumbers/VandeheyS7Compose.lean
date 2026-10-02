/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CP: the §7 front has TWO hypotheses

S7-GR bounds the stall clock affinely by the slack (`min (stallAge (n+2)) n ≤ 1 + 2·slack n/log 2`)
and S7-RS turns a bounded *mean* stall age into a linear output clock.  Composing them removes
`ClockLinear` — Vandehey's Lemma 6.1 — from the front's signature entirely:

* `meanStallAge_of_meanSlack` — `MeanSlack ⟹ Σ_{n<q} stallAge n ≤ (4 + 2A/log 2)·q`.
  The index shift is the only real content: `stallAge (n+2) ≤ 2 + min (stallAge (n+2)) n` because
  `stallAge m ≤ m`, so the capped bound of S7-GR is an uncapped one up to `+2`.
* `clockLinear_of_meanSlack` — `MeanSlack ⟹ ∃ c > 0, ∀ᶠ q, c·q ≤ runClock (q+2)`.
* `blockAverageBound_of_meanSlack` — the front with `ClassFreqBound` and `MeanSlack` and nothing
  else (the `Tendsto` side condition also follows, from the linear clock).
-/
import NormalNumbers.VandeheyS7Reset
import NormalNumbers.VandeheyS7Front

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ}

/-- The cap in S7-GR costs at most `2`: `stallAge m ≤ m`, so if the cap bites then the stall age
is at most `n + 2`. -/
lemma stallAge_le_capped (Φ : MapState) (x : ℝ) (n : ℕ) :
    stallAge Φ x (n + 2) ≤ 2 + min (stallAge Φ x (n + 2)) n := by
  have h := stallAge_le_self Φ x (n + 2)
  omega

/-- **The mean stall age is bounded by the mean slack.** -/
theorem meanStallAge_of_meanSlack (Φ : MapState) (x : ℝ)
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {A : ℝ} (hA : 0 ≤ A)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q) :
    ∀ᶠ q in atTop, ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ)
      ≤ (4 + 2 * A / Real.log 2) * q := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hmean, eventually_ge_atTop 2] with q hm hq2
  -- shifted bound, termwise
  have hterm : ∀ n : ℕ, ((stallAge Φ x (n + 2) : ℕ) : ℝ) ≤ 3 + 2 * slack Φ x n / Real.log 2 := by
    intro n
    set a := min (stallAge Φ x (n + 2)) n with hadef
    have h1 := stallAge_le_slack Φ hx n
    rw [← hadef] at h1
    have hc : stallAge Φ x (n + 2) ≤ 2 + a := stallAge_le_capped Φ x n
    have hc' : ((stallAge Φ x (n + 2) : ℕ) : ℝ) ≤ 2 + (a : ℝ) := by
      have h := Nat.cast_le (α := ℝ) |>.mpr hc
      simpa using h
    linarith
  -- the shifted sum dominates the sum, up to the first two terms
  obtain ⟨p, hp⟩ : ∃ p, q = 2 + p := ⟨q - 2, by omega⟩
  have hsplit : ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ)
      = ∑ n ∈ range 2, ((stallAge Φ x n : ℕ) : ℝ)
        + ∑ n ∈ range p, ((stallAge Φ x (2 + n) : ℕ) : ℝ) := by
    rw [hp]; exact Finset.sum_range_add _ 2 p
  have hfirst : ∑ n ∈ range 2, ((stallAge Φ x n : ℕ) : ℝ) ≤ 1 := by
    have h0 : stallAge Φ x 0 = 0 := by simp [stallAge]
    have h1 : stallAge Φ x 1 ≤ 1 := stallAge_le_self Φ x 1
    have h1' : ((stallAge Φ x 1 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
    simp [Finset.sum_range_succ, h0]
    linarith
  have hshift : ∑ n ∈ range p, ((stallAge Φ x (2 + n) : ℕ) : ℝ)
      ≤ ∑ n ∈ range q, ((stallAge Φ x (n + 2) : ℕ) : ℝ) := by
    have hpq : p ≤ q := by omega
    have hsub : range p ⊆ range q := fun i hi =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hpq)
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun n => ((stallAge Φ x (n + 2) : ℕ) : ℝ))
      hsub (fun n _ _ => Nat.cast_nonneg _)
    calc ∑ n ∈ range p, ((stallAge Φ x (2 + n) : ℕ) : ℝ)
        = ∑ n ∈ range p, ((stallAge Φ x (n + 2) : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Nat.add_comm]
      _ ≤ _ := this
  have hbound : ∑ n ∈ range q, ((stallAge Φ x (n + 2) : ℕ) : ℝ)
      ≤ ∑ n ∈ range q, (3 + 2 * slack Φ x n / Real.log 2) :=
    Finset.sum_le_sum fun n _ => hterm n
  have hrhs : ∑ n ∈ range q, (3 + 2 * slack Φ x n / Real.log 2)
      = 3 * q + (2 / Real.log 2) * ∑ n ∈ range q, slack Φ x n := by
    have hcong : ∀ n ∈ range q, (3 + 2 * slack Φ x n / Real.log 2)
        = 3 + (2 / Real.log 2) * slack Φ x n := fun n _ => by ring
    rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hslack : (2 / Real.log 2) * ∑ n ∈ range q, slack Φ x n
      ≤ (2 / Real.log 2) * (A * q) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have hq1 : (1:ℝ) ≤ (q : ℝ) := by
    have : (2:ℕ) ≤ q := hq2
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast this
    linarith
  have hfinal : (2 / Real.log 2) * (A * q) = (2 * A / Real.log 2) * q := by ring
  linarith [hsplit.le, hsplit.ge]

/-- **S7-CP.**  `ClockLinear` is a consequence of `MeanSlack`. -/
theorem clockLinear_of_meanSlack (Φ : MapState) (x : ℝ)
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) {A : ℝ} (hA : 0 ≤ A)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine clockLinear_of_meanStallAge Φ x (C := 4 + 2 * A / Real.log 2) (by positivity) ?_
  exact meanStallAge_of_meanSlack Φ x hx hA hmean

/-- **The §7 front, with two hypotheses.** -/
theorem blockAverageBound_of_meanSlack (Φ : MapState) (x : ℝ) (w : List ℕ) {B A : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) (hA : 0 ≤ A)
    (hCF : ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∀ {M : ℕ} (net : StateNet Φ x η ρ M),
      ClassFreqBound net w B)
    (hmean : ∀ᶠ q in atTop, ∑ m ∈ range q, slack Φ x m ≤ A * q) :
    BlockAverageBound B x (runClock Φ x) (fun n j => mapBlockSet (runState Φ x n) w j) := by
  obtain ⟨c, hc, hclin⟩ := clockLinear_of_meanSlack Φ x hx hA hmean
  have hclock : Tendsto (fun q => ((runClock Φ x (q + 2) : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' _ hclin ?_
    exact Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  exact blockAverageBound_of_scalar Φ x w hB hA hc hclock hCF hmean hclin

end MapState

section Audit

#print axioms MapState.meanStallAge_of_meanSlack
#print axioms MapState.clockLinear_of_meanSlack
#print axioms MapState.blockAverageBound_of_meanSlack

end Audit

end NormalNumbers.VandeheyS7
