/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinSubpowerAux

/-!
# Non-normality below the sub-power weight, `c > 3` (personal-c5, 2026-10-25)

Statements are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never edit them.  The
paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Heavy neighbours", and the
plan is in `EB-SUBPOWER-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinSubpower

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinRandom

/-- The sub-power weight `(log m)^{−ln 2} · exp(−ln 2 · √(c·u·log u))`, with `u = log log m`.  Where
`c·u·log u < 0` (small `m`), `Real.sqrt` returns `0` and the weight is `(log m)^{−ln 2}`. -/
noncomputable def subpowerWeight (c : ℝ) (m : ℕ) : ℝ :=
  Real.rpow (Real.log m) (-Real.log 2) *
    Real.exp (-(Real.log 2) * Real.sqrt (c * Real.log (Real.log m) * Real.log (Real.log (Real.log m))))

lemma subpowerWeight_nonneg (c : ℝ) (m : ℕ) : 0 ≤ subpowerWeight c m := by
  unfold subpowerWeight
  apply mul_nonneg (Real.rpow_nonneg ?_ _) (Real.exp_pos _).le
  cases m with
  | zero => simp
  | succ m =>
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))

/-- Past the harmless small range, the sub-power weight decreases with its integer argument. -/
lemma subpowerWeight_antitone {c : ℝ} (hc : 0 ≤ c) {m d : ℕ}
    (hm : Real.exp 1 ≤ Real.log m) (hmd : m ≤ d) :
    subpowerWeight c d ≤ subpowerWeight c m := by
  have hm1 : 1 < m := by
    by_contra h
    have hmle : m ≤ 1 := by omega
    interval_cases m <;> norm_num at hm <;> have := Real.exp_pos 1 <;> linarith
  have hd1 : 1 < d := hm1.trans_le hmd
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm1)
  have hlogd_pos : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast hd1)
  have hlog : Real.log (m : ℝ) ≤ Real.log (d : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hmpos)
      (Set.mem_Ioi.mpr hdpos) (by exact_mod_cast hmd)
  have hUone : 1 ≤ Real.log (Real.log (m : ℝ)) := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (Real.exp_pos 1))
      (Set.mem_Ioi.mpr hlogm_pos) hm
  have hU : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (d : ℝ)) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hlogm_pos)
      (Set.mem_Ioi.mpr hlogd_pos) hlog
  have hUd_pos : 0 < Real.log (Real.log (d : ℝ)) := zero_lt_one.trans_le (hUone.trans hU)
  have hV : Real.log (Real.log (Real.log (m : ℝ))) ≤
      Real.log (Real.log (Real.log (d : ℝ))) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (zero_lt_one.trans_le hUone))
      (Set.mem_Ioi.mpr hUd_pos) hU
  have hA : c * Real.log (Real.log (m : ℝ)) * Real.log (Real.log (Real.log (m : ℝ))) ≤
      c * Real.log (Real.log (d : ℝ)) * Real.log (Real.log (Real.log (d : ℝ))) := by
    rw [mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hc
    exact mul_le_mul hU hV (Real.log_nonneg hUone) (zero_le_one.trans (hUone.trans hU))
  have hsqrt := Real.sqrt_le_sqrt hA
  have hpow : Real.rpow (Real.log (d : ℝ)) (-Real.log 2) ≤
      Real.rpow (Real.log (m : ℝ)) (-Real.log 2) :=
    Real.rpow_le_rpow_of_nonpos hlogm_pos hlog (neg_nonpos.mpr (Real.log_pos one_lt_two).le)
  have hexp : Real.exp (-(Real.log 2) *
      Real.sqrt (c * Real.log (Real.log (d : ℝ)) * Real.log (Real.log (Real.log (d : ℝ))))) ≤
      Real.exp (-(Real.log 2) *
        Real.sqrt (c * Real.log (Real.log (m : ℝ)) * Real.log (Real.log (Real.log (m : ℝ))))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hsqrt (neg_nonpos.mpr (Real.log_pos one_lt_two).le)
  unfold subpowerWeight
  exact mul_le_mul hpow hexp (Real.exp_pos _).le (Real.rpow_nonneg hlogm_pos.le _)

/-- On every block from `ℓ = 3` onward, the weight is bounded by its left-end value. -/
lemma subpowerWeight_block_le (c : ℝ) (hc : 0 ≤ c) (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (d : ℕ)
    (hdlo : dyadicExpCutoff ℓ < d) :
    subpowerWeight c d ≤ subpowerWeight c (dyadicExpCutoff ℓ) := by
  apply subpowerWeight_antitone hc
  · rw [log_dyadicExpCutoff]
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ ℓ := by
      calc
        (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
        _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by exact_mod_cast hℓ)
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    calc
      Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ 8 * (1 / 2 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ℓ * Real.log 2 :=
        mul_le_mul hpow hlog (by norm_num) (by positivity)
  · exact hdlo.le

/-- The generic smooth-divisor estimate specialized to one block of the frozen sub-power weight. -/
lemma subpowerWeight_block_rpow_sum_le
    (c s : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hs1 : s ≤ 1)
    (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        Real.rpow (weightedDivisorBlockMass (subpowerWeight c) ℓ n) s) ≤
      Real.rpow (subpowerWeight c (dyadicExpCutoff ℓ)) s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  exact weightedDivisorBlockMass_rpow_sum_le (subpowerWeight c)
    (subpowerWeight c (dyadicExpCutoff ℓ)) s (subpowerWeight_nonneg c)
    (subpowerWeight_nonneg c _) hs hs1 ℓ N
    (fun d hdlo _ => subpowerWeight_block_le c hc ℓ hℓ d hdlo)

/-- Per-block counting Chernoff bound for the frozen sub-power weight. -/
lemma subpowerWeight_block_large_card_mul_rpow_le
    (c Y s : ℝ) (hc : 0 ≤ c) (hY : 0 ≤ Y) (hs : 0 < s) (hs1 : s ≤ 1)
    (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (N : ℕ) :
    (((Finset.Icc 1 N).filter
        (fun n => Y < weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) *
          Real.rpow Y s ≤
      Real.rpow (subpowerWeight c (dyadicExpCutoff ℓ)) s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  exact weightedDivisorBlockMass_large_card_mul_rpow_le (subpowerWeight c)
    (subpowerWeight c (dyadicExpCutoff ℓ)) Y s (subpowerWeight_nonneg c)
    (subpowerWeight_nonneg c _) hY hs hs1 ℓ N
    (fun d hdlo _ => subpowerWeight_block_le c hc ℓ hℓ d hdlo)

/-- **Target (negative side, elementary): non-normal below the sub-power weight at `c > 3`.**
Marginal-only, with no literature input.  The proof has three steps.
* The log-moment criterion: if `Σ_j dens{μ_M > ε b^{j/2}} → 0` as `M → ∞`, uniformly in `N`, then
  the series is non-normal.
* A per-dyadic-block Chernoff bound with `s_ℓ = √(c log u/u)/ln 2`, using the uniform moment bound
  for `τ(n_y)^s`.
* The block sum `Σ_ℓ ℓ^{1/2 − c/2}/√(log ℓ)`, finite iff `c > 3`.
The heuristic threshold is `c = 1`.  Reaching it needs a maximal inequality inside geometric blocks,
i.e. the Kubilius model.  This is strictly stronger than `ebRandom_ae_not_normal`.  Confidence 80%. -/
theorem ebRandom_ae_not_normal_subpower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c C : ℝ) (hc : 3 < c)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinSubpower
