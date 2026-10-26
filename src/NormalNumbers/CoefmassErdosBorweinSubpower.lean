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

/-! ### Normalization of the variable block moment -/

/-- The fractional-moment exponent on block `ℓ`; multiplying it by `log 2` gives the natural
exponential coordinate `blockSigma`. -/
noncomputable def subpowerBlockS (c : ℝ) (ℓ : ℕ) : ℝ :=
  blockSigma c (blockLogLog ℓ) / Real.log 2

lemma tendsto_subpowerBlockS_zero (c : ℝ) :
    Tendsto (subpowerBlockS c) atTop (nhds 0) := by
  change Tendsto (fun ℓ => blockSigma c (blockLogLog ℓ) / Real.log 2) atTop (nhds 0)
  simpa only [zero_div] using
    (tendsto_blockSigma_blockLogLog_zero c).div_const (Real.log 2)

lemma subpowerBlockS_mul_log_two (c : ℝ) (ℓ : ℕ) :
    subpowerBlockS c ℓ * Real.log 2 = blockSigma c (blockLogLog ℓ) := by
  unfold subpowerBlockS
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

lemma two_rpow_subpowerBlockS (c : ℝ) (ℓ : ℕ) :
    (2 : ℝ) ^ subpowerBlockS c ℓ =
      Real.exp (blockSigma c (blockLogLog ℓ)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  simpa only [mul_comm] using subpowerBlockS_mul_log_two c ℓ

lemma subpowerBlockS_pos (c : ℝ) (hc : 0 < c) (ℓ : ℕ)
    (hu : 1 < blockLogLog ℓ) : 0 < subpowerBlockS c ℓ := by
  unfold subpowerBlockS blockSigma
  exact div_pos (Real.sqrt_pos.mpr (div_pos
    (mul_pos hc (Real.log_pos hu)) (zero_lt_one.trans hu)))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))

lemma subpowerBlockS_nonneg (c : ℝ) (ℓ : ℕ) : 0 ≤ subpowerBlockS c ℓ := by
  unfold subpowerBlockS
  exact div_nonneg (Real.sqrt_nonneg _) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The fixed slack used at `c > 3`.  It leaves exactly the exponent `(c+3)/4`. -/
noncomputable def subpowerRho (c : ℝ) : ℝ := (c - 3) / (4 * c)

/-- Polynomial decay exponent left by the variable Chernoff estimate. -/
noncomputable def subpowerAlpha (c : ℝ) : ℝ := (c + 3) / 4

/-- A `p`-series exponent strictly between `1` and `subpowerAlpha c - 1/2`. -/
noncomputable def subpowerP (c : ℝ) : ℝ := (c + 5) / 8

/-- Half of the spare exponent between the Chernoff decay and the final `p`-series. -/
noncomputable def subpowerDelta (c : ℝ) : ℝ := (c - 3) / 16

lemma subpowerRho_pos {c : ℝ} (hc : 3 < c) : 0 < subpowerRho c := by
  unfold subpowerRho
  positivity

lemma subpowerRho_lt_half {c : ℝ} (hc : 3 < c) : subpowerRho c < 1 / 2 := by
  unfold subpowerRho
  have hc0 : 0 < c := by linarith
  apply (div_lt_iff₀ (by positivity : 0 < 4 * c)).2
  linarith

lemma subpower_slack_mul (c : ℝ) (hc : 0 < c) :
    (1 / 2 - subpowerRho c) * c = subpowerAlpha c := by
  unfold subpowerRho subpowerAlpha
  field_simp
  ring

lemma one_lt_subpowerP {c : ℝ} (hc : 3 < c) : 1 < subpowerP c := by
  unfold subpowerP
  linarith

lemma subpowerP_lt_alpha_sub_half {c : ℝ} (hc : 3 < c) :
    subpowerP c < subpowerAlpha c - 1 / 2 := by
  unfold subpowerP subpowerAlpha
  linarith

lemma subpowerDelta_pos {c : ℝ} (hc : 3 < c) : 0 < subpowerDelta c := by
  unfold subpowerDelta
  linarith

lemma subpower_exponent_budget {c : ℝ} (hc : 3 < c) :
    -subpowerAlpha c + subpowerDelta c + 1 / 2 < -subpowerP c := by
  unfold subpowerAlpha subpowerDelta subpowerP
  linarith

/-- The one-block moment factor after removing the averaging length `N`. -/
noncomputable def subpowerBlockMomentFactor (c : ℝ) (ℓ : ℕ) : ℝ :=
  Real.rpow (subpowerWeight c (dyadicExpCutoff ℓ)) (subpowerBlockS c ℓ) *
    (Real.exp (((2 : ℝ) ^ subpowerBlockS c ℓ - 1) *
        Erdos67.PrimeEstimates.mertensBound + 1) *
      Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ))
        ((2 : ℝ) ^ subpowerBlockS c ℓ - 1))

lemma subpowerBlockMomentFactor_nonneg (c : ℝ) (ℓ : ℕ) :
    0 ≤ subpowerBlockMomentFactor c ℓ := by
  unfold subpowerBlockMomentFactor
  exact mul_nonneg
    (Real.rpow_nonneg (subpowerWeight_nonneg c _) _)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _))

/-- The left-end weight raised to its variable block exponent, in the exact exponential form used
by the Chernoff cancellation. -/
lemma subpowerWeight_cutoff_rpow_subpowerBlockS (c : ℝ) (ℓ : ℕ) :
    Real.rpow (subpowerWeight c (dyadicExpCutoff ℓ)) (subpowerBlockS c ℓ) =
      Real.exp (-blockSigma c (blockLogLog ℓ) * blockLogLog ℓ -
        blockSigma c (blockLogLog ℓ) *
          Real.sqrt (c * blockLogLog ℓ * Real.log (blockLogLog ℓ))) := by
  have hlogcut : 0 < Real.log (dyadicExpCutoff ℓ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < dyadicExpCutoff ℓ by
      exact lt_of_lt_of_le (by omega) (dyadicExpCutoff_two_le ℓ)))
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold subpowerWeight
  change (((Real.log (dyadicExpCutoff ℓ : ℝ)) ^ (-Real.log 2) *
      Real.exp (-(Real.log 2) *
        Real.sqrt (c * Real.log (Real.log (dyadicExpCutoff ℓ : ℝ)) *
          Real.log (Real.log (Real.log (dyadicExpCutoff ℓ : ℝ)))))) ^
        (subpowerBlockS c ℓ)) = _
  rw [Real.rpow_def_of_pos (mul_pos
    (Real.rpow_pos_of_pos hlogcut (-Real.log 2)) (Real.exp_pos _))]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hlogcut (-Real.log 2)))
    (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_rpow hlogcut, Real.log_exp]
  rw [show Real.log (Real.log (dyadicExpCutoff ℓ : ℝ)) = blockLogLog ℓ by rfl]
  congr 1
  rw [← subpowerBlockS_mul_log_two c ℓ]
  ring

/-- The non-constant part of the smooth-divisor moment bound is exactly the exponent controlled by
`chernoffExponent_blockSigma_le_slack`, plus two bounded Euler-product terms. -/
lemma subpowerBlockMomentFactor_eq_exp (c : ℝ) (ℓ : ℕ) :
    subpowerBlockMomentFactor c ℓ =
      Real.exp
        (blockLogLog ℓ *
              (Real.exp (blockSigma c (blockLogLog ℓ)) - 1 -
                blockSigma c (blockLogLog ℓ)) -
            blockSigma c (blockLogLog ℓ) *
              Real.sqrt (c * blockLogLog ℓ * Real.log (blockLogLog ℓ)) +
          (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) * Real.log 2 +
          (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) *
            Erdos67.PrimeEstimates.mertensBound + 1) := by
  unfold subpowerBlockMomentFactor
  have hlognext : 0 < Real.log (dyadicExpCutoff (ℓ + 1) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < dyadicExpCutoff (ℓ + 1) by
      exact lt_of_lt_of_le (by omega) (dyadicExpCutoff_two_le (ℓ + 1))))
  rw [subpowerWeight_cutoff_rpow_subpowerBlockS]
  rw [two_rpow_subpowerBlockS]
  have hrpowNext :
      Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ))
          (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) =
        Real.exp (blockLogLog (ℓ + 1) *
          (Real.exp (blockSigma c (blockLogLog ℓ)) - 1)) := by
    change (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ) ^
        (Real.exp (blockSigma c (blockLogLog ℓ)) - 1)) = _
    rw [Real.rpow_def_of_pos hlognext]
    rfl
  rw [hrpowNext]
  rw [blockLogLog_succ]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- A uniform constant absorbing the bounded Euler-product terms in the block moment. -/
noncomputable def subpowerMomentConstant : ℝ :=
  Real.exp ((Real.exp 1 - 1) *
    (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1)

lemma subpowerMomentConstant_pos : 0 < subpowerMomentConstant := by
  exact Real.exp_pos _

/-- Eventually the complete one-block moment factor has polynomial decay
`(log log cutoff)^{-(c+3)/4}`.  This is the exact normalization step where the variable exponent
cancels the critical `(log d)^{-log 2}` contribution. -/
lemma eventually_subpowerBlockMomentFactor_le {c : ℝ} (hc : 3 < c) :
    ∀ᶠ ℓ : ℕ in atTop,
      subpowerBlockMomentFactor c ℓ ≤
        subpowerMomentConstant * Real.rpow (blockLogLog ℓ) (-subpowerAlpha c) := by
  have hρ0 : 0 < subpowerRho c := subpowerRho_pos hc
  have hρhalf : subpowerRho c < 1 / 2 := subpowerRho_lt_half hc
  have hσ : ∀ᶠ ℓ : ℕ in atTop,
      blockSigma c (blockLogLog ℓ) < subpowerRho c :=
    (tendsto_blockSigma_blockLogLog_zero c).eventually_lt_const hρ0
  have hu : ∀ᶠ ℓ : ℕ in atTop, 1 ≤ blockLogLog ℓ :=
    tendsto_blockLogLog_atTop.eventually_ge_atTop 1
  filter_upwards [hσ, hu] with ℓ hσ hu
  have hc0 : 0 < c := by linarith
  have hσ0 : 0 ≤ blockSigma c (blockLogLog ℓ) := Real.sqrt_nonneg _
  have hσ1 : blockSigma c (blockLogLog ℓ) ≤ 1 := by linarith
  have hcore := chernoffExponent_blockSigma_le_slack c (blockLogLog ℓ)
    (subpowerRho c) hc0.le hu hρhalf hσ.le
  have hcore' :
      blockLogLog ℓ *
            (Real.exp (blockSigma c (blockLogLog ℓ)) - 1 -
              blockSigma c (blockLogLog ℓ)) -
          blockSigma c (blockLogLog ℓ) *
            Real.sqrt (c * blockLogLog ℓ * Real.log (blockLogLog ℓ)) ≤
        -subpowerAlpha c * Real.log (blockLogLog ℓ) := by
    calc
      _ ≤ -(1 / 2 - subpowerRho c) * c * Real.log (blockLogLog ℓ) := hcore
      _ = -((1 / 2 - subpowerRho c) * c) * Real.log (blockLogLog ℓ) := by ring
      _ = _ := by rw [subpower_slack_mul c hc0]
  let q : ℝ := Real.exp (blockSigma c (blockLogLog ℓ)) - 1
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr (by simpa using Real.exp_le_exp.mpr hσ0)
  have hq1 : q ≤ Real.exp 1 - 1 := by
    dsimp [q]
    linarith [Real.exp_le_exp.mpr hσ1]
  have hrest :
      q * Real.log 2 + q * Erdos67.PrimeEstimates.mertensBound + 1 ≤
        (Real.exp 1 - 1) *
          (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1 := by
    calc
      q * Real.log 2 + q * Erdos67.PrimeEstimates.mertensBound + 1 ≤
          q * Real.log 2 + q * |Erdos67.PrimeEstimates.mertensBound| + 1 := by
        gcongr
        exact le_abs_self _
      _ = q * (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1 := by ring
      _ ≤ (Real.exp 1 - 1) *
          (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1 := by
        gcongr
  rw [subpowerBlockMomentFactor_eq_exp]
  have hfull :
      blockLogLog ℓ *
            (Real.exp (blockSigma c (blockLogLog ℓ)) - 1 -
              blockSigma c (blockLogLog ℓ)) -
          blockSigma c (blockLogLog ℓ) *
            Real.sqrt (c * blockLogLog ℓ * Real.log (blockLogLog ℓ)) +
        (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) * Real.log 2 +
        (Real.exp (blockSigma c (blockLogLog ℓ)) - 1) *
          Erdos67.PrimeEstimates.mertensBound + 1 ≤
        -subpowerAlpha c * Real.log (blockLogLog ℓ) +
          ((Real.exp 1 - 1) *
            (Real.log 2 + |Erdos67.PrimeEstimates.mertensBound|) + 1) := by
    change _ + q * Real.log 2 + q * Erdos67.PrimeEstimates.mertensBound + 1 ≤ _
    linarith
  have hrpow : Real.rpow (blockLogLog ℓ) (-subpowerAlpha c) =
      Real.exp (Real.log (blockLogLog ℓ) * (-subpowerAlpha c)) := by
    change blockLogLog ℓ ^ (-subpowerAlpha c) = _
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hu)]
  rw [subpowerMomentConstant, hrpow]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert hfull using 1 <;> ring

lemma eventually_subpowerBlock_parameters {c : ℝ} (hc : 3 < c) :
    ∀ᶠ ℓ : ℕ in atTop,
      6 ≤ ℓ ∧
      1 ≤ Real.log (blockLogLog ℓ) ∧
      0 < subpowerBlockS c ℓ ∧
      subpowerBlockS c ℓ ≤ 1 ∧
      2 * subpowerBlockS c ℓ ≤ subpowerDelta c ∧
      blockSigma c (blockLogLog ℓ) ≤ 1 := by
  have hδ : 0 < subpowerDelta c / 2 := by positivity [subpowerDelta_pos hc]
  have hsδ : ∀ᶠ ℓ : ℕ in atTop, subpowerBlockS c ℓ < subpowerDelta c / 2 :=
    (tendsto_subpowerBlockS_zero c).eventually_lt_const hδ
  have hs1 : ∀ᶠ ℓ : ℕ in atTop, subpowerBlockS c ℓ < 1 :=
    (tendsto_subpowerBlockS_zero c).eventually_lt_const zero_lt_one
  have hσ1 : ∀ᶠ ℓ : ℕ in atTop, blockSigma c (blockLogLog ℓ) < 1 :=
    (tendsto_blockSigma_blockLogLog_zero c).eventually_lt_const zero_lt_one
  have hu : ∀ᶠ ℓ : ℕ in atTop, Real.exp 1 ≤ blockLogLog ℓ :=
    tendsto_blockLogLog_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [eventually_ge_atTop 6, hu, hsδ, hs1, hσ1] with ℓ hℓ hu hsδ hs1 hσ1
  have hu1 : 1 < blockLogLog ℓ := (by linarith [Real.exp_one_gt_two] : 1 < Real.exp 1).trans_le hu
  have hlog : 1 ≤ Real.log (blockLogLog ℓ) := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (Real.exp_pos 1))
      (Set.mem_Ioi.mpr (zero_lt_one.trans hu1)) hu
  exact ⟨hℓ, hlog, subpowerBlockS_pos c (by linarith) ℓ hu1, hs1.le,
    (by linarith), hσ1.le⟩

lemma subpowerBlockThresholdFactor_le (c A : ℝ) (hA : 0 < A) (ℓ : ℕ)
    (hs0 : 0 ≤ subpowerBlockS c ℓ) (hs1 : subpowerBlockS c ℓ ≤ 1)
    (hsδ : 2 * subpowerBlockS c ℓ ≤ subpowerDelta c) :
    Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) ≤
      max 1 A⁻¹ * Real.rpow ((ℓ : ℝ) + 2) (subpowerDelta c) := by
  have halloc0 : 0 ≤ blockAllocation ℓ := (blockAllocation_pos ℓ).le
  have hsplit :
      Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) =
        Real.rpow A (-subpowerBlockS c ℓ) *
          Real.rpow (blockAllocation ℓ) (-subpowerBlockS c ℓ) := by
    change (A * blockAllocation ℓ) ^ (-subpowerBlockS c ℓ) = _
    exact Real.mul_rpow hA.le halloc0
  rw [hsplit]
  exact mul_le_mul
    (rpow_neg_le_max_one_inv A (subpowerBlockS c ℓ) hA hs0 hs1)
    (blockAllocation_rpow_neg_le ℓ (subpowerBlockS c ℓ) (subpowerDelta c) hs0 hsδ)
    (Real.rpow_nonneg (by positivity) _)
    (le_trans zero_le_one (le_max_left _ _))

lemma subpowerBlockShiftGeomFactor_le (c : ℝ) (hc : 0 < c) (ℓ : ℕ) (hℓ : 6 ≤ ℓ)
    (hlog : 1 ≤ Real.log (blockLogLog ℓ))
    (hs0 : 0 < subpowerBlockS c ℓ)
    (hσ1 : blockSigma c (blockLogLog ℓ) ≤ 1) :
    (1 - Real.rpow 2 (-subpowerBlockS c ℓ / 2))⁻¹ ≤
      (4 / Real.sqrt c) * Real.rpow ((ℓ : ℝ) + 2) (1 / 2) := by
  have hu0 : 0 < blockLogLog ℓ :=
    (by positivity : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4).trans_le
      (blockLogLog_ge_quarter_add ℓ hℓ)
  have hu : 1 ≤ blockLogLog ℓ := by
    have hlog0 : 0 < Real.log (blockLogLog ℓ) := zero_lt_one.trans_le hlog
    exact (Real.log_pos_iff hu0.le).mp hlog0 |>.le
  have hσ0 : 0 < blockSigma c (blockLogLog ℓ) := by
    rw [← subpowerBlockS_mul_log_two c ℓ]
    exact mul_pos hs0 (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hrpow : Real.rpow 2 (-subpowerBlockS c ℓ / 2) =
      Real.exp (-blockSigma c (blockLogLog ℓ) / 2) := by
    change (2 : ℝ) ^ (-subpowerBlockS c ℓ / 2) = _
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [← subpowerBlockS_mul_log_two c ℓ]
    ring
  have hinv := one_sub_exp_neg_half_inv_le
    (blockSigma c (blockLogLog ℓ)) hσ0 hσ1
  have hσinv := blockSigma_inv_le_sqrt_div_sqrt c (blockLogLog ℓ) hc hu hlog
  have husqrt : Real.sqrt (blockLogLog ℓ) ≤ Real.sqrt ((ℓ : ℝ) + 2) := by
    apply Real.sqrt_le_sqrt
    exact (blockLogLog_le_natCast ℓ).trans (by linarith)
  rw [hrpow]
  calc
    (1 - Real.exp (-blockSigma c (blockLogLog ℓ) / 2))⁻¹ ≤
        4 / blockSigma c (blockLogLog ℓ) := hinv
    _ = 4 * (blockSigma c (blockLogLog ℓ))⁻¹ := by field_simp
    _ ≤ 4 * (Real.sqrt (blockLogLog ℓ) / Real.sqrt c) := by gcongr
    _ ≤ 4 * (Real.sqrt ((ℓ : ℝ) + 2) / Real.sqrt c) := by gcongr
    _ = (4 / Real.sqrt c) * Real.rpow ((ℓ : ℝ) + 2) (1 / 2) := by
      have hsqrtpow : Real.rpow ((ℓ : ℝ) + 2) (1 / 2) = Real.sqrt ((ℓ : ℝ) + 2) := by
        change ((ℓ : ℝ) + 2) ^ (1 / 2 : ℝ) = _
        exact (Real.sqrt_eq_rpow _).symm
      rw [hsqrtpow]
      ring

/-- Per-block majorant after summing all geometric shift thresholds. -/
noncomputable def subpowerBlockShiftMajorant (c A : ℝ) (ℓ : ℕ) : ℝ :=
  subpowerBlockMomentFactor c ℓ *
    Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) *
      (1 - Real.rpow 2 (-subpowerBlockS c ℓ / 2))⁻¹

lemma subpowerBlockShiftMajorant_nonneg (c A : ℝ) (hA : 0 ≤ A) (ℓ : ℕ) :
    0 ≤ subpowerBlockShiftMajorant c A ℓ := by
  have hs0 := subpowerBlockS_nonneg c ℓ
  have hgeom : 0 ≤ (1 - Real.rpow 2 (-subpowerBlockS c ℓ / 2))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
  unfold subpowerBlockShiftMajorant
  exact mul_nonneg
    (mul_nonneg (subpowerBlockMomentFactor_nonneg c ℓ)
      (Real.rpow_nonneg (mul_nonneg hA (blockAllocation_pos ℓ).le) _)) hgeom

noncomputable def subpowerSeriesConstant (c A : ℝ) : ℝ :=
  subpowerMomentConstant * Real.rpow 4 (subpowerAlpha c) *
    max 1 A⁻¹ * (4 / Real.sqrt c)

/-- Threshold assigned to block `ℓ` at geometric shift `j`. -/
noncomputable def subpowerBlockThreshold (A : ℝ) (ℓ j : ℕ) : ℝ :=
  A * blockAllocation ℓ * Real.rpow 2 ((j : ℝ) / 2)

lemma subpowerBlockThreshold_pos (A : ℝ) (hA : 0 < A) (ℓ j : ℕ) :
    0 < subpowerBlockThreshold A ℓ j := by
  unfold subpowerBlockThreshold
  exact mul_pos (mul_pos hA (blockAllocation_pos ℓ))
    (Real.rpow_pos_of_pos (by norm_num) _)

lemma subpowerBlockThreshold_rpow_neg (c A : ℝ) (hA : 0 < A) (ℓ j : ℕ) :
    Real.rpow (subpowerBlockThreshold A ℓ j) (-subpowerBlockS c ℓ) =
      Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) *
        (Real.rpow 2 (-subpowerBlockS c ℓ / 2)) ^ j := by
  have hbase : 0 ≤ A * blockAllocation ℓ :=
    mul_nonneg hA.le (blockAllocation_pos ℓ).le
  unfold subpowerBlockThreshold
  change (A * blockAllocation ℓ * (2 ^ ((j : ℝ) / 2))) ^ (-subpowerBlockS c ℓ) = _
  rw [Real.mul_rpow hbase (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (j : ℝ) / 2 * (-subpowerBlockS c ℓ) =
      (-subpowerBlockS c ℓ / 2) * (j : ℝ) by ring]
  exact Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) _ j

lemma subpowerWeight_block_large_card_le_factor
    (c Y : ℝ) (hc : 0 ≤ c) (hY : 0 < Y)
    (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    (hs : 0 < subpowerBlockS c ℓ) (hs1 : subpowerBlockS c ℓ ≤ 1) (N : ℕ) :
    (((Finset.Icc 1 N).filter
        (fun n => Y < weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
      N * subpowerBlockMomentFactor c ℓ *
        Real.rpow Y (-subpowerBlockS c ℓ) := by
  have h := subpowerWeight_block_large_card_mul_rpow_le c Y (subpowerBlockS c ℓ)
    hc hY.le hs hs1 ℓ hℓ N
  have hrhs :
      Real.rpow (subpowerWeight c (dyadicExpCutoff ℓ)) (subpowerBlockS c ℓ) *
          (N * (Real.exp (((2 : ℝ) ^ subpowerBlockS c ℓ - 1) *
              Erdos67.PrimeEstimates.mertensBound + 1) *
            Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ))
              ((2 : ℝ) ^ subpowerBlockS c ℓ - 1))) =
        N * subpowerBlockMomentFactor c ℓ := by
    unfold subpowerBlockMomentFactor
    ring
  rw [hrhs] at h
  have hpow : 0 < Real.rpow Y (subpowerBlockS c ℓ) := Real.rpow_pos_of_pos hY _
  calc
    (((Finset.Icc 1 N).filter
        (fun n => Y < weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
        (N * subpowerBlockMomentFactor c ℓ) /
          Real.rpow Y (subpowerBlockS c ℓ) := (le_div_iff₀ hpow).2 h
    _ = N * subpowerBlockMomentFactor c ℓ *
        Real.rpow Y (-subpowerBlockS c ℓ) := by
      change _ / (Y ^ subpowerBlockS c ℓ) = _ * (Y ^ (-subpowerBlockS c ℓ))
      rw [Real.rpow_neg hY.le, div_eq_mul_inv]

lemma sum_subpowerWeight_block_large_cards_le_majorant
    (c A : ℝ) (hc : 0 ≤ c) (hA : 0 < A)
    (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    (hs : 0 < subpowerBlockS c ℓ) (hs1 : subpowerBlockS c ℓ ≤ 1)
    (N J : ℕ) :
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 N).filter (fun n =>
          subpowerBlockThreshold A ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) ≤
      N * subpowerBlockShiftMajorant c A ℓ := by
  let r : ℝ := Real.rpow 2 (-subpowerBlockS c ℓ / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ j : ℕ,
      (((Finset.Icc 1 N).filter (fun n =>
        subpowerBlockThreshold A ℓ j <
          weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
        N * subpowerBlockMomentFactor c ℓ *
          Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) * r ^ j := by
    intro j
    calc
      (((Finset.Icc 1 N).filter (fun n =>
          subpowerBlockThreshold A ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ) ≤
          N * subpowerBlockMomentFactor c ℓ *
            Real.rpow (subpowerBlockThreshold A ℓ j) (-subpowerBlockS c ℓ) :=
        subpowerWeight_block_large_card_le_factor c (subpowerBlockThreshold A ℓ j) hc
          (subpowerBlockThreshold_pos A hA ℓ j) ℓ hℓ hs hs1 N
      _ = _ := by
        rw [subpowerBlockThreshold_rpow_neg c A hA]
        dsimp [r]
        ring
  have hconst0 : 0 ≤ N * subpowerBlockMomentFactor c ℓ *
      Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (subpowerBlockMomentFactor_nonneg c ℓ))
      (Real.rpow_nonneg (mul_nonneg hA.le (blockAllocation_pos ℓ).le) _)
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 N).filter (fun n =>
          subpowerBlockThreshold A ℓ j <
            weightedDivisorBlockMass (subpowerWeight c) ℓ n)).card : ℝ)) ≤
        ∑ j ∈ Finset.range J,
          (N * subpowerBlockMomentFactor c ℓ *
            Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) * r ^ j) := by
      exact Finset.sum_le_sum fun j _ => hterm j
    _ = (N * subpowerBlockMomentFactor c ℓ *
        Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ)) *
          ∑ j ∈ Finset.range J, r ^ j := by rw [Finset.mul_sum]
    _ ≤ (N * subpowerBlockMomentFactor c ℓ *
        Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ)) *
          ∑' j : ℕ, r ^ j := by
      exact mul_le_mul_of_nonneg_left
        ((hasSum_geometric_of_lt_one hr0 hr1).summable.sum_le_tsum
          (Finset.range J) (fun j _ => pow_nonneg hr0 j)) hconst0
    _ = N * subpowerBlockShiftMajorant c A ℓ := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
      unfold subpowerBlockShiftMajorant
      ring

/-- The block majorants, already summed over every shift threshold, form a convergent series for
every `c > 3`.  The comparison exponent is `(c+5)/8 > 1`. -/
lemma summable_subpowerBlockShiftMajorant {c A : ℝ} (hc : 3 < c) (hA : 0 < A) :
    Summable (subpowerBlockShiftMajorant c A) := by
  have hc0 : 0 < c := by linarith
  have hα0 : 0 < subpowerAlpha c := by
    unfold subpowerAlpha
    linarith
  have hp : 1 < subpowerP c := one_lt_subpowerP hc
  have hseries0 : Summable (fun ℓ : ℕ =>
      1 / |(ℓ : ℝ) + 2| ^ subpowerP c) :=
    (Real.summable_one_div_nat_add_rpow 2 (subpowerP c)).2 hp
  have hseries : Summable (fun ℓ : ℕ =>
      Real.rpow ((ℓ : ℝ) + 2) (-subpowerP c)) := by
    apply hseries0.congr
    intro ℓ
    change 1 / |(ℓ : ℝ) + 2| ^ subpowerP c =
      ((ℓ : ℝ) + 2) ^ (-subpowerP c)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (ℓ : ℝ) + 2)]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) + 2)]
    rw [one_div]
  have hsum : Summable (fun ℓ : ℕ => subpowerSeriesConstant c A *
      Real.rpow ((ℓ : ℝ) + 2) (-subpowerP c)) := hseries.mul_left _
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [eventually_subpowerBlockMomentFactor_le hc,
    eventually_subpowerBlock_parameters hc] with ℓ hmoment hpar
  rcases hpar with ⟨hℓ, hlog, hs0, hs1, hsδ, hσ1⟩
  let u : ℝ := blockLogLog ℓ
  let v : ℝ := (ℓ : ℝ) + 2
  have hu0 : 0 < u := by
    dsimp [u]
    exact (by positivity : (0 : ℝ) < ((ℓ : ℝ) + 2) / 4).trans_le
      (blockLogLog_ge_quarter_add ℓ hℓ)
  have hv0 : 0 < v := by dsimp [v]; positivity
  have hv1 : 1 ≤ v := by
    dsimp [v]
    exact_mod_cast (show 1 ≤ ℓ + 2 by omega)
  have huv : v / 4 ≤ u := by
    simpa [u, v] using blockLogLog_ge_quarter_add ℓ hℓ
  have hpowUV : Real.rpow u (-subpowerAlpha c) ≤
      Real.rpow 4 (subpowerAlpha c) * Real.rpow v (-subpowerAlpha c) := by
    have hmono : Real.rpow u (-subpowerAlpha c) ≤
        Real.rpow (v / 4) (-subpowerAlpha c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) huv (by linarith)
    calc
      Real.rpow u (-subpowerAlpha c) ≤
          Real.rpow (v / 4) (-subpowerAlpha c) := hmono
      _ = Real.rpow 4 (subpowerAlpha c) * Real.rpow v (-subpowerAlpha c) := by
        change (v / 4) ^ (-subpowerAlpha c) =
          4 ^ subpowerAlpha c * v ^ (-subpowerAlpha c)
        rw [Real.div_rpow hv0.le (by norm_num : (0 : ℝ) ≤ 4)]
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv, inv_inv]
        ring
  have hthreshold := subpowerBlockThresholdFactor_le c A hA ℓ hs0.le hs1 hsδ
  have hgeom := subpowerBlockShiftGeomFactor_le c hc0 ℓ hℓ hlog hs0 hσ1
  have hfactor0 : 0 ≤ subpowerBlockMomentFactor c ℓ := by
    unfold subpowerBlockMomentFactor
    exact mul_nonneg
      (Real.rpow_nonneg (subpowerWeight_nonneg c _) _)
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _))
  have hthreshold0 : 0 ≤ Real.rpow (A * blockAllocation ℓ) (-subpowerBlockS c ℓ) :=
    Real.rpow_nonneg (mul_nonneg hA.le (blockAllocation_pos ℓ).le) _
  have hgeom0 : 0 ≤ (1 - Real.rpow 2 (-subpowerBlockS c ℓ / 2))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
  have hupper0 : 0 ≤ subpowerMomentConstant * Real.rpow u (-subpowerAlpha c) :=
    mul_nonneg subpowerMomentConstant_pos.le (Real.rpow_nonneg hu0.le _)
  have hthresholdUpper0 :
      0 ≤ max 1 A⁻¹ * Real.rpow v (subpowerDelta c) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.rpow_nonneg hv0.le _)
  have hgeomUpper0 :
      0 ≤ (4 / Real.sqrt c) * Real.rpow v (1 / 2) :=
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hv0.le _)
  have hraw : subpowerBlockShiftMajorant c A ℓ ≤
      (subpowerMomentConstant * Real.rpow u (-subpowerAlpha c)) *
        (max 1 A⁻¹ * Real.rpow v (subpowerDelta c)) *
          ((4 / Real.sqrt c) * Real.rpow v (1 / 2)) := by
    unfold subpowerBlockShiftMajorant
    exact mul_le_mul
      (mul_le_mul hmoment hthreshold hthreshold0 hupper0)
      hgeom hgeom0 (mul_nonneg hupper0 hthresholdUpper0)
  have hraw' : subpowerBlockShiftMajorant c A ℓ ≤
      (subpowerMomentConstant *
          (Real.rpow 4 (subpowerAlpha c) * Real.rpow v (-subpowerAlpha c))) *
        (max 1 A⁻¹ * Real.rpow v (subpowerDelta c)) *
          ((4 / Real.sqrt c) * Real.rpow v (1 / 2)) :=
    hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowUV subpowerMomentConstant_pos.le)
        hthresholdUpper0)
      hgeomUpper0)
  have hrpows :
      Real.rpow v (-subpowerAlpha c) * Real.rpow v (subpowerDelta c) *
          Real.rpow v (1 / 2) =
        Real.rpow v (-subpowerAlpha c + subpowerDelta c + 1 / 2) := by
    change v ^ (-subpowerAlpha c) * v ^ subpowerDelta c * v ^ (1 / 2 : ℝ) =
      v ^ (-subpowerAlpha c + subpowerDelta c + 1 / 2)
    rw [← Real.rpow_add hv0, ← Real.rpow_add hv0]
  have hcombine :
      (subpowerMomentConstant *
          (Real.rpow 4 (subpowerAlpha c) * Real.rpow v (-subpowerAlpha c))) *
        (max 1 A⁻¹ * Real.rpow v (subpowerDelta c)) *
          ((4 / Real.sqrt c) * Real.rpow v (1 / 2)) =
        subpowerSeriesConstant c A *
          Real.rpow v (-subpowerAlpha c + subpowerDelta c + 1 / 2) := by
    unfold subpowerSeriesConstant
    rw [← hrpows]
    ring
  rw [hcombine] at hraw'
  have hbudget : -subpowerAlpha c + subpowerDelta c + 1 / 2 ≤ -subpowerP c :=
    (subpower_exponent_budget hc).le
  have hconst0 : 0 ≤ subpowerSeriesConstant c A := by
    unfold subpowerSeriesConstant
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg subpowerMomentConstant_pos.le (Real.rpow_nonneg (by norm_num) _))
        (le_trans zero_le_one (le_max_left _ _)))
      (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hfinal := hraw'.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hv1 hbudget) hconst0)
  have hmajor0 : 0 ≤ subpowerBlockShiftMajorant c A ℓ := by
    unfold subpowerBlockShiftMajorant
    exact mul_nonneg (mul_nonneg hfactor0 hthreshold0) hgeom0
  rw [Real.norm_eq_abs, abs_of_nonneg hmajor0]
  simpa [v] using hfinal

/-- Summing the allocated block covers first over shifts and then over blocks costs exactly the
finite tail of the block majorant. -/
lemma sum_marginalDivisorMass_large_cards_le_block_majorants
    (c C ε : ℝ) (hc0 : 0 ≤ c) (hC : 0 < C) (hε : 0 < ε)
    (delta : ℕ → ℝ)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m)
    (L T J : ℕ)
    (hpar : ∀ ℓ : ℕ, L ≤ ℓ →
      3 ≤ ℓ ∧ 0 < subpowerBlockS c ℓ ∧ subpowerBlockS c ℓ ≤ 1) :
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) ≤
      T * ∑ i ∈ Finset.range T, subpowerBlockShiftMajorant c (ε / C) (L + i) := by
  have hdom : ∀ m : ℕ, dyadicExpCutoff L < m →
      delta m ≤ C * subpowerWeight c m := by
    intro m hm
    exact hdelta m ((dyadicExpCutoff_two_le L).trans (Nat.le_of_lt hm))
  have hA : 0 < ε / C := div_pos hε hC
  have hthreshold : ∀ i j : ℕ,
      ((ε * Real.rpow 2 ((j : ℝ) / 2)) / C) * blockAllocation (L + i) =
        subpowerBlockThreshold (ε / C) (L + i) j := by
    intro i j
    unfold subpowerBlockThreshold
    ring
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) ≤
        ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range T,
          (((Finset.Icc 1 T).filter (fun n =>
            subpowerBlockThreshold (ε / C) (L + i) j <
              weightedDivisorBlockMass (subpowerWeight c) (L + i) n)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hcover := marginalDivisorMass_large_card_le_sum_block_cards
        delta (subpowerWeight c) C hC L T hdom
        (ε * Real.rpow 2 ((j : ℝ) / 2))
        (mul_nonneg hε.le (Real.rpow_nonneg (by norm_num) _))
      exact_mod_cast (by simpa only [hthreshold] using hcover)
    _ = ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            subpowerBlockThreshold (ε / C) (L + i) j <
              weightedDivisorBlockMass (subpowerWeight c) (L + i) n)).card : ℝ) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ Finset.range T,
          T * subpowerBlockShiftMajorant c (ε / C) (L + i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hLi : L ≤ L + i := Nat.le_add_right L i
      rcases hpar (L + i) hLi with ⟨hℓ, hs, hs1⟩
      exact sum_subpowerWeight_block_large_cards_le_majorant
        c (ε / C) hc0 hA (L + i) hℓ hs hs1 T J
    _ = T * ∑ i ∈ Finset.range T,
          subpowerBlockShiftMajorant c (ε / C) (L + i) := by
      rw [Finset.mul_sum]

/-- Uniformly in the averaging range and in the number of shifts, the total density of large
marginal divisor tails tends to zero as the double-exponential cutoff moves out. -/
lemma exists_subpower_marginal_large_cards_le
    (c C ε ζ : ℝ) (hc : 3 < c) (hC : 0 < C) (hε : 0 < ε) (hζ : 0 < ζ)
    (delta : ℕ → ℝ)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∃ L₀ : ℕ, 3 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) ≤
        ζ * T := by
  let f : ℕ → ℝ := subpowerBlockShiftMajorant c (ε / C)
  have hA : 0 < ε / C := div_pos hε hC
  have hsum : Summable f := summable_subpowerBlockShiftMajorant hc hA
  obtain ⟨L₀, hpar₀⟩ := eventually_atTop.1 (eventually_subpowerBlock_parameters hc)
  have htailEv : ∀ᶠ L : ℕ in atTop, (∑' i : ℕ, f (i + L)) < ζ :=
    (tendsto_sum_nat_add f).eventually_lt_const hζ
  obtain ⟨Lbase, hbase⟩ := eventually_atTop.1
    (htailEv.and (eventually_ge_atTop (max L₀ 3)))
  have hbaseData := hbase Lbase le_rfl
  refine ⟨Lbase, (le_max_right L₀ 3).trans hbaseData.2, ?_⟩
  intro L hLbase T J
  have hdata := hbase L hLbase
  have htail := hdata.1
  have hL := hdata.2
  have hpar : ∀ ℓ : ℕ, L ≤ ℓ →
      3 ≤ ℓ ∧ 0 < subpowerBlockS c ℓ ∧ subpowerBlockS c ℓ ≤ 1 := by
    intro ℓ hLℓ
    rcases hpar₀ ℓ ((le_max_left L₀ 3).trans hL |>.trans hLℓ) with
      ⟨hℓ, _hlog, hs, hs1, _hsδ, _hσ1⟩
    exact ⟨by omega, hs, hs1⟩
  have hfinite :
      (∑ i ∈ Finset.range T, f (L + i)) ≤ ∑' i : ℕ, f (i + L) := by
    have hshift : Summable (fun i : ℕ => f (i + L)) :=
      hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have hle := hshift.sum_le_tsum (Finset.range T)
      (fun i _ => subpowerBlockShiftMajorant_nonneg c (ε / C) hA.le (i + L))
    simpa only [Nat.add_comm] using hle
  calc
    (∑ j ∈ Finset.range J,
        (((Finset.Icc 1 T).filter (fun n =>
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta (dyadicExpCutoff L) n)).card : ℝ)) ≤
        T * ∑ i ∈ Finset.range T,
          subpowerBlockShiftMajorant c (ε / C) (L + i) :=
      sum_marginalDivisorMass_large_cards_le_block_majorants
        c C ε (by linarith) hC hε delta hdelta L T J hpar
    _ ≤ T * ∑' i : ℕ, f (i + L) := by
      exact mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ ≤ T * ζ := mul_le_mul_of_nonneg_left htail.le (by positivity)
    _ = ζ * T := by ring

/-- The deterministic capped residual required by the marginal-only non-normality criterion becomes
uniformly small under the frozen sub-power domination hypothesis. -/
lemma subpower_capped_marginal_residual_small
    (delta : ℕ → ℝ) (hdeltaRange : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1)
    (c C : ℝ) (hc : 3 < c) (hC : 0 < C)
    (hdelta : ∀ m : ℕ, 2 ≤ m → delta m ≤ C * subpowerWeight c m) :
    ∀ b : ℕ, 2 ≤ b → ∀ η : ℝ, 0 < η →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
        cappedMarginalResidualAverage b delta M N ≤ η := by
  intro b hb η hη
  let G : ℝ := ∑' j : ℕ, residualGoodMajorant j
  have hG : 0 ≤ G := tsum_nonneg fun j => by
    unfold residualGoodMajorant
    exact mul_nonneg (by norm_num)
      (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  have hG1 : 0 < G + 1 := by linarith
  let ε : ℝ := η / (4 * (G + 1))
  let ζ : ℝ := η / 12
  let τ : ℝ := η / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨L₀, hL₀, hlargeAll⟩ :=
    exists_subpower_marginal_large_cards_le c C ε ζ hc hC hε hζ delta hdelta
  have htailEv : ∀ᶠ J : ℕ in atTop,
      (∑' k : ℕ, residualTailMajorant (k + J)) < τ :=
    (tendsto_sum_nat_add residualTailMajorant).eventually_lt_const hτ
  obtain ⟨K, htailK⟩ := eventually_atTop.1 htailEv
  let L := L₀ + 3 * K
  let M := dyadicExpCutoff L
  have hL : L₀ ≤ L := by dsimp [L]; omega
  have hMK : 3 * K ≤ M := by
    dsimp [M, L]
    exact index_le_dyadicExpCutoff_add L₀ (3 * K)
  have hlarge : ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta M n)).card : ℝ)) ≤ ζ * T := by
    simpa [M] using hlargeAll L hL
  have htail : ∀ J : ℕ, K ≤ J →
      (∑' k : ℕ, residualTailMajorant (k + J)) ≤ τ := by
    intro J hKJ
    exact (htailK J hKJ).le
  refine ⟨M, ?_, ?_⟩
  · exact dyadicExpCutoff_two_le L
  intro N hN
  have havg := cappedMarginalResidualAverage_le_of_large_cards
    b hb delta hdeltaRange M K hMK ε ζ τ hε.le hζ.le hlarge htail N hN
  have hgood : ε * G ≤ η / 4 := by
    calc
      ε * G ≤ ε * (G + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = η / 4 := by
        dsimp [ε]
        field_simp [ne_of_gt hG1]
  calc
    cappedMarginalResidualAverage b delta M N ≤ ε * G + τ + 3 * ζ := by
      simpa [G] using havg
    _ ≤ η / 4 + η / 4 + 3 * (η / 12) := by
      dsimp [τ, ζ]
      gcongr
    _ ≤ η := by linarith

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
  have hX' := hX
  obtain ⟨hdeltaRange, _hMeas, _hIndep, _hLaw⟩ := hX
  have hweight : 0 < subpowerWeight c 2 := by
    unfold subpowerWeight
    exact mul_pos (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _)
      (Real.exp_pos _)
  have hprod : 0 ≤ C * subpowerWeight c 2 :=
    (hdeltaRange 2).1.trans (hdelta 2 (by omega))
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left hprod hweight
  apply ae_not_normal_of_capped_marginal_residual μ delta X hX'
  by_cases hC0 : C = 0
  · intro b hb η hη
    have hdeltaZero : ∀ m : ℕ, 2 ≤ m → delta m = 0 := by
      intro m hm
      apply le_antisymm
      · simpa [hC0] using hdelta m hm
      · exact (hdeltaRange m).1
    refine ⟨2, by omega, ?_⟩
    intro N hN
    have hmass : ∀ n : ℕ, marginalDivisorMass delta 2 n = 0 := by
      intro n
      unfold marginalDivisorMass
      apply Finset.sum_eq_zero
      intro m hm
      exact hdeltaZero m (by
        have hm2 := (Finset.mem_filter.mp hm).2
        omega)
    have hres : ∀ n : ℕ, marginalShiftResidual b delta 2 n = 0 := by
      intro n
      unfold marginalShiftResidual
      simp only [hmass, mul_zero, tsum_zero]
    unfold cappedMarginalResidualAverage
    simp [hres, hη.le]
  · exact subpower_capped_marginal_residual_small delta hdeltaRange c C hc
      (lt_of_le_of_ne hC (Ne.symm hC0)) hdelta

end NormalNumbers.ErdosBorweinSubpower
