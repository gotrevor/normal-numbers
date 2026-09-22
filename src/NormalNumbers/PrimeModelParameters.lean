import NormalNumbers.G4WiringSparse
import NormalNumbers.PrimeModelPrimeDimension
import Mathlib.NumberTheory.Primorial

/-!
# Prime model, assembly part D: parameters and real-inequality bookkeeping

`papers/prime-model-assembly-2026-09-22.md`, "Regime split", "Parameters", F1–F5, E2, E3 and
the absorption inequalities.  Pure real analysis; no arithmetic and no phases.

Regime R2 is `ε ≤ 1/(7680k)` together with the frozen `1/log log x < ε`; then
`log log x > 7680 k` and every size condition is automatic.  Parameters:

    y = ⌊x^ε⌋₊,   σ = log x / (4 log y),   T = x^{1/(4k)},   R = y^σ = x^{1/4},   Q = k#.

All statements are about the actual integer `y = ⌊x^ε⌋₊`, never about `x^ε`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.Params

open NormalNumbers.G4Sparse

/-- The main regime: the frozen `ε`-window together with the sieve threshold `ε ≤ 1/(7680k)`. -/
structure Regime (x k : ℕ) (ε : ℝ) : Prop where
  hx : 3 ≤ x
  hk : 1 ≤ k
  hε1 : 1 / Real.log (Real.log x) < ε
  hε2 : ε ≤ 1 / (7680 * k)

/-- `y = ⌊x^ε⌋₊`. -/
noncomputable def yOf (x : ℕ) (ε : ℝ) : ℕ := ⌊(x : ℝ) ^ ε⌋₊

/-- `σ = log x / (4 log y)`, the sieve parameter `log R / log y` with `R = x^{1/4}`. -/
noncomputable def sigmaOf (x : ℕ) (ε : ℝ) : ℝ := Real.log x / (4 * Real.log (yOf x ε))

/-- `T = x^{1/(4k)}`, the retained-box side. -/
noncomputable def TOf (x k : ℕ) : ℝ := (x : ℝ) ^ (1 / (4 * (k : ℝ)))

variable {x k : ℕ} {ε : ℝ}

private theorem x_ge_three (hx : 3 ≤ x) : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx

private theorem logx_gt_one (hx : 3 ≤ x) : 1 < Real.log x := by
  have h3 : Real.exp 1 < (x : ℝ) := by
    have := x_ge_three hx
    linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log x := Real.log_lt_log (Real.exp_pos 1) h3

private theorem loglogx_pos (hx : 3 ≤ x) : 0 < Real.log (Real.log x) :=
  Real.log_pos (logx_gt_one hx)

theorem eps_pos (hR : Regime x k ε) : 0 < ε :=
  lt_trans (div_pos one_pos (loglogx_pos hR.hx)) hR.hε1

/-- `log log x > 7680 k`. -/
theorem loglog_gt (hR : Regime x k ε) : 7680 * (k : ℝ) < Real.log (Real.log x) :=
  lt_of_one_div_lt_one_div (loglogx_pos hR.hx) (lt_of_lt_of_le hR.hε1 hR.hε2)

private theorem loglog_ge_7680 (hR : Regime x k ε) :
    (7680 : ℝ) ≤ Real.log (Real.log x) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have := loglog_gt hR
  nlinarith

/-- `3840 k ≤ ε log x`. -/
private theorem eps_mul_log_ge (hR : Regime x k ε) : 3840 * (k : ℝ) ≤ ε * Real.log x := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have htk : 7680 * (k : ℝ) < Real.log (Real.log x) := loglog_gt hR
  have hL1 : 1 < Real.log x := logx_gt_one hR.hx
  have ht0 : 0 < Real.log (Real.log x) := loglogx_pos hR.hx
  have ht : (7680 : ℝ) ≤ Real.log (Real.log x) := loglog_ge_7680 hR
  have hexp : Real.exp (Real.log (Real.log x)) = Real.log x :=
    Real.exp_log (by linarith)
  have hquad : 1 + Real.log (Real.log x) + (Real.log (Real.log x)) ^ 2 / 2 ≤ Real.log x := by
    have h0 := Real.quadratic_le_exp_of_nonneg ht0.le
    rwa [hexp] at h0
  have hεpos : 0 < ε := eps_pos hR
  have hεt : 1 < ε * Real.log (Real.log x) := (div_lt_iff₀ ht0).mp hR.hε1
  nlinarith [mul_le_mul_of_nonneg_left hquad hεpos.le,
    mul_pos (sub_pos.mpr hεt) ht0]

/-- `3 ≤ ε log x`. -/
private theorem eps_mul_log_ge_three (hR : Regime x k ε) : 3 ≤ ε * Real.log x := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have := eps_mul_log_ge hR
  linarith

/-- F1: `x^ε ≥ e³`. -/
theorem rpow_ge_exp_three (hR : Regime x k ε) : Real.exp 3 ≤ (x : ℝ) ^ ε := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  rw [Real.rpow_def_of_pos hx0]
  exact Real.exp_le_exp.mpr (by rw [mul_comm]; exact eps_mul_log_ge_three hR)

private theorem exp_three_ge_four : (4 : ℝ) ≤ Real.exp 3 := by
  linarith [Real.add_one_le_exp (3 : ℝ)]

/-- F1: `x^ε/2 ≤ y ≤ x^ε`. -/
theorem yOf_bounds (hR : Regime x k ε) :
    (x : ℝ) ^ ε / 2 ≤ (yOf x ε : ℝ) ∧ (yOf x ε : ℝ) ≤ (x : ℝ) ^ ε := by
  have hu : Real.exp 3 ≤ (x : ℝ) ^ ε := rpow_ge_exp_three hR
  have hu0 : (0 : ℝ) ≤ (x : ℝ) ^ ε := by linarith [exp_three_ge_four, hu]
  refine ⟨?_, Nat.floor_le hu0⟩
  have h := Nat.lt_floor_add_one ((x : ℝ) ^ ε)
  unfold yOf
  linarith [exp_three_ge_four, hu]

/-- F1: `y ≥ e²`. -/
theorem yOf_ge_exp_two (hR : Regime x k ε) : Real.exp 2 ≤ (yOf x ε : ℝ) := by
  have h1 := (yOf_bounds hR).1
  have hu : Real.exp 3 ≤ (x : ℝ) ^ ε := rpow_ge_exp_three hR
  have he : Real.exp 3 = Real.exp 2 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  nlinarith

/-- F1: `log y ≥ 2`. -/
theorem log_yOf_ge_two (hR : Regime x k ε) : 2 ≤ Real.log (yOf x ε) := by
  have h := yOf_ge_exp_two hR
  calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
    _ ≤ Real.log (yOf x ε) := Real.log_le_log (Real.exp_pos 2) h

/-- The window length is below the sieve cutoff: `k ≤ y`. -/
theorem k_le_yOf (hR : Regime x k ε) : k ≤ yOf x ε := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have hεL : 3840 * (k : ℝ) ≤ ε * Real.log x := eps_mul_log_ge hR
  have hu : (k : ℝ) ≤ (x : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos hx0]
    have h1 : Real.log x * ε + 1 ≤ Real.exp (Real.log x * ε) := Real.add_one_le_exp _
    nlinarith
  exact Nat.le_floor hu

/-- F2: `1/ε ≤ log x / log y ≤ 2/ε`. -/
theorem log_ratio_bounds (hR : Regime x k ε) :
    1 / ε ≤ Real.log x / Real.log (yOf x ε) ∧ Real.log x / Real.log (yOf x ε) ≤ 2 / ε := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hεpos : 0 < ε := eps_pos hR
  have hly : 2 ≤ Real.log (yOf x ε) := log_yOf_ge_two hR
  have hly0 : 0 < Real.log (yOf x ε) := by linarith
  have hεL : 3 ≤ ε * Real.log x := eps_mul_log_ge_three hR
  have hy0 : (0 : ℝ) < (yOf x ε : ℝ) := lt_of_lt_of_le (Real.exp_pos 2) (yOf_ge_exp_two hR)
  have hu0 : (0 : ℝ) < (x : ℝ) ^ ε := Real.rpow_pos_of_pos hx0 ε
  have hlogu : Real.log ((x : ℝ) ^ ε) = ε * Real.log x := Real.log_rpow hx0 ε
  have hb := yOf_bounds hR
  have hyu : Real.log (yOf x ε) ≤ ε * Real.log x := by
    rw [← hlogu]; exact Real.log_le_log hy0 hb.2
  have hyl : ε * Real.log x - Real.log 2 ≤ Real.log (yOf x ε) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (x : ℝ) ^ ε / 2) hb.1
    rw [Real.log_div (ne_of_gt hu0) (by norm_num), hlogu] at h
    linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hcomm : Real.log x * ε = ε * Real.log x := mul_comm _ _
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff₀ hεpos hly0]; linarith
  · rw [div_le_div_iff₀ hly0 hεpos]; linarith

/-- F2: `σ ≥ 1/(4ε)`. -/
theorem sigmaOf_ge (hR : Regime x k ε) : 1 / (4 * ε) ≤ sigmaOf x ε := by
  have hεpos : 0 < ε := eps_pos hR
  have hly0 : 0 < Real.log (yOf x ε) := by linarith [log_yOf_ge_two hR]
  have h := (log_ratio_bounds hR).1
  rw [div_le_div_iff₀ hεpos hly0] at h
  unfold sigmaOf
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- F2: the two size hypotheses of `brun_sifted_count_lower`. -/
theorem sigmaOf_thresholds (hR : Regime x k ε) :
    1920 * (k : ℝ) ≤ sigmaOf x ε
      ∧ 40 * Real.log ((4 : ℝ) ^ k * Real.exp (16 * k)) + 4 ≤ sigmaOf x ε := by
  have hεpos : 0 < ε := eps_pos hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have hk0 : (0 : ℝ) < 7680 * k := by linarith
  have h7 : ε * (7680 * (k : ℝ)) ≤ 1 := (le_div_iff₀ hk0).mp hR.hε2
  have hσ : 1920 * (k : ℝ) ≤ sigmaOf x ε := by
    refine le_trans ?_ (sigmaOf_ge hR)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨hσ, le_trans ?_ hσ⟩
  have hlog : Real.log ((4 : ℝ) ^ k * Real.exp (16 * k)) = (k : ℝ) * Real.log 4 + 16 * k := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
  have hlog4 : Real.log 4 < 1.39 := by
    have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  rw [hlog]
  nlinarith

/-- F3: `y^σ = x^{1/4}`. -/
theorem yOf_rpow_sigmaOf (hR : Regime x k ε) :
    (yOf x ε : ℝ) ^ sigmaOf x ε = (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hy0 : (0 : ℝ) < (yOf x ε : ℝ) := lt_of_lt_of_le (Real.exp_pos 2) (yOf_ge_exp_two hR)
  have hly0 : Real.log (yOf x ε) ≠ 0 := by
    have := log_yOf_ge_two hR; intro h; rw [h] at this; linarith
  rw [Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hx0]
  congr 1
  unfold sigmaOf
  field_simp

/-- F4: `1 ≤ T` and `⌊T⌋₊^k ≤ x^{1/4}`. -/
theorem TOf_ge_one (hR : Regime x k ε) : 1 ≤ TOf x k := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith [x_ge_three hR.hx]
  exact Real.one_le_rpow hx1 (by positivity)

theorem floor_TOf_pow_le (hR : Regime x k ε) :
    (Nat.floor (TOf x k) : ℝ) ^ k ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith [x_ge_three hR.hx]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have hkne : (k : ℝ) ≠ 0 := by linarith
  have hT1 : (1 : ℝ) ≤ TOf x k := TOf_ge_one hR
  have hfl : (Nat.floor (TOf x k) : ℝ) ≤ TOf x k := Nat.floor_le (by linarith)
  have hpow : (Nat.floor (TOf x k) : ℝ) ^ k ≤ (TOf x k) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hfl k
  refine le_trans hpow (le_of_eq ?_)
  unfold TOf
  rw [← Real.rpow_natCast ((x : ℝ) ^ (1 / (4 * (k : ℝ)))) k, ← Real.rpow_mul hx0]
  congr 1
  field_simp

/-- F4: `k# ≤ 4^k`. -/
theorem primorial_le_four_pow_real (k : ℕ) : ((primorial k : ℕ) : ℝ) ≤ (4 : ℝ) ^ k := by
  exact_mod_cast primorial_le_four_pow k

/-- `k#` is coprime to every prime exceeding `k`. -/
theorem primorial_coprime_of_lt {p : ℕ} (hp : p.Prime) (hkp : k < p) :
    Nat.Coprime (primorial k) p :=
  Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    (fun hd => by have := hp.dvd_primorial_iff.mp hd; omega))

/-! ### Absorption into the frozen sieve term `exp(−1/(8k²ε))` -/

/-- `1/ε < log x`. -/
private theorem one_div_eps_lt_logx (hR : Regime x k ε) : 1 / ε < Real.log x := by
  have ht0 := loglogx_pos hR.hx
  have hL1 := logx_gt_one hR.hx
  have hεpos := eps_pos hR
  have hεt : 1 < ε * Real.log (Real.log x) := (div_lt_iff₀ ht0).mp hR.hε1
  have htL : Real.log (Real.log x) ≤ Real.log x := Real.log_le_self (by linarith)
  rw [div_lt_iff₀ hεpos]
  nlinarith [mul_le_mul_of_nonneg_left htL hεpos.le]

/-- `1/(8k²ε) ≤ (log x)/4`. -/
private theorem inv_key_le_quarter_logx (hR : Regime x k ε) :
    1 / (8 * (k : ℝ) ^ 2 * ε) ≤ Real.log x / 4 := by
  have hεpos : 0 < ε := eps_pos hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have h := one_div_eps_lt_logx hR
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  rw [div_lt_iff₀ hεpos] at h
  nlinarith

/-- E3 / F5: `1/x ≤ exp(−1/(8k²ε))`. -/
theorem inv_x_le_expTerm (hR : Regime x k ε) :
    1 / (x : ℝ) ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hL1 : 1 < Real.log x := logx_gt_one hR.hx
  have hxe : (1 : ℝ) / x = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hx0, one_div]
  rw [hxe]
  refine Real.exp_le_exp.mpr ?_
  have hkey := inv_key_le_quarter_logx hR
  have hneg : (-1 : ℝ) / (8 * (k : ℝ) ^ 2 * ε) = -(1 / (8 * (k : ℝ) ^ 2 * ε)) := by ring
  rw [hneg]
  linarith

/-- The model tail: `k e^{20} / T^{1/(2 log y)} ≤ k e^{20} · exp(−1/(8k²ε))`. -/
theorem tail_absorbed (hR : Regime x k ε) :
    (k : ℝ) * Real.exp 20 / (TOf x k) ^ (1 / (2 * Real.log (yOf x ε)))
      ≤ (k : ℝ) * Real.exp 20 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hεpos : 0 < ε := eps_pos hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have hly : 2 ≤ Real.log (yOf x ε) := log_yOf_ge_two hR
  have hly0 : 0 < Real.log (yOf x ε) := by linarith
  have hT0 : (0 : ℝ) < TOf x k := Real.rpow_pos_of_pos hx0 _
  have hE0 : (0 : ℝ) < (TOf x k) ^ (1 / (2 * Real.log (yOf x ε))) :=
    Real.rpow_pos_of_pos hT0 _
  have hA0 : (0 : ℝ) ≤ (k : ℝ) * Real.exp 20 := by positivity
  -- the key exponent bound
  have hratio : 1 / ε ≤ Real.log x / Real.log (yOf x ε) := (log_ratio_bounds hR).1
  rw [div_le_div_iff₀ hεpos hly0] at hratio
  have hkey : 1 / (8 * (k : ℝ) ^ 2 * ε)
      ≤ Real.log x / (8 * (k : ℝ) * Real.log (yOf x ε)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr (by nlinarith : (k : ℝ) ≤ (k : ℝ) ^ 2)) hly0.le]
  have hE : Real.exp (1 / (8 * (k : ℝ) ^ 2 * ε))
      ≤ (TOf x k) ^ (1 / (2 * Real.log (yOf x ε))) := by
    rw [Real.rpow_def_of_pos hT0]
    refine Real.exp_le_exp.mpr ?_
    have hlogT : Real.log (TOf x k) = 1 / (4 * (k : ℝ)) * Real.log x := by
      unfold TOf; exact Real.log_rpow hx0 _
    rw [hlogT]
    have heq : 1 / (4 * (k : ℝ)) * Real.log x * (1 / (2 * Real.log (yOf x ε)))
        = Real.log x / (8 * (k : ℝ) * Real.log (yOf x ε)) := by
      field_simp
      ring
    rw [heq]
    exact hkey
  have hmul : (1 : ℝ) ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))
      * (TOf x k) ^ (1 / (2 * Real.log (yOf x ε))) := by
    have hneg : Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε))
        = (Real.exp (1 / (8 * (k : ℝ) ^ 2 * ε)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hneg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _)]
    simpa using hE
  rw [div_le_iff₀ hE0]
  nlinarith [mul_le_mul_of_nonneg_left hmul hA0]

/-- The sieve relative error: `exp(−σ/2) ≤ exp(−1/(8k²ε))`. -/
theorem sieve_absorbed (hR : Regime x k ε) :
    Real.exp (-(sigmaOf x ε) / 2) ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  have hεpos : 0 < ε := eps_pos hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  refine Real.exp_le_exp.mpr ?_
  have hσ : 1 / (4 * ε) ≤ sigmaOf x ε := sigmaOf_ge hR
  have hksq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hden : 8 * ε ≤ 8 * (k : ℝ) ^ 2 * ε := by nlinarith
  have hle : 1 / (8 * (k : ℝ) ^ 2 * ε) ≤ 1 / (8 * ε) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hhalf : 1 / (8 * ε) = 1 / (4 * ε) / 2 := by ring
  have hneg : (-1 : ℝ) / (8 * (k : ℝ) ^ 2 * ε) = -(1 / (8 * (k : ℝ) ^ 2 * ε)) := by ring
  rw [hneg]
  linarith

/-- The accumulated arithmetic remainder:
`Q ⌊T⌋₊^k (y^σ)² / x ≤ 4^k · x^{−1/4} ≤ 4^k · exp(−1/(8k²ε))`. -/
theorem remainder_absorbed (hR : Regime x k ε) :
    ((primorial k : ℕ) : ℝ) * (Nat.floor (TOf x k) : ℝ) ^ k * ((yOf x ε : ℝ) ^ sigmaOf x ε) ^ 2 / x
      ≤ (4 : ℝ) ^ k * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hq := primorial_le_four_pow_real k
  have hfl := floor_TOf_pow_le hR
  have hy := yOf_rpow_sigmaOf hR
  have hfl0 : (0 : ℝ) ≤ (Nat.floor (TOf x k) : ℝ) ^ k := by positivity
  have hnum : ((primorial k : ℕ) : ℝ) * (Nat.floor (TOf x k) : ℝ) ^ k
      * ((yOf x ε : ℝ) ^ sigmaOf x ε) ^ 2 ≤ (4 : ℝ) ^ k * (x : ℝ) ^ (3 / 4 : ℝ) := by
    rw [hy]
    have hs : ((x : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (x : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hs]
    have hmul : (4 : ℝ) ^ k * (x : ℝ) ^ (3 / 4 : ℝ)
        = ((4 : ℝ) ^ k * (x : ℝ) ^ (1 / 4 : ℝ)) * (x : ℝ) ^ (1 / 2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      norm_num
    rw [hmul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hq hfl hfl0 (by positivity)) (by positivity)
  have hkey2 : (x : ℝ) ^ (3 / 4 : ℝ)
      ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) * (x : ℝ) := by
    have hr : (x : ℝ) ^ (3 / 4 : ℝ) = Real.exp (Real.log x * (3 / 4)) :=
      Real.rpow_def_of_pos hx0 _
    have hr2 : Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) * (x : ℝ)
        = Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε) + Real.log x) := by
      rw [Real.exp_add, Real.exp_log hx0]
    rw [hr, hr2]
    refine Real.exp_le_exp.mpr ?_
    have h := inv_key_le_quarter_logx hR
    have hneg : (-1 : ℝ) / (8 * (k : ℝ) ^ 2 * ε) = -(1 / (8 * (k : ℝ) ^ 2 * ε)) := by ring
    rw [hneg]
    linarith
  calc ((primorial k : ℕ) : ℝ) * (Nat.floor (TOf x k) : ℝ) ^ k
        * ((yOf x ε : ℝ) ^ sigmaOf x ε) ^ 2 / x
      ≤ (4 : ℝ) ^ k * (x : ℝ) ^ (3 / 4 : ℝ) / x :=
        (div_le_div_iff_of_pos_right hx0).mpr hnum
    _ ≤ (4 : ℝ) ^ k * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
        rw [div_le_iff₀ hx0]
        nlinarith [mul_le_mul_of_nonneg_left hkey2 (by positivity : (0:ℝ) ≤ (4:ℝ) ^ k)]

/-! ### E2: Cauchy–Schwarz against the interval Mertens bound -/

/-- `∑_{y<p≤x} 1/p ≤ 36 log(1/ε)` (from `primeRecipSum_le` and F2). -/
theorem recip_Ioc_le (hR : Regime x k ε) :
    ∑ p ∈ (Finset.Ioc (yOf x ε) x).filter Nat.Prime, (1 : ℝ) / p
      ≤ 36 * Real.log (1 / ε) := by
  have hx0 : (0 : ℝ) < x := by linarith [x_ge_three hR.hx]
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith [x_ge_three hR.hx]
  have hεpos : 0 < ε := eps_pos hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR.hk
  have hinv : (7680 : ℝ) ≤ 1 / ε := by
    have h := one_div_le_one_div_of_le hεpos hR.hε2
    rw [one_div_one_div] at h
    nlinarith
  have h7680 : 7680 * ε ≤ 1 := (le_div_iff₀ hεpos).mp hinv
  have hεle1 : ε ≤ 1 := by linarith
  have hly : 2 ≤ Real.log (yOf x ε) := log_yOf_ge_two hR
  have hly0 : 0 < Real.log (yOf x ε) := by linarith
  have hy2 : (2 : ℝ) ≤ (yOf x ε : ℝ) := by
    have h := yOf_ge_exp_two hR
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hyx : (yOf x ε : ℝ) ≤ (x : ℝ) := by
    refine le_trans (yOf_bounds hR).2 ?_
    calc (x : ℝ) ^ ε ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hεle1
      _ = x := Real.rpow_one _
  have key := NormalNumbers.PrimeModel.PrimeDensity.primeRecipSum_le
    ((yOf x ε : ℝ)) hy2 x hyx
  have hset : (Finset.Iic x).filter (fun p => Nat.Prime p ∧ ((yOf x ε : ℝ)) < (p : ℝ))
      = (Finset.Ioc (yOf x ε) x).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc, Nat.cast_lt]
    tauto
  rw [hset] at key
  refine le_trans key ?_
  have hratio := (log_ratio_bounds hR).2
  have hLpos : 0 < Real.log x := by linarith [logx_gt_one hR.hx]
  have hpos : 0 < Real.log x / Real.log (yOf x ε) := div_pos hLpos hly0
  have hlogmono : Real.log (Real.log x / Real.log (yOf x ε)) ≤ Real.log (2 / ε) :=
    Real.log_le_log hpos hratio
  have hsplit : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hεpos),
        Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hεpos), Real.log_one]
    ring
  have hl1 : (1 : ℝ) ≤ Real.log (1 / ε) := by
    have he : Real.exp 1 ≤ 1 / ε := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (1 / ε) := Real.log_le_log (Real.exp_pos 1) he
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- **E2.**  `4k · recipSumIoc ≤ 24k · √log(1/ε) · √(2 recipSumIoc)`. -/
theorem recipSumIoc_cs (hR : Regime x k ε) (S : ℕ → Prop) [DecidablePred S] :
    4 * (k : ℝ) * recipSumIoc S (yOf x ε) x
      ≤ 24 * (k : ℝ) * (Real.sqrt (Real.log (1 / ε))
          * Real.sqrt (2 * recipSumIoc S (yOf x ε) x)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  set a := recipSumIoc S (yOf x ε) x with ha
  have ha0 : 0 ≤ a := by
    rw [ha]
    unfold recipSumIoc
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hb : a ≤ 36 * Real.log (1 / ε) := by
    refine le_trans ?_ (recip_Ioc_le hR)
    rw [ha]
    unfold recipSumIoc
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hl0 : 0 ≤ Real.log (1 / ε) := by linarith
  have hsq36 : Real.sqrt (36 * Real.log (1 / ε)) = 6 * Real.sqrt (Real.log (1 / ε)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36),
      show Real.sqrt 36 = 6 by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]]
  have h1 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
  have h2 : Real.sqrt a ≤ Real.sqrt (2 * a) := Real.sqrt_le_sqrt (by linarith)
  have h3 : Real.sqrt a ≤ 6 * Real.sqrt (Real.log (1 / ε)) := by
    rw [← hsq36]; exact Real.sqrt_le_sqrt hb
  have h4 : a ≤ 6 * (Real.sqrt (Real.log (1 / ε)) * Real.sqrt (2 * a)) := by
    have hmm := mul_le_mul h3 h2 (Real.sqrt_nonneg a) (by positivity)
    rw [h1] at hmm
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hk0]

/-! ### Constants and their growth -/

/-- `C₁(k) = exp(4k)`. -/
noncomputable def C₁ (k : ℕ) : ℝ := Real.exp (4 * k)

/-- `C₂(k) = exp(exp(k+7))`. -/
noncomputable def C₂ (k : ℕ) : ℝ := Real.exp (Real.exp (k + 7))

private theorem exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3 := by
  have h : Real.exp 1 ^ (3 : ℕ) = Real.exp (3 : ℕ) := Real.exp_one_pow 3
  have h2 : (2.7182818283 : ℝ) ^ (3 : ℕ) ≤ Real.exp 1 ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 3
  rw [h] at h2
  norm_num at h2 ⊢
  linarith

private theorem exp_two_ge_four : (4 : ℝ) ≤ Real.exp 2 := by
  have h : Real.exp 1 ^ (2 : ℕ) = Real.exp (2 : ℕ) := Real.exp_one_pow 2
  have h2 : (2.7182818283 : ℝ) ^ (2 : ℕ) ≤ Real.exp 1 ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 2
  rw [h] at h2
  norm_num at h2 ⊢
  linarith

private theorem exp_seven_ge_960 : (960 : ℝ) ≤ Real.exp 7 := by
  have h : Real.exp 1 ^ (7 : ℕ) = Real.exp (7 : ℕ) := Real.exp_one_pow 7
  have h2 : (2.7182818283 : ℝ) ^ (7 : ℕ) ≤ Real.exp 1 ^ (7 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7
  rw [h] at h2
  norm_num at h2 ⊢
  linarith

theorem const_one_le (hk : 1 ≤ k) : 24 * (k : ℝ) + Real.exp (3 * k) ≤ C₁ k := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h3k : (20 : ℝ) ≤ Real.exp (3 * (k : ℝ)) :=
    le_trans exp_three_ge_twenty (Real.exp_le_exp.mpr (by linarith))
  have hq : 1 + (k : ℝ) + (k : ℝ) ^ 2 / 2 ≤ Real.exp (k : ℝ) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have hsplit : Real.exp (4 * (k : ℝ)) = Real.exp (3 * (k : ℝ)) * Real.exp (k : ℝ) := by
    rw [← Real.exp_add]; ring_nf
  unfold C₁
  rw [hsplit]
  have hA : Real.exp (3 * (k : ℝ)) * (1 + (k : ℝ) + (k : ℝ) ^ 2 / 2)
      ≤ Real.exp (3 * (k : ℝ)) * Real.exp (k : ℝ) :=
    mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
  have hB : (20 : ℝ) * (k : ℝ) ≤ Real.exp (3 * (k : ℝ)) * (k : ℝ) :=
    mul_le_mul_of_nonneg_right h3k (by linarith)
  have hC : (20 : ℝ) * (k : ℝ) ^ 2 ≤ Real.exp (3 * (k : ℝ)) * (k : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h3k (by positivity)
  nlinarith [hA, hB, hC, hk2]

theorem const_two_le (hk : 1 ≤ k) :
    2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ k ≤ C₂ k := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hke : (k : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp ((k : ℝ))]
  have hexp2k : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) * Real.exp (k : ℝ) := by
    rw [← Real.exp_add]; ring_nf
  have h2k : ((k : ℝ)) ^ 2 ≤ Real.exp (2 * (k : ℝ)) := by
    rw [hexp2k]; nlinarith [Real.exp_pos ((k : ℝ))]
  have h4 : (4 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
    have hpow : (4 : ℝ) ^ k ≤ (Real.exp 1 ^ (2 : ℕ)) ^ k := by
      refine pow_le_pow_left₀ (by norm_num) ?_ k
      rw [Real.exp_one_pow 2]
      exact_mod_cast exp_two_ge_four
    calc (4 : ℝ) ^ k ≤ (Real.exp 1 ^ (2 : ℕ)) ^ k := hpow
      _ = Real.exp 1 ^ (2 * k) := by rw [← pow_mul]
      _ = Real.exp ((2 * k : ℕ) : ℝ) := Real.exp_one_pow (2 * k)
      _ = Real.exp (2 * (k : ℝ)) := by push_cast; ring_nf
  have hkexp : (k : ℝ) * Real.exp 20 ≤ Real.exp ((k : ℝ) + 20) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right hke (Real.exp_pos _).le
  have e1 : Real.exp (2 * (k : ℝ)) ≤ Real.exp (2 * (k : ℝ) + 20) :=
    Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp ((k : ℝ) + 20) ≤ Real.exp (2 * (k : ℝ) + 20) :=
    Real.exp_le_exp.mpr (by linarith)
  have e3 : (1 : ℝ) ≤ Real.exp (2 * (k : ℝ) + 20) := Real.one_le_exp (by linarith)
  have hbound : 2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ k
      ≤ 10 * Real.exp (2 * (k : ℝ) + 20) := by linarith
  have h10 : (10 : ℝ) * Real.exp (2 * (k : ℝ) + 20) ≤ Real.exp (2 * (k : ℝ) + 23) := by
    have hh : Real.exp (2 * (k : ℝ) + 23) = Real.exp 3 * Real.exp (2 * (k : ℝ) + 20) := by
      rw [← Real.exp_add]; ring_nf
    rw [hh]
    nlinarith [Real.exp_pos (2 * (k : ℝ) + 20), exp_three_ge_twenty]
  have hfin : 2 * (k : ℝ) + 23 ≤ Real.exp ((k : ℝ) + 7) := by
    have hqq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 7 by linarith)
    nlinarith
  unfold C₂
  exact le_trans (le_trans hbound h10) (Real.exp_le_exp.mpr hfin)

theorem exp_960_le_C₂ (k : ℕ) : Real.exp 960 ≤ C₂ k := by
  unfold C₂
  refine Real.exp_le_exp.mpr ?_
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h7 : Real.exp 7 ≤ Real.exp ((k : ℝ) + 7) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith [exp_seven_ge_960]

theorem growth_C₁ :
    Filter.Tendsto (fun k : ℕ => Real.log (C₁ k) / (4 : ℝ) ^ k) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 4 by norm_num)
  have h4 := h.const_mul (4 : ℝ)
  rw [mul_zero] at h4
  refine h4.congr (fun n => ?_)
  simp only [C₁, Real.log_exp, pow_one]
  ring

theorem growth_C₂ :
    Filter.Tendsto (fun k : ℕ => Real.log (Real.log (C₂ k)) / (4 : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 4 by norm_num)
  have h2 : Filter.Tendsto (fun n : ℕ => (7 : ℝ) / (4 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 4 by norm_num) (show (1 : ℝ) / 4 < 1 by norm_num)
    have h7 := hp.const_mul (7 : ℝ)
    rw [mul_zero] at h7
    refine h7.congr (fun n => ?_)
    rw [div_pow, one_pow]
    ring
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr (fun n => ?_)
  simp only [C₂, Real.log_exp, pow_one]
  ring

end NormalNumbers.PrimeModel.Params
