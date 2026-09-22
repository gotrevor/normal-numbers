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

theorem eps_pos (hR : Regime x k ε) : 0 < ε := by
  sorry

/-- `log log x > 7680 k`. -/
theorem loglog_gt (hR : Regime x k ε) : 7680 * (k : ℝ) < Real.log (Real.log x) := by
  sorry

/-- F1: `x^ε ≥ e³`. -/
theorem rpow_ge_exp_three (hR : Regime x k ε) : Real.exp 3 ≤ (x : ℝ) ^ ε := by
  sorry

/-- F1: `x^ε/2 ≤ y ≤ x^ε`. -/
theorem yOf_bounds (hR : Regime x k ε) :
    (x : ℝ) ^ ε / 2 ≤ (yOf x ε : ℝ) ∧ (yOf x ε : ℝ) ≤ (x : ℝ) ^ ε := by
  sorry

/-- F1: `y ≥ e²`. -/
theorem yOf_ge_exp_two (hR : Regime x k ε) : Real.exp 2 ≤ (yOf x ε : ℝ) := by
  sorry

/-- F1: `log y ≥ 2`. -/
theorem log_yOf_ge_two (hR : Regime x k ε) : 2 ≤ Real.log (yOf x ε) := by
  sorry

/-- F2: `1/ε ≤ log x / log y ≤ 2/ε`. -/
theorem log_ratio_bounds (hR : Regime x k ε) :
    1 / ε ≤ Real.log x / Real.log (yOf x ε) ∧ Real.log x / Real.log (yOf x ε) ≤ 2 / ε := by
  sorry

/-- F2: `σ ≥ 1/(4ε)`. -/
theorem sigmaOf_ge (hR : Regime x k ε) : 1 / (4 * ε) ≤ sigmaOf x ε := by
  sorry

/-- F2: the two size hypotheses of `brun_sifted_count_lower`. -/
theorem sigmaOf_thresholds (hR : Regime x k ε) :
    1920 * (k : ℝ) ≤ sigmaOf x ε
      ∧ 40 * Real.log ((4 : ℝ) ^ k * Real.exp (16 * k)) + 4 ≤ sigmaOf x ε := by
  sorry

/-- F3: `y^σ = x^{1/4}`. -/
theorem yOf_rpow_sigmaOf (hR : Regime x k ε) :
    (yOf x ε : ℝ) ^ sigmaOf x ε = (x : ℝ) ^ (1 / 4 : ℝ) := by
  sorry

/-- F4: `1 ≤ T` and `⌊T⌋₊^k ≤ x^{1/4}`. -/
theorem TOf_ge_one (hR : Regime x k ε) : 1 ≤ TOf x k := by
  sorry

theorem floor_TOf_pow_le (hR : Regime x k ε) :
    (Nat.floor (TOf x k) : ℝ) ^ k ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
  sorry

/-- F4: `k# ≤ 4^k`. -/
theorem primorial_le_four_pow_real (k : ℕ) : ((primorial k : ℕ) : ℝ) ≤ (4 : ℝ) ^ k := by
  sorry

/-- `k#` is coprime to every prime exceeding `k`. -/
theorem primorial_coprime_of_lt {p : ℕ} (hp : p.Prime) (hkp : k < p) :
    Nat.Coprime (primorial k) p := by
  sorry

/-! ### Absorption into the frozen sieve term `exp(−1/(8k²ε))` -/

/-- E3 / F5: `1/x ≤ exp(−1/(8k²ε))`. -/
theorem inv_x_le_expTerm (hR : Regime x k ε) :
    1 / (x : ℝ) ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  sorry

/-- The model tail: `k e^{20} / T^{1/(2 log y)} ≤ k e^{20} · exp(−1/(8k²ε))`. -/
theorem tail_absorbed (hR : Regime x k ε) :
    (k : ℝ) * Real.exp 20 / (TOf x k) ^ (1 / (2 * Real.log (yOf x ε)))
      ≤ (k : ℝ) * Real.exp 20 * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  sorry

/-- The sieve relative error: `exp(−σ/2) ≤ exp(−1/(8k²ε))`. -/
theorem sieve_absorbed (hR : Regime x k ε) :
    Real.exp (-(sigmaOf x ε) / 2) ≤ Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  sorry

/-- The accumulated arithmetic remainder:
`Q ⌊T⌋₊^k (y^σ)² / x ≤ 4^k · x^{−1/4} ≤ 4^k · exp(−1/(8k²ε))`. -/
theorem remainder_absorbed (hR : Regime x k ε) :
    ((primorial k : ℕ) : ℝ) * (Nat.floor (TOf x k) : ℝ) ^ k * ((yOf x ε : ℝ) ^ sigmaOf x ε) ^ 2 / x
      ≤ (4 : ℝ) ^ k * Real.exp (-1 / (8 * (k : ℝ) ^ 2 * ε)) := by
  sorry

/-! ### E2: Cauchy–Schwarz against the interval Mertens bound -/

/-- `∑_{y<p≤x} 1/p ≤ 36 log(1/ε)` (from `primeRecipSum_le` and F2). -/
theorem recip_Ioc_le (hR : Regime x k ε) :
    ∑ p ∈ (Finset.Ioc (yOf x ε) x).filter Nat.Prime, (1 : ℝ) / p
      ≤ 36 * Real.log (1 / ε) := by
  sorry

/-- **E2.**  `4k · recipSumIoc ≤ 24k · √log(1/ε) · √(2 recipSumIoc)`. -/
theorem recipSumIoc_cs (hR : Regime x k ε) (S : ℕ → Prop) [DecidablePred S] :
    4 * (k : ℝ) * recipSumIoc S (yOf x ε) x
      ≤ 24 * (k : ℝ) * (Real.sqrt (Real.log (1 / ε))
          * Real.sqrt (2 * recipSumIoc S (yOf x ε) x)) := by
  sorry

/-! ### Constants and their growth -/

/-- `C₁(k) = exp(4k)`. -/
noncomputable def C₁ (k : ℕ) : ℝ := Real.exp (4 * k)

/-- `C₂(k) = exp(exp(k+7))`. -/
noncomputable def C₂ (k : ℕ) : ℝ := Real.exp (Real.exp (k + 7))

theorem const_one_le (hk : 1 ≤ k) : 24 * (k : ℝ) + Real.exp (3 * k) ≤ C₁ k := by
  sorry

theorem const_two_le (hk : 1 ≤ k) :
    2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ k ≤ C₂ k := by
  sorry

theorem exp_960_le_C₂ (k : ℕ) : Real.exp 960 ≤ C₂ k := by
  sorry

theorem growth_C₁ :
    Filter.Tendsto (fun k : ℕ => Real.log (C₁ k) / (4 : ℝ) ^ k) Filter.atTop (nhds 0) := by
  sorry

theorem growth_C₂ :
    Filter.Tendsto (fun k : ℕ => Real.log (Real.log (C₂ k)) / (4 : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
  sorry

end NormalNumbers.PrimeModel.Params
