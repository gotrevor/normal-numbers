import NormalNumbers.PrimeModelKMT
import NormalNumbers.PrimeModelDensityMass

/-!
# Prime model, Part II-b: the family theorem

`papers/prime-model-assembly-2026-09-22.md`, Part II.

**Theorem.**  If `P` is a set of primes with `π_P(x) · log log x ≤ π(x)` eventually (`Sparse P`)
and `∑_{p∈P} 1/p = ∞` (`DivergentRecip P`), then `IsNormal 4 (subsetLambert P 4)`.

Schedule, built from the **actual accumulated mass** `S = recipSumLe P y_N`:

    ε_N = 2 / log log N,   y_N = ⌊N^{ε_N}⌋₊,   J_N = min(⌊log log log N / 24⌋₊, ⌊S/8⌋₊).

The four terms of `KMT_quant₂ C₁ C₂` (Part I) at `(k, x, ε) = (J_N, N, ε_N)`, and the L¹ tail
`(recipSumLe P (2N) + 5J_N + 12)/4^{J_N}` (`tail_error_L1`), all tend to `0`; the wiring theorem
`isNormal_subsetLambert_of_KMT_along` then gives normality.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.Family

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra

variable (P : ℕ → Prop) [DecidablePred P]

/-- `log log N`. -/
noncomputable def L2 (N : ℕ) : ℝ := Real.log (Real.log N)

/-- `log log log N`. -/
noncomputable def L3 (N : ℕ) : ℝ := Real.log (Real.log (Real.log N))

/-- `ε_N = 2 / log log N`. -/
noncomputable def epsN (N : ℕ) : ℝ := 2 / L2 N

/-- `y_N = ⌊N^{ε_N}⌋₊`. -/
noncomputable def yN (N : ℕ) : ℕ := ⌊(N : ℝ) ^ epsN N⌋₊

/-- `J_N = min(⌊L₃ N / 24⌋₊, ⌊recipSumLe P y_N / 8⌋₊)`. -/
noncomputable def JN (N : ℕ) : ℕ :=
  min ⌊L3 N / 24⌋₊ ⌊recipSumLe P (yN N) / 8⌋₊

/-! ### Elementary schedule facts -/

/-! #### Real-analysis helpers -/

private theorem log_nat_tendsto : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem L2_tendsto : Tendsto L2 atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto

theorem L3_tendsto : Tendsto L3 atTop atTop :=
  Real.tendsto_log_atTop.comp L2_tendsto

private theorem L3_eq (N : ℕ) : L3 N = Real.log (L2 N) := rfl

private theorem logN_gt_one {N : ℕ} (hN : 3 ≤ N) : 1 < Real.log N := by
  have h3 : Real.exp 1 < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log N := Real.log_lt_log (Real.exp_pos 1) h3

private theorem L2_pos {N : ℕ} (hN : 3 ≤ N) : 0 < L2 N :=
  Real.log_pos (logN_gt_one hN)

/-- `log N ≥ 1 + L₂ + L₂²/2`. -/
private theorem quad_bound {N : ℕ} (hN : 3 ≤ N) :
    1 + L2 N + (L2 N) ^ 2 / 2 ≤ Real.log N := by
  have h0 : (0 : ℝ) < Real.log N := lt_trans zero_lt_one (logN_gt_one hN)
  have hexp : Real.exp (L2 N) = Real.log N := Real.exp_log h0
  have := Real.quadratic_le_exp_of_nonneg (L2_pos hN).le
  rwa [hexp] at this

/-- `log t ≤ 2√t − 2` for `t > 0`. -/
private theorem log_le_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t - 2 := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by
    have hm := Real.log_mul (ne_of_gt hs) (ne_of_gt hs)
    rw [hsq] at hm
    linarith
  linarith

/-- The arithmetic consequences of `L₂ ≥ 2500`. -/
private theorem L3_bounds {N : ℕ} (hL : 2500 ≤ L2 N) :
    1 ≤ L3 N ∧ L3 N ≤ L2 N / 2 ∧ 42 + 24 * L3 N ≤ L2 N := by
  have hpos : 0 < L2 N := by linarith
  have hs : (50 : ℝ) ≤ Real.sqrt (L2 N) := by
    have : Real.sqrt (2500 : ℝ) ≤ Real.sqrt (L2 N) := Real.sqrt_le_sqrt hL
    rwa [show (2500 : ℝ) = 50 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 50)] at this
  have hsq : Real.sqrt (L2 N) * Real.sqrt (L2 N) = L2 N := Real.mul_self_sqrt hpos.le
  have hlog : L3 N ≤ 2 * Real.sqrt (L2 N) - 2 := by
    rw [L3_eq]; exact log_le_sqrt hpos
  have hone : 1 ≤ L3 N := by
    rw [L3_eq, Real.le_log_iff_exp_le hpos]
    linarith [Real.exp_one_lt_d9]
  refine ⟨hone, ?_, ?_⟩ <;> nlinarith [hs, hsq, hlog]


/-! #### The schedule facts -/

/-- All the `y_N` facts, from `3 ≤ N` and `L₂ N ≥ 2500`. -/
private theorem yN_core {N : ℕ} (hN : 3 ≤ N) (hL : 2500 ≤ L2 N) :
    2 ≤ yN N ∧ yN N ≤ N ∧ Real.log N / L2 N ≤ Real.log (yN N) ∧
      L2 N / 2 ≤ Real.log (Real.log (yN N)) ∧ Real.log N - 1 ≤ (yN N : ℝ) := by
  obtain ⟨hL3one, hL3half, -⟩ := L3_bounds hL
  have hpos : 0 < L2 N := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hquad : 1 + L2 N + (L2 N) ^ 2 / 2 ≤ Real.log N := quad_bound hN
  have hepsdef : epsN N = 2 / L2 N := rfl
  have hepsLe1 : epsN N ≤ 1 := by
    rw [hepsdef, div_le_one hpos]; linarith
  set u : ℝ := (N : ℝ) ^ epsN N with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hNpos _
  have hlogu : Real.log u = epsN N * Real.log N := by
    rw [hudef, Real.log_rpow hNpos]
  -- `log u ≥ L₂`
  have hratio : L2 N / 2 ≤ Real.log N / L2 N := by
    rw [le_div_iff₀ hpos]; nlinarith
  have hlogu_ge : L2 N ≤ Real.log u := by
    rw [hlogu, hepsdef]
    have : L2 N * L2 N ≤ 2 * Real.log N := by nlinarith
    calc L2 N = L2 N * L2 N / L2 N := by field_simp
      _ ≤ 2 * Real.log N / L2 N := by gcongr
      _ = 2 / L2 N * Real.log N := by ring
  have hubig : (2500 : ℝ) ≤ u := by
    have h1 : Real.exp (L2 N) ≤ u := by
      have : u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      rw [this]; exact Real.exp_le_exp.mpr hlogu_ge
    have h2 : L2 N + 1 ≤ Real.exp (L2 N) := Real.add_one_le_exp _
    linarith
  have hy : (yN N : ℝ) = ((⌊u⌋₊ : ℕ) : ℝ) := rfl
  have hyle : (yN N : ℝ) ≤ u := by rw [hy]; exact Nat.floor_le hu0.le
  have hygt : u - 1 < (yN N : ℝ) := by
    rw [hy]; linarith [Nat.lt_floor_add_one u]
  have h2y : 2 ≤ yN N := by
    have : (2 : ℝ) ≤ (yN N : ℝ) := by linarith
    exact_mod_cast this
  have hyN : yN N ≤ N := by
    have hle : u ≤ (N : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 hepsLe1
      rwa [Real.rpow_one] at this
    have : (⌊u⌋₊ : ℕ) ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_le_floor hle
    rwa [Nat.floor_natCast] at this
  -- `log y_N ≥ log N / L₂`
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlogy : Real.log N / L2 N ≤ Real.log (yN N) := by
    have h1 : u / 2 ≤ (yN N : ℝ) := by linarith
    have h2 : Real.log (u / 2) ≤ Real.log (yN N) := Real.log_le_log (by positivity) h1
    rw [Real.log_div (ne_of_gt hu0) (by norm_num)] at h2
    rw [hlogu, hepsdef] at h2
    have h3 : 2 / L2 N * Real.log N = Real.log N / L2 N + Real.log N / L2 N := by
      field_simp; ring
    linarith
  have hlogNy : Real.log N - 1 ≤ (yN N : ℝ) := by
    have hexp : Real.exp (L2 N) = Real.log N := Real.exp_log (by linarith)
    have h1 : Real.exp (L2 N) ≤ u := by
      have : u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      rw [this]; exact Real.exp_le_exp.mpr hlogu_ge
    rw [hexp] at h1
    linarith
  refine ⟨h2y, hyN, hlogy, ?_, hlogNy⟩
  have hlogypos : 0 < Real.log (yN N) := by linarith
  have h4 : Real.log (Real.log N / L2 N) ≤ Real.log (Real.log (yN N)) :=
    Real.log_le_log (by positivity) hlogy
  rw [Real.log_div (by linarith) (ne_of_gt hpos)] at h4
  have : Real.log (Real.log N) = L2 N := rfl
  rw [this] at h4
  have h5 : Real.log (L2 N) = L3 N := (L3_eq N).symm
  rw [h5] at h4
  linarith

/-- The frozen `ε`-window holds eventually. -/
theorem epsN_range : ∀ᶠ N : ℕ in atTop,
    1 / Real.log (Real.log N) < epsN N ∧ epsN N < 1 / 2 := by
  filter_upwards [L2_tendsto.eventually_ge_atTop 2500] with N hL
  have hpos : 0 < L2 N := by linarith
  have hd : epsN N = 2 / L2 N := rfl
  constructor
  · show 1 / L2 N < epsN N
    rw [hd, div_lt_div_iff₀ hpos hpos]
    linarith
  · rw [hd, div_lt_div_iff₀ hpos (by norm_num)]
    linarith

/-- `y_N ≥ 2`, `y_N ≤ N`, and `log log y_N ≥ (log log N)/2`, eventually. -/
theorem yN_facts : ∀ᶠ N : ℕ in atTop,
    2 ≤ yN N ∧ yN N ≤ N ∧ L2 N / 2 ≤ Real.log (Real.log (yN N)) := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500] with N hN hL
  obtain ⟨h1, h2, -, h4, -⟩ := yN_core hN hL
  exact ⟨h1, h2, h4⟩

theorem yN_tendsto : Tendsto yN atTop atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    log_nat_tendsto.eventually_ge_atTop ((b : ℝ) + 1)] with N hN hL hlog
  obtain ⟨-, -, -, -, h5⟩ := yN_core hN hL
  have : (b : ℝ) ≤ (yN N : ℝ) := by linarith
  exact_mod_cast this

private theorem recipSumLe_nonneg (x : ℕ) : 0 ≤ recipSumLe P x :=
  Finset.sum_nonneg fun p _ => by positivity

theorem JN_le_L3 : ∀ᶠ N : ℕ in atTop, (JN P N : ℝ) ≤ L3 N / 24 := by
  filter_upwards [L3_tendsto.eventually_ge_atTop 0] with N hL
  have h1 : JN P N ≤ ⌊L3 N / 24⌋₊ := min_le_left _ _
  have h2 : ((⌊L3 N / 24⌋₊ : ℕ) : ℝ) ≤ L3 N / 24 := Nat.floor_le (by linarith)
  have h3 : (JN P N : ℝ) ≤ ((⌊L3 N / 24⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem JN_le_mass (N : ℕ) : 8 * (JN P N : ℝ) ≤ recipSumLe P (yN N) := by
  have hS := recipSumLe_nonneg P (yN N)
  have h1 : JN P N ≤ ⌊recipSumLe P (yN N) / 8⌋₊ := min_le_right _ _
  have h2 : ((⌊recipSumLe P (yN N) / 8⌋₊ : ℕ) : ℝ) ≤ recipSumLe P (yN N) / 8 :=
    Nat.floor_le (by positivity)
  have h3 : (JN P N : ℝ) ≤ ((⌊recipSumLe P (yN N) / 8⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- The accumulated mass along the schedule tends to infinity. -/
private theorem mass_tendsto (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => recipSumLe P (yN N)) atTop atTop :=
  (recipSumLe_tendsto_atTop P hP).comp yN_tendsto

theorem JN_tendsto (hP : DivergentRecip P) : Tendsto (JN P) atTop atTop := by
  have hA : Tendsto (fun N : ℕ => ⌊L3 N / 24⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (L3_tendsto.atTop_div_const (by norm_num))
  have hB : Tendsto (fun N : ℕ => ⌊recipSumLe P (yN N) / 8⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((mass_tendsto P hP).atTop_div_const (by norm_num))
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hA.eventually_ge_atTop b, hB.eventually_ge_atTop b] with N h1 h2
  exact le_min h1 h2

/-! ### The mass bounds along the schedule -/

/-- The dominated-Abel bound, uniformly in the upper endpoint. -/
private theorem fresh_bound (hS : Sparse P) : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, yN N ≤ M →
    recipSumIoc P (yN N) M
      ≤ (2 / L2 N) * (9 + 12 * Real.log (Real.log M / Real.log (yN N))) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hS
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    yN_tendsto.eventually_ge_atTop x₀] with N hN hL hy0 M hM
  obtain ⟨h2y, -, hlogy, hloglogy, -⟩ := yN_core hN hL
  have hpos : 0 < L2 N := by linarith
  have hδ : (0 : ℝ) ≤ 2 / L2 N := by positivity
  have hylogpos : 0 < Real.log (yN N) := by
    have : L2 N / 2 ≤ Real.log N / L2 N := by
      rw [le_div_iff₀ hpos]; nlinarith [quad_bound hN]
    linarith
  have hdom : ∀ t : ℕ, yN N < t → t ≤ M + 1 →
      (piP P t : ℝ) ≤ (2 / L2 N) * (t.primesBelow.card : ℝ) := by
    intro t ht _
    have ht0 : x₀ ≤ t := le_trans hy0 ht.le
    have hsp := hx₀ t ht0
    have hty : (yN N : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.le
    have hlt : Real.log (yN N) ≤ Real.log t :=
      Real.log_le_log (by positivity) hty
    have hllt : Real.log (Real.log (yN N)) ≤ Real.log (Real.log t) :=
      Real.log_le_log hylogpos hlt
    have hbig : L2 N / 2 ≤ Real.log (Real.log t) := le_trans hloglogy hllt
    have hppos : (0 : ℝ) ≤ (piP P t : ℝ) := Nat.cast_nonneg _
    have : (piP P t : ℝ) * (L2 N / 2) ≤ (t.primesBelow.card : ℝ) := by
      refine le_trans ?_ hsp
      exact mul_le_mul_of_nonneg_left hbig hppos
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith
  exact recipSumIoc_le_of_dominated' P hδ h2y hM hdom

/-- Fresh mass between `y_N` and `N` (from (M1') with `δ = 1/log log y_N ≤ 2/L₂N`). -/
theorem fresh_mass (hS : Sparse P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yN N) N ≤ (2 / L2 N) * (9 + 12 * L3 N) := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    fresh_bound P hS] with N hN hL hfb
  obtain ⟨-, hyN, hlogy, -, -⟩ := yN_core hN hL
  have hpos : 0 < L2 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hylogpos : 0 < Real.log (yN N) := by
    have : L2 N / 2 ≤ Real.log N / L2 N := by
      rw [le_div_iff₀ hpos]; nlinarith [quad_bound hN]
    linarith
  have hratio : Real.log N / Real.log (yN N) ≤ L2 N := by
    rw [div_le_iff₀ hylogpos]
    have : Real.log N / L2 N * L2 N ≤ Real.log (yN N) * L2 N := by
      exact mul_le_mul_of_nonneg_right hlogy hpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    linarith
  have hlogratio : Real.log (Real.log N / Real.log (yN N)) ≤ L3 N := by
    rw [L3_eq]
    exact Real.log_le_log (div_pos (by linarith) hylogpos) hratio
  have := hfb N hyN
  have hδ : (0 : ℝ) ≤ 2 / L2 N := by positivity
  nlinarith [this, hlogratio, hδ]

/-- Fresh mass between `y_N` and `2N` is eventually at most `1`. -/
theorem fresh_mass_two (hS : Sparse P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yN N) (2 * N) ≤ 1 := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    fresh_bound P hS] with N hN hL hfb
  obtain ⟨-, hyN, hlogy, -, -⟩ := yN_core hN hL
  obtain ⟨hL3one, -, hL3big⟩ := L3_bounds hL
  have hpos : 0 < L2 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hylogpos : 0 < Real.log (yN N) := by
    have : L2 N / 2 ≤ Real.log N / L2 N := by
      rw [le_div_iff₀ hpos]; nlinarith [quad_bound hN]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    rw [hcast, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hratio : Real.log ((2 * N : ℕ) : ℝ) / Real.log (yN N) ≤ 2 * L2 N := by
    rw [div_le_iff₀ hylogpos]
    have h1 : Real.log N / L2 N * L2 N ≤ Real.log (yN N) * L2 N :=
      mul_le_mul_of_nonneg_right hlogy hpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h1
    nlinarith
  have hlogratio : Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yN N)) ≤ 1 + L3 N := by
    have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by
      rw [hcast, Real.log_mul (by norm_num) (by positivity)]
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have h2 : Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yN N)) ≤ Real.log (2 * L2 N) :=
      Real.log_le_log (div_pos hlog2Npos hylogpos) hratio
    rw [Real.log_mul (by norm_num) (ne_of_gt hpos), ← L3_eq] at h2
    linarith
  have hb := hfb (2 * N) (le_trans hyN (by omega))
  have hδ : (0 : ℝ) ≤ 2 / L2 N := by positivity
  have hstep : recipSumIoc P (yN N) (2 * N) ≤ (2 / L2 N) * (9 + 12 * (1 + L3 N)) := by
    refine le_trans hb ?_
    have : (9 : ℝ) + 12 * Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yN N))
        ≤ 9 + 12 * (1 + L3 N) := by linarith
    exact mul_le_mul_of_nonneg_left this hδ
  have hfin : (2 / L2 N) * (9 + 12 * (1 + L3 N)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hpos]
    linarith
  linarith

/-! ### The four limits -/

private theorem tendsto_log_div_rpow {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => Real.log t / t ^ r) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero

private theorem C₁_pos (k : ℕ) : (0 : ℝ) < C₁ k := Real.exp_pos _

/-- Term 1: `C₁(J) √log(1/ε) √(2 recipSumIoc) → 0`. -/
theorem term_one (hS : Sparse P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => C₁ (JN P N) *
      (Real.sqrt (Real.log (1 / epsN N)) * Real.sqrt (2 * recipSumIoc P (yN N) N)))
      atTop (𝓝 0) := by
  have hG : Tendsto (fun N : ℕ => 10 * (Real.log (L2 N) / (L2 N) ^ (1/3 : ℝ))) atTop (𝓝 0) := by
    have h := ((tendsto_log_div_rpow (r := (1/3 : ℝ)) (by norm_num)).const_mul (10 : ℝ)).comp
      L2_tendsto
    simpa [Function.comp_def] using h
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hG
  · exact mul_nonneg (C₁_pos _).le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    fresh_mass P hS, JN_le_L3 P] with N hN hL hfm hJ
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  set t : ℝ := L2 N with htdef
  set u : ℝ := L3 N with hudef
  have ht0 : 0 < t := by rw [htdef]; linarith
  have hulog : u = Real.log t := L3_eq N
  have hA0 : 0 ≤ recipSumIoc P (yN N) N := recipSumIoc_nonneg P _ _
  -- the fresh mass
  have h2A : 2 * recipSumIoc P (yN N) N ≤ 84 * u / t := by
    have hdiv : (2 / t) * (9 + 12 * u) ≤ 42 * u / t := by
      have h : (2 : ℝ) * (9 + 12 * u) ≤ 42 * u := by linarith
      calc (2 / t) * (9 + 12 * u) = (2 * (9 + 12 * u)) / t := by ring
        _ ≤ (42 * u) / t := by gcongr
    have : 2 * recipSumIoc P (yN N) N ≤ 2 * ((2 / t) * (9 + 12 * u)) := by linarith
    calc 2 * recipSumIoc P (yN N) N ≤ 2 * ((2 / t) * (9 + 12 * u)) := this
      _ ≤ 2 * (42 * u / t) := by linarith
      _ = 84 * u / t := by ring
  -- the `log(1/ε)` factor
  have hepslog : Real.log (1 / epsN N) ≤ u := by
    have he : (1 : ℝ) / epsN N = t / 2 := by
      show (1 : ℝ) / (2 / t) = t / 2
      field_simp
    rw [he, Real.log_div (ne_of_gt ht0) (by norm_num), ← hulog]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  -- the product of square roots
  have hsqrt : Real.sqrt (Real.log (1 / epsN N)) * Real.sqrt (2 * recipSumIoc P (yN N) N)
      ≤ 10 * u / Real.sqrt t := by
    have h1 : Real.sqrt (Real.log (1 / epsN N)) ≤ Real.sqrt u := Real.sqrt_le_sqrt hepslog
    have h2 : Real.sqrt (2 * recipSumIoc P (yN N) N) ≤ Real.sqrt (84 * u / t) :=
      Real.sqrt_le_sqrt h2A
    have h3 : Real.sqrt u * Real.sqrt (84 * u / t) ≤ 10 * u / Real.sqrt t := by
      rw [← Real.sqrt_mul (by linarith)]
      have hsq : (10 * u / Real.sqrt t) ^ 2 = 100 * u ^ 2 / t := by
        rw [div_pow, Real.sq_sqrt ht0.le]; ring
      have hle : u * (84 * u / t) ≤ (10 * u / Real.sqrt t) ^ 2 := by
        rw [hsq]
        have : u * (84 * u / t) = 84 * u ^ 2 / t := by ring
        rw [this]
        exact div_le_div_of_nonneg_right (by nlinarith) ht0.le
      calc Real.sqrt (u * (84 * u / t)) ≤ Real.sqrt ((10 * u / Real.sqrt t) ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = 10 * u / Real.sqrt t := Real.sqrt_sq (by positivity)
    calc Real.sqrt (Real.log (1 / epsN N)) * Real.sqrt (2 * recipSumIoc P (yN N) N)
        ≤ Real.sqrt u * Real.sqrt (84 * u / t) := by
          exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ 10 * u / Real.sqrt t := h3
  -- the constant
  have hC : C₁ (JN P N) ≤ Real.exp (u / 6) := by
    show Real.exp (4 * (JN P N : ℝ)) ≤ Real.exp (u / 6)
    exact Real.exp_le_exp.mpr (by linarith)
  -- assemble
  have hfin : Real.exp (u / 6) * (10 * u / Real.sqrt t) = 10 * (u / t ^ (1/3 : ℝ)) := by
    have h1 : Real.exp (u / 6) = t ^ (1/6 : ℝ) := by
      rw [Real.rpow_def_of_pos ht0]
      congr 1
      rw [hulog]; ring
    have h2 : Real.sqrt t = t ^ (1/2 : ℝ) := Real.sqrt_eq_rpow t
    have h3 : t ^ (1/6 : ℝ) / t ^ (1/2 : ℝ) = (t ^ (1/3 : ℝ))⁻¹ := by
      rw [← Real.rpow_sub ht0, show (1/6 - 1/2 : ℝ) = -(1/3) by norm_num,
        Real.rpow_neg ht0.le]
    rw [h1, h2, show t ^ (1/6 : ℝ) * (10 * u / t ^ (1/2 : ℝ))
      = 10 * u * (t ^ (1/6 : ℝ) / t ^ (1/2 : ℝ)) by ring, h3, div_eq_mul_inv]
    ring
  calc C₁ (JN P N) * (Real.sqrt (Real.log (1 / epsN N))
        * Real.sqrt (2 * recipSumIoc P (yN N) N))
      ≤ Real.exp (u / 6) * (10 * u / Real.sqrt t) := by
        refine mul_le_mul hC hsqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (Real.exp_pos _).le
    _ = 10 * (u / t ^ (1/3 : ℝ)) := hfin
    _ = 10 * (Real.log (L2 N) / (L2 N) ^ (1/3 : ℝ)) := by rw [← hulog]

/-- Term 2: `C₁(J) exp(−recipSumLe P y_N) → 0` (uses `8J ≤ S`). -/
theorem term_two (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => C₁ (JN P N) * Real.exp (- recipSumLe P (yN N))) atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => Real.exp (- (recipSumLe P (yN N) / 2))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp ((mass_tendsto P hP).atTop_div_const (by norm_num))
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N => ?_) hg
  · exact mul_nonneg (C₁_pos _).le (Real.exp_pos _).le
  · have hJ := JN_le_mass P N
    calc C₁ (JN P N) * Real.exp (- recipSumLe P (yN N))
        = Real.exp (4 * (JN P N : ℝ) + - recipSumLe P (yN N)) := by
          rw [Real.exp_add]; rfl
      _ ≤ Real.exp (- (recipSumLe P (yN N) / 2)) := Real.exp_le_exp.mpr (by linarith)

/-- `c (log t)² ≤ t^r` eventually, for any `r, c > 0`. -/
private theorem eventually_sq_log_le {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, c * (Real.log t) ^ 2 ≤ t ^ r := by
  have h := tendsto_log_div_rpow (r := r / 2) (by linarith)
  have h2 : Tendsto (fun t : ℝ => (Real.log t / t ^ (r / 2)) * (Real.log t / t ^ (r / 2)))
      atTop (𝓝 0) := by simpa using h.mul h
  have h3 : ∀ᶠ t : ℝ in atTop,
      (Real.log t / t ^ (r / 2)) * (Real.log t / t ^ (r / 2)) ≤ 1 / c :=
    h2.eventually_le_const (by positivity)
  filter_upwards [h3, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have hrp : 0 < t ^ (r / 2) := Real.rpow_pos_of_pos ht0 _
  have hmul : t ^ (r / 2) * t ^ (r / 2) = t ^ r := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have h4 := mul_le_mul_of_nonneg_right ht (le_of_lt (mul_pos hrp hrp))
  have h5 : (Real.log t / t ^ (r / 2)) * (Real.log t / t ^ (r / 2)) * (t ^ (r / 2) * t ^ (r / 2))
      = (Real.log t) ^ 2 := by field_simp
  rw [h5, hmul] at h4
  have h6 := mul_le_mul_of_nonneg_left h4 hc.le
  rw [show c * (1 / c * t ^ r) = t ^ r by field_simp] at h6
  exact h6

/-- Term 3: `C₂(J) exp(−1/(8J²ε_N)) → 0`. -/
theorem term_three (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => C₂ (JN P N) * Real.exp (-1 / (8 * (JN P N : ℝ) ^ 2 * epsN N)))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => Real.exp (-(Real.exp 7 * (L2 N) ^ (1/24 : ℝ))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (L2 N) ^ (1/24 : ℝ)) atTop atTop := by
      have := (tendsto_rpow_atTop (y := (1/24 : ℝ)) (by norm_num)).comp L2_tendsto
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun N : ℕ => Real.exp 7 * (L2 N) ^ (1/24 : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (Real.exp_pos 7) h1
    have h3 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)
    simpa [Function.comp_def] using h3
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hg
  · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JN_le_L3 P,
    (JN_tendsto P hP).eventually_ge_atTop 1,
    L2_tendsto.eventually (eventually_sq_log_le (r := (23/24 : ℝ)) (c := 2 * Real.exp 7)
      (by norm_num) (by positivity))] with N hN hL hJ hJ1 hsq
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  set t : ℝ := L2 N with htdef
  set u : ℝ := L3 N with hudef
  set J : ℝ := (JN P N : ℝ) with hJdef
  have ht0 : 0 < t := by rw [htdef]; linarith
  have hulog : u = Real.log t := L3_eq N
  have hJpos : (1 : ℝ) ≤ J := by rw [hJdef]; exact_mod_cast hJ1
  have h16pos : (0 : ℝ) < 16 * J ^ 2 := by nlinarith
  have hrp : 0 < t ^ (1/24 : ℝ) := Real.rpow_pos_of_pos ht0 _
  -- the exponent
  have hden : -1 / (8 * J ^ 2 * epsN N) = -(t / (16 * J ^ 2)) := by
    have he : epsN N = 2 / t := rfl
    rw [he]
    field_simp
    ring
  -- (a)
  have ha : Real.exp (J + 7) ≤ Real.exp 7 * t ^ (1/24 : ℝ) := by
    have h1 : Real.exp (J + 7) ≤ Real.exp (u / 24 + 7) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (u / 24 + 7) = Real.exp 7 * t ^ (1/24 : ℝ) := by
      rw [Real.rpow_def_of_pos ht0, ← hulog, Real.exp_add,
        show u * (1/24 : ℝ) = u / 24 by ring]
      ring
    linarith [h1, h2.le, h2.ge]
  -- (b)
  have hb : 2 * Real.exp 7 * t ^ (1/24 : ℝ) ≤ t / (16 * J ^ 2) := by
    have hprod : t ^ (1/24 : ℝ) * t ^ (23/24 : ℝ) = t := by
      rw [← Real.rpow_add ht0]; norm_num
    have h16 : 16 * J ^ 2 ≤ u ^ 2 := by nlinarith
    have hsq' : 2 * Real.exp 7 * u ^ 2 ≤ t ^ (23/24 : ℝ) := by rw [hulog]; exact hsq
    rw [le_div_iff₀ h16pos]
    calc 2 * Real.exp 7 * t ^ (1/24 : ℝ) * (16 * J ^ 2)
        ≤ 2 * Real.exp 7 * t ^ (1/24 : ℝ) * u ^ 2 := by
          refine mul_le_mul_of_nonneg_left h16 (by positivity)
      _ = t ^ (1/24 : ℝ) * (2 * Real.exp 7 * u ^ 2) := by ring
      _ ≤ t ^ (1/24 : ℝ) * t ^ (23/24 : ℝ) := mul_le_mul_of_nonneg_left hsq' hrp.le
      _ = t := hprod
  -- assemble
  have hcast : C₂ (JN P N) * Real.exp (-1 / (8 * J ^ 2 * epsN N))
      = Real.exp (Real.exp (J + 7) + -(t / (16 * J ^ 2))) := by
    rw [hden, Real.exp_add]
    rfl
  rw [hcast]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `L₃(2N) ≤ L₃(N) + 1` eventually. -/
private theorem L3_two_le : ∀ᶠ N : ℕ in atTop, L3 (2 * N) ≤ L3 N + 1 := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500] with N hN hL
  have hpos : 0 < L2 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hNne : ((N : ℝ)) ≠ 0 := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact ne_of_gt (by linarith)
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
    rw [hcast, Real.log_mul (by norm_num) hNne]
  have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by rw [hlog2N]; linarith
  have hL2mono : L2 N ≤ L2 (2 * N) := by
    refine Real.log_le_log (by linarith) ?_
    rw [hlog2N]; linarith
  have hL2two : L2 (2 * N) ≤ L2 N + 1 := by
    have h1 : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by rw [hlog2N]; linarith
    have h2 : L2 (2 * N) ≤ Real.log (2 * Real.log N) := Real.log_le_log hlog2Npos h1
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have : Real.log (Real.log N) = L2 N := rfl
    linarith [h2, this.le, this.ge]
  have h3 : L3 (2 * N) ≤ Real.log (L2 N + 1) :=
    Real.log_le_log (show (0:ℝ) < L2 (2 * N) by linarith) hL2two
  have h4 : Real.log (L2 N + 1) ≤ Real.log (2 * L2 N) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) (ne_of_gt hpos), ← L3_eq] at h4
  linarith

/-- The L¹ tail: `(recipSumLe P (2N) + 5J + 12)/4^J → 0`. -/
theorem tail_family (hS : Sparse P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JN P N : ℝ) + 12) / (4 : ℝ) ^ JN P N)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := recipSumLe_le_of_sparse P hS
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
  have hC2 : ∀ᶠ N : ℕ in atTop, recipSumLe P (2 * N) ≤ C + 100 * L3 (2 * N) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact hN₀ (2 * N) (by omega)
  set K : ℝ := |C| + 113 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hCK : C ≤ K - 113 := by
    rw [hKdef]; simp [le_abs_self]
  set ρ : ℝ := Real.log 4 / 24 with hρdef
  have hρ0 : 0 < ρ := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    rw [hρdef]; linarith
  -- majorant 1
  have hf : Tendsto (fun N : ℕ => (13 * (JN P N : ℝ) + 21) / (4 : ℝ) ^ (JN P N))
      atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
    have hsum : Tendsto
        (fun n : ℕ => 13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n))
        atTop (𝓝 0) := by
      simpa using (h1.const_mul (13 : ℝ)).add (h0.const_mul (21 : ℝ))
    have hcongr : ∀ n : ℕ,
        13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n)
          = (13 * (n : ℝ) + 21) / (4 : ℝ) ^ n := by
      intro n; rw [pow_one, pow_zero]; ring
    refine Tendsto.congr (fun N => ?_) (hsum.comp (JN_tendsto P hP))
    simp only [Function.comp_apply, pow_one, pow_zero]
    ring
  -- majorant 2
  have hgt : Tendsto
      (fun N : ℕ => 4 * K / (L2 N) ^ ρ + 404 * (Real.log (L2 N) / (L2 N) ^ ρ))
      atTop (𝓝 0) := by
    have hA : Tendsto (fun N : ℕ => 4 * K / (L2 N) ^ ρ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (L2 N) ^ ρ) atTop atTop := by
        have := (tendsto_rpow_atTop hρ0).comp L2_tendsto
        simpa [Function.comp_def] using this
      simpa using h1.const_div_atTop (4 * K)
    have hB : Tendsto (fun N : ℕ => 404 * (Real.log (L2 N) / (L2 N) ^ ρ)) atTop (𝓝 0) := by
      have := ((tendsto_log_div_rpow hρ0).const_mul (404 : ℝ)).comp L2_tendsto
      simpa [Function.comp_def] using this
    simpa using hA.add hB
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ (by simpa using hf.add hgt)
  · have := recipSumLe_nonneg P (2 * N)
    positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JN_le_L3 P,
    fresh_mass_two P hS, L3_two_le, hC2, yN_facts] with N hN hL hJle hfm2 hL3two hCN hyf
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  obtain ⟨-, hyN, -⟩ := hyf
  have ht0 : 0 < L2 N := by linarith
  have hulog : L3 N = Real.log (L2 N) := L3_eq N
  have hrp : (0 : ℝ) < (L2 N) ^ ρ := Real.rpow_pos_of_pos ht0 _
  have hpow0 : (0 : ℝ) < (4 : ℝ) ^ (JN P N) := by positivity
  have hfnn : (0 : ℝ) ≤ (13 * (JN P N : ℝ) + 21) / (4 : ℝ) ^ (JN P N) := by positivity
  have hgnn : (0 : ℝ) ≤ 4 * K / (L2 N) ^ ρ + 404 * (Real.log (L2 N) / (L2 N) ^ ρ) := by
    have : (0 : ℝ) ≤ Real.log (L2 N) := by rw [← hulog]; linarith
    positivity
  rcases le_total (⌊L3 N / 24⌋₊) (⌊recipSumLe P (yN N) / 8⌋₊) with hcase | hcase
  · -- `J = ⌊L₃/24⌋₊`
    have hJeq : JN P N = ⌊L3 N / 24⌋₊ := min_eq_left hcase
    have hJlow : L3 N / 24 - 1 ≤ (JN P N : ℝ) := by
      have := Nat.lt_floor_add_one (L3 N / 24)
      rw [← hJeq] at this
      linarith
    have hpow : (L2 N) ^ ρ / 4 ≤ (4 : ℝ) ^ (JN P N) := by
      have h1 : (4 : ℝ) ^ (JN P N) = (4 : ℝ) ^ ((JN P N : ℕ) : ℝ) := (Real.rpow_natCast 4 _).symm
      have h2 : (4 : ℝ) ^ (L3 N / 24 - 1) ≤ (4 : ℝ) ^ ((JN P N : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (4 : ℝ) ^ (L3 N / 24 - 1) = (L2 N) ^ ρ / 4 := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        congr 1
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4), Real.rpow_def_of_pos ht0, hρdef,
          hulog]
        congr 1
        ring
      rw [h1, ← h3]; exact h2
    have hnum : recipSumLe P (2 * N) + 5 * (JN P N : ℝ) + 12 ≤ K + 101 * Real.log (L2 N) := by
      have h5 : 5 * (JN P N : ℝ) ≤ L3 N := by linarith
      rw [← hulog]
      linarith [hCN, hL3two]
    have hK101 : (0 : ℝ) ≤ K + 101 * Real.log (L2 N) := by
      have : (0 : ℝ) ≤ Real.log (L2 N) := by rw [← hulog]; linarith
      linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JN P N : ℝ) + 12) / (4 : ℝ) ^ (JN P N)
        ≤ (K + 101 * Real.log (L2 N)) / ((L2 N) ^ ρ / 4) :=
      div_le_div₀ hK101 hnum (by positivity) hpow
    have hfin : (K + 101 * Real.log (L2 N)) / ((L2 N) ^ ρ / 4)
        = 4 * K / (L2 N) ^ ρ + 404 * (Real.log (L2 N) / (L2 N) ^ ρ) := by
      field_simp
      ring
    linarith [hstep, hfin.le, hfin.ge, hfnn]
  · -- `J = ⌊S/8⌋₊`
    have hJeq : JN P N = ⌊recipSumLe P (yN N) / 8⌋₊ := min_eq_right hcase
    have hSlt : recipSumLe P (yN N) < 8 * (JN P N : ℝ) + 8 := by
      have := Nat.lt_floor_add_one (recipSumLe P (yN N) / 8)
      rw [← hJeq] at this
      linarith
    have hsplit : recipSumLe P (2 * N)
        = recipSumLe P (yN N) + recipSumIoc P (yN N) (2 * N) :=
      recipSumLe_add_recipSumIoc P (le_trans hyN (by omega))
    have hnum : recipSumLe P (2 * N) + 5 * (JN P N : ℝ) + 12 ≤ 13 * (JN P N : ℝ) + 21 := by
      rw [hsplit]; linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JN P N : ℝ) + 12) / (4 : ℝ) ^ (JN P N)
        ≤ (13 * (JN P N : ℝ) + 21) / (4 : ℝ) ^ (JN P N) :=
      div_le_div_of_nonneg_right hnum hpow0.le
    linarith [hstep, hgnn]
/-! ### Assembly -/

/-- `TailOK P J_N`. -/
theorem tailOK_family (hS : Sparse P) (hP : DivergentRecip P) : TailOK P (JN P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_family P hS hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JN P N) N hN

/-- `KMT_along P J_N`. -/
theorem kmt_along_family (hS : Sparse P) (hP : DivergentRecip P) : KMT_along P (JN P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      C₁ (JN P N) * (Real.sqrt (Real.log (1 / epsN N))
          * Real.sqrt (2 * recipSumIoc P (yN N) N))
        + C₁ (JN P N) * Real.exp (- recipSumLe P (yN N))
        + C₂ (JN P N) * Real.exp (-1 / (8 * (JN P N : ℝ) ^ 2 * epsN N))) atTop (𝓝 0) := by
    have := ((term_one P hS hP).add (term_two P hP)).add (term_three P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [epsN_range, (JN_tendsto P hP).eventually_ge_atTop (h.natAbs + 1),
    eventually_ge_atTop 3] with N hε hJ hN3
  have hntw : NontrivialWindow (JN P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := KMT_quant₂_primeModel P (JN P N) h hh hntw N hN3 (epsN N) hε.1 hε.2
  have hy : yN N = ⌊(N : ℝ) ^ epsN N⌋₊ := rfl
  rw [hy]
  linarith [hb]

/-- **The family theorem.**  Every prime set with `π_P(x) log log x ≤ π(x)` eventually and
divergent reciprocal sum has a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sparse (hS : Sparse P) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JN P) (tailOK_family P hS hP) (kmt_along_family P hS hP)

end NormalNumbers.PrimeModel.Family
