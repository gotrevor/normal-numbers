import NormalNumbers.PrimeModelFamily

/-!
# Sharper family theorem, part A: schedule and mass bounds

The frozen statement `KMT_quant₂ C₁ C₂` carries constants `C₁ k = e^{4k}`, which forces the
family theorem `isNormal_subsetLambert_of_sparse` to take the schedule `J_N ≤ L₃N/24` and the
hypothesis `π_P(x) · log log x ≤ π(x)`.  The intermediate bound `window_bound_regime` actually
proved has **polynomial** constants (`24k`, `e^{3k}`, `2·4^k + …`).  Consuming it directly, the
schedule can take `J_N ≈ L₃N` (so that `4^{J_N} ≫ L₂N ≥ S_P(N)`, killing the tail with no
density input at all), and the density hypothesis weakens to

    π_P(x) · (log log log x)^5 ≤ π(x)   eventually            (`SparseIter`).

This file: the hypothesis, the schedule `JS`, and the mass bounds.  Part B
(`PrimeModelFamilySharp`) has the four limits and the assembly.

All the `L₂, L₃, epsN, yN` machinery is reused from `PrimeModelFamily`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilySharp

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family

variable (P : ℕ → Prop) [DecidablePred P]

/-- **The sharper density hypothesis**: `π_P(x) · (log log log x)^5 ≤ π(x)` eventually. -/
def SparseIter : Prop :=
  ∀ᶠ x : ℕ in atTop, (piP P x : ℝ) * (L3 x) ^ 5 ≤ (x.primesBelow.card : ℝ)

/-- `(log t)^5 ≤ t` for large real `t`. -/
theorem eventually_log_pow_five_le : ∀ᶠ t : ℝ in atTop, (Real.log t) ^ 5 ≤ t := by
  have h := tendsto_log_div_rpow (r := (1/5 : ℝ)) (by norm_num)
  have h1 : ∀ᶠ t : ℝ in atTop, Real.log t / t ^ (1/5 : ℝ) ≤ 1 :=
    h.eventually_le_const (by norm_num)
  filter_upwards [h1, eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have ht0 : (0 : ℝ) < t := by linarith
  have hrp : 0 < t ^ (1/5 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
  have hle : Real.log t ≤ t ^ (1/5 : ℝ) := by rw [div_le_one hrp] at ht; exact ht
  have hpow : (t ^ (1/5 : ℝ)) ^ (5 : ℕ) = t := by
    rw [← Real.rpow_natCast (t ^ (1/5 : ℝ)) 5, ← Real.rpow_mul ht0.le]
    norm_num
  calc (Real.log t) ^ 5 ≤ (t ^ (1/5 : ℝ)) ^ (5 : ℕ) := pow_le_pow_left₀ hlog hle 5
    _ = t := hpow

/-- `Sparse` implies `SparseIter` (since `(L₃x)^5 ≤ L₂x` eventually). -/
theorem sparseIter_of_sparse (hS : Sparse P) : SparseIter P := by
  filter_upwards [hS, L2_tendsto.eventually eventually_log_pow_five_le] with x hx hpow
  have h1 : (L3 x) ^ 5 ≤ L2 x := hpow
  have hp : (0 : ℝ) ≤ (piP P x : ℝ) := Nat.cast_nonneg _
  have h2 : (piP P x : ℝ) * (L3 x) ^ 5 ≤ (piP P x : ℝ) * L2 x :=
    mul_le_mul_of_nonneg_left h1 hp
  exact h2.trans hx

/-- The sharper schedule `J_N = min(⌊L₃N⌋₊, ⌊S_P(y_N)/8⌋₊)`. -/
noncomputable def JS (N : ℕ) : ℕ :=
  min ⌊L3 N⌋₊ ⌊recipSumLe P (yN N) / 8⌋₊

theorem JS_le_L3 : ∀ᶠ N : ℕ in atTop, (JS P N : ℝ) ≤ L3 N := by
  filter_upwards [L3_tendsto.eventually_ge_atTop 0] with N hL
  have h1 : JS P N ≤ ⌊L3 N⌋₊ := min_le_left _ _
  have h2 : ((⌊L3 N⌋₊ : ℕ) : ℝ) ≤ L3 N := Nat.floor_le (by linarith)
  have h3 : (JS P N : ℝ) ≤ ((⌊L3 N⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem JS_le_mass (N : ℕ) : 8 * (JS P N : ℝ) ≤ recipSumLe P (yN N) := by
  have hS := recipSumLe_nonneg P (yN N)
  have h1 : JS P N ≤ ⌊recipSumLe P (yN N) / 8⌋₊ := min_le_right _ _
  have h2 : ((⌊recipSumLe P (yN N) / 8⌋₊ : ℕ) : ℝ) ≤ recipSumLe P (yN N) / 8 :=
    Nat.floor_le (by positivity)
  have h3 : (JS P N : ℝ) ≤ ((⌊recipSumLe P (yN N) / 8⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem JS_tendsto (hP : DivergentRecip P) : Tendsto (JS P) atTop atTop := by
  have hA : Tendsto (fun N : ℕ => ⌊L3 N⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp L3_tendsto
  have hB : Tendsto (fun N : ℕ => ⌊recipSumLe P (yN N) / 8⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((mass_tendsto P hP).atTop_div_const (by norm_num))
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hA.eventually_ge_atTop b, hB.eventually_ge_atTop b] with N h1 h2
  exact le_min h1 h2

/-- In the first branch of the `min`, `J_N ≥ L₃N − 1`. -/
theorem JS_lower {N : ℕ} (hcase : ⌊L3 N⌋₊ ≤ ⌊recipSumLe P (yN N) / 8⌋₊) (hL : 0 ≤ L3 N) :
    L3 N - 1 ≤ (JS P N : ℝ) := by
  have h : JS P N = ⌊L3 N⌋₊ := min_eq_left hcase
  rw [h]
  linarith [Nat.lt_floor_add_one (L3 N)]

/-! ### Total mass with no density input: `S_P(N) ≤ 12 L₂N + 21` -/

/-- Crude total mass: `∑_{p ≤ N, p ∈ P} 1/p ≤ ∑_{p ≤ N} 1/p ≤ 1 + 8 + 12 log(log N / log 2)
≤ 12 L₂N + 21` for `N ≥ 3`.  Uses `PrimeDensity.primeRecipSum_le` with `v = 2`, the prime `2`
contributing at most `1`, and `−log log 2 ≤ 1`. -/
theorem recipSumLe_le_crude {N : ℕ} (hN : 3 ≤ N) : recipSumLe P N ≤ 12 * L2 N + 21 := by
  classical
  -- drop the membership condition `P`
  have hsub : (Finset.Iic N).filter (fun p => p.Prime ∧ P p)
      ⊆ (Finset.Iic N).filter (fun p => Nat.Prime p) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have h1 : recipSumLe P N ≤ ∑ p ∈ (Finset.Iic N).filter (fun p => Nat.Prime p), (1 : ℝ) / p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _; positivity
  -- split off the prime `2`
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Iic N).filter (fun p => Nat.Prime p)) (fun p : ℕ => (2 : ℝ) < (p : ℝ))
    (fun p => (1 : ℝ) / p)
  have hsmall : (((Finset.Iic N).filter (fun p => Nat.Prime p)).filter
      (fun p : ℕ => ¬ ((2 : ℝ) < (p : ℝ)))) = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_singleton, not_lt]
    constructor
    · rintro ⟨⟨hpN, hp⟩, hp2⟩
      have hle : p ≤ 2 := by exact_mod_cast hp2
      have := hp.two_le
      omega
    · rintro rfl
      exact ⟨⟨by omega, Nat.prime_two⟩, by norm_num⟩
  have hbig : (((Finset.Iic N).filter (fun p => Nat.Prime p)).filter
      (fun p : ℕ => (2 : ℝ) < (p : ℝ)))
      = (Finset.Iic N).filter (fun p : ℕ => Nat.Prime p ∧ (2 : ℝ) < (p : ℝ)) :=
    Finset.filter_filter _ _ _
  have hsmallsum : ∑ p ∈ (((Finset.Iic N).filter (fun p => Nat.Prime p)).filter
      (fun p : ℕ => ¬ ((2 : ℝ) < (p : ℝ)))), (1 : ℝ) / p = 1 / 2 := by
    rw [hsmall, Finset.sum_singleton]; norm_num
  -- the Mertens-type bound for the primes `> 2`
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have key := NormalNumbers.PrimeModel.PrimeDensity.primeRecipSum_le (2 : ℝ) le_rfl N hNr
  -- `log (log N / log 2) = L₂ N − log (log 2)`
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogeq : Real.log (Real.log N / Real.log 2) = L2 N - Real.log (Real.log 2) := by
    rw [Real.log_div (by linarith) (ne_of_gt hlog2pos)]
    rfl
  have hinv : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2pos]; linarith [Real.log_two_gt_d9]
  have hneg : - Real.log (Real.log 2) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / Real.log 2 by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hlog2pos), Real.log_one] at h
    linarith
  rw [hbig] at hsplit
  rw [hsmallsum] at hsplit
  rw [hlogeq] at key
  linarith

/-! ### Fresh mass under `SparseIter` -/

/-- Dominated-Abel bound, uniformly in the upper endpoint: on `(y_N, M+1]` the relative density
is `≤ 32/(L₃N)^5` because `L₃t ≥ L₃(y_N) ≥ L₃N − log 2 ≥ L₃N/2` there
(`log log y_N ≥ L₂N/2` from `yN_core`). -/
theorem fresh_bound_iter (hS : SparseIter P) : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, yN N ≤ M →
    recipSumIoc P (yN N) M
      ≤ (32 / (L3 N) ^ 5) * (9 + 12 * Real.log (Real.log M / Real.log (yN N))) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hS
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, yN_tendsto.eventually_ge_atTop x₀] with N hN hL hL3 hy0 M hM
  obtain ⟨h2y, -, hlogy, hloglogy, -⟩ := yN_core hN hL
  have hpos : 0 < L2 N := by linarith
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hδ : (0 : ℝ) ≤ 32 / (L3 N) ^ 5 := by positivity
  have hylogpos : 0 < Real.log (yN N) := by
    have : L2 N / 2 ≤ Real.log N / L2 N := by
      rw [le_div_iff₀ hpos]; nlinarith [quad_bound hN]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hdom : ∀ t : ℕ, yN N < t → t ≤ M + 1 →
      (piP P t : ℝ) ≤ (32 / (L3 N) ^ 5) * (t.primesBelow.card : ℝ) := by
    intro t ht _
    have ht0 : x₀ ≤ t := le_trans hy0 ht.le
    have hsp := hx₀ t ht0
    have hty : (yN N : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.le
    have hlt : Real.log (yN N) ≤ Real.log t := Real.log_le_log (by positivity) hty
    have hllt : Real.log (Real.log (yN N)) ≤ Real.log (Real.log t) :=
      Real.log_le_log hylogpos hlt
    have hbig : L2 N / 2 ≤ Real.log (Real.log t) := le_trans hloglogy hllt
    have hL3t : L3 N - Real.log 2 ≤ L3 t := by
      have h1 : Real.log (L2 N / 2) ≤ Real.log (Real.log (Real.log t)) :=
        Real.log_le_log (by linarith) hbig
      rw [Real.log_div (ne_of_gt hpos) (by norm_num), ← L3_eq] at h1
      exact h1
    have hhalf : L3 N / 2 ≤ L3 t := by linarith
    have hpow : (L3 N) ^ 5 / 32 ≤ (L3 t) ^ 5 := by
      have h5 := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ L3 N / 2) hhalf 5
      calc (L3 N) ^ 5 / 32 = (L3 N / 2) ^ 5 := by ring
        _ ≤ (L3 t) ^ 5 := h5
    have hppos : (0 : ℝ) ≤ (piP P t : ℝ) := Nat.cast_nonneg _
    have hkey : (piP P t : ℝ) * ((L3 N) ^ 5 / 32) ≤ (t.primesBelow.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hpow hppos) hsp
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (L3 N) ^ 5)]
    nlinarith
  exact recipSumIoc_le_of_dominated' P hδ h2y hM hdom

/-- Fresh mass between `y_N` and `N`: `≤ (32/(L₃N)^5)(9 + 12 L₃N) ≤ 672 / (L₃N)^4`. -/
theorem fresh_mass_iter (hS : SparseIter P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yN N) N ≤ 672 / (L3 N) ^ 4 := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    fresh_bound_iter P hS] with N hN hL hfb
  obtain ⟨-, hyN, hlogy, -, -⟩ := yN_core hN hL
  obtain ⟨hu1, -, -⟩ := L3_bounds hL
  have hpos : 0 < L2 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hylogpos : 0 < Real.log (yN N) := by
    have : L2 N / 2 ≤ Real.log N / L2 N := by
      rw [le_div_iff₀ hpos]; nlinarith [quad_bound hN]
    linarith
  have hratio : Real.log N / Real.log (yN N) ≤ L2 N := by
    rw [div_le_iff₀ hylogpos]
    have h := mul_le_mul_of_nonneg_right hlogy hpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h
    linarith
  have hlogratio : Real.log (Real.log N / Real.log (yN N)) ≤ L3 N := by
    rw [L3_eq]
    exact Real.log_le_log (div_pos (by linarith) hylogpos) hratio
  have hb := hfb N hyN
  have hstepa : (9 : ℝ) + 12 * Real.log (Real.log N / Real.log (yN N)) ≤ 21 * L3 N := by
    linarith
  have hstepb : (32 / (L3 N) ^ 5) * (9 + 12 * Real.log (Real.log N / Real.log (yN N)))
      ≤ (32 / (L3 N) ^ 5) * (21 * L3 N) :=
    mul_le_mul_of_nonneg_left hstepa (by positivity)
  have hid : (32 / (L3 N) ^ 5) * (21 * L3 N) = 672 / (L3 N) ^ 4 := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  linarith

/-- Fresh mass between `y_N` and `2N` is eventually at most `1`. -/
theorem fresh_mass_two_iter (hS : SparseIter P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yN N) (2 * N) ≤ 1 := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 5, fresh_bound_iter P hS] with N hN hL hu5 hfb
  obtain ⟨-, hyN, hlogy, -, -⟩ := yN_core hN hL
  have hpos : 0 < L2 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hu0 : (0 : ℝ) < L3 N := by linarith
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
    have h1 := mul_le_mul_of_nonneg_right hlogy hpos.le
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
  have hδ : (0 : ℝ) ≤ 32 / (L3 N) ^ 5 := by positivity
  have hstep : recipSumIoc P (yN N) (2 * N) ≤ (32 / (L3 N) ^ 5) * (9 + 12 * (1 + L3 N)) := by
    refine le_trans hb ?_
    have : (9 : ℝ) + 12 * Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yN N))
        ≤ 9 + 12 * (1 + L3 N) := by linarith
    exact mul_le_mul_of_nonneg_left this hδ
  have hfin : (32 / (L3 N) ^ 5) * (9 + 12 * (1 + L3 N)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    have h4 : (625 : ℝ) ≤ (L3 N) ^ 4 := by
      linarith [pow_le_pow_left₀ (show (0:ℝ) ≤ 5 by norm_num) hu5 4]
    have h5 : (625 : ℝ) * L3 N ≤ (L3 N) ^ 5 := by
      have := mul_le_mul_of_nonneg_right h4 hu0.le
      nlinarith [this]
    linarith
  linarith

end NormalNumbers.PrimeModel.FamilySharp
