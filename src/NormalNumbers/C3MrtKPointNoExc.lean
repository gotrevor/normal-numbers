/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtUniformMass

/-!
# The `K`-point layer: one named input, every point count

`C3MrtNoExc` proved the natural-density transfer for `K = 2` and lap 84 showed the proof never
used the point count: `class_sum_tendsto_of_window` and `progression_avg_tendsto_of_window`
ask only for a unimodular summand with a dyadic window bound.  The point count enters in
exactly one place, the window bound, i.e. in the named input itself.

This file states that input at `K` points — `KPointNaturalCorrelationNoExc K`, Tao–Teräväinen
Theorem 3.1(ii) with the exceptional set of scales removed — checks it really is the `K = 2`
input at `K = 2`, and runs the `K = 2` pipeline at general `K`.  The archimedean side is
already unconditional: `ttNonPretentious_zOmegaNat` (`C3MrtUniformMass`) supplies TT's (3.3)
for `z^ω` with no hypothesis at all.

TT state in print that even `K = 3` is out of current reach; the point here is not to prove
the input but to make the whole tower rest on ONE named statement at every `K`, with the
exponent `κ(z)·c` and all the bookkeeping machine-checked.
-/

open Filter Finset Topology

namespace NormalNumbers

namespace CastingOut

/-- **The named open problem at `K` points.**  Tao–Teräväinen Theorem 3.1(ii) for `K`-point
correlations, with the exceptional set of scales removed.  As in TT's two-point
statement, only ONE of the `K` functions is asked to be non-pretentious — which is exactly what
the depth rung can supply, since only `z 0 ≠ 1` is known there.  `K = 2` gives back
`TwoPointNaturalCorrelationNoExc` (`twoPointNoExc_of_kPointNoExc`). -/
def KPointNaturalCorrelationNoExc (K : ℕ) : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g : Fin K → ℕ → ℂ, (∀ i, IsCoprimeMultiplicativeNat (g i)) →
      (∀ i n, ‖g i n‖ ≤ 1) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
        (∃ i, TTNonPretentious (g i) X L) →
          ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X →
            ∀ (W b : ℕ) (hsh : Fin K → ℕ), 0 < W → (W : ℝ) ≤ L ^ c →
              (∀ i, (hsh i : ℝ) ≤ L ^ c) → Function.Injective hsh →
              ‖((W : ℝ) / (N : ℝ) : ℝ) •
                  ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                    ∏ i : Fin K, g i (n + hsh i)‖
                ≤ Cst * L ^ (-c)


/-- `K = 2` is the input `C3MrtNoExc` already uses: nothing has been smuggled in. -/
theorem twoPointNoExc_of_kPointNoExc (h : KPointNaturalCorrelationNoExc 2) :
    TwoPointNaturalCorrelationNoExc := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := h
  refine ⟨c, Cst, hc, hCst, ?_⟩
  intro g₁ g₂ hm₁ hm₂ hb₁ hb₂ X L hX hL1 hLX hnp N hN1 hN2 W b h₁ h₂ hW hWL hh₁ hh₂ hne
  have hspec := hmain ![g₁, g₂]
    (fun i => by fin_cases i; exacts [hm₁, hm₂])
    (fun i n => by fin_cases i; exacts [hb₁ n, hb₂ n])
    X L hX hL1 hLX ⟨0, hnp⟩
    N hN1 hN2 W b ![h₁, h₂] hW hWL
    (fun i => by fin_cases i; exacts [hh₁, hh₂])
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  refine le_trans (le_of_eq ?_) hspec
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fin.prod_univ_two]
  simp


/-- **The `K`-point dyadic window bound.**  At `X = N²`, `L = (log X)^κ = (2 log N)^κ`, with
the shifts `h i = i+1` (distinct, and `≤ K ≤ L^c` once `N` is large).  Only the summand and
the shift vector change from the two-point case; the exponent visible downstream is `κ·c`. -/
theorem dyadic_window_bound_K {K : ℕ} (hK : 0 < K) (h : KPointNaturalCorrelationNoExc K)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (z 0)) X L) :
    ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ M r : ℕ, 0 < M → (M : ℝ) ≤ (2 * Real.log N) ^ c →
        ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
            ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1)‖
          ≤ Cst * (2 * Real.log N) ^ (-c) * (N : ℝ) / (M : ℝ) := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := h
  have hc' : 0 < κ * c := mul_pos hκ hc
  have hLtend : Tendsto (fun N : ℕ => (2 * Real.log N) ^ (κ * c)) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => 2 * Real.log N) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    exact (tendsto_rpow_atTop hc').comp h1
  obtain ⟨N₁, hN₁⟩ :=
    Filter.eventually_atTop.1 (hLtend.eventually_ge_atTop (max 2 ((K : ℝ) + 1)))
  refine ⟨κ * c, Cst, hc', hCst, max N₁ 2, fun N hN M r hM hML => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNl : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hmaxle : max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * c) := hN₁ N hNl
  have h2L : (2 : ℝ) ≤ (2 * Real.log N) ^ (κ * c) := le_trans (le_max_left _ _) hmaxle
  have hKL : (K : ℝ) + 1 ≤ (2 * Real.log N) ^ (κ * c) := le_trans (le_max_right _ _) hmaxle
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  set X : ℝ := (N : ℝ) ^ 2 with hX
  have hlogX : Real.log X = 2 * Real.log N := by rw [hX, Real.log_pow]; push_cast; ring
  have hX3 : 3 ≤ X := by rw [hX]; nlinarith
  have hbase : (1 : ℝ) ≤ 2 * Real.log N := by linarith
  have hbase0 : (0 : ℝ) ≤ 2 * Real.log N := by linarith
  set L : ℝ := (2 * Real.log N) ^ κ with hLdef
  have hpow : ∀ s : ℝ, L ^ s = (2 * Real.log N) ^ (κ * s) := by
    intro s; rw [hLdef, ← Real.rpow_mul hbase0]
  have hL1 : (1 : ℝ) ≤ L := Real.one_le_rpow hbase hκ.le
  have hLlog : L ≤ Real.log X := by
    rw [hlogX, hLdef]
    calc (2 * Real.log N) ^ κ ≤ (2 * Real.log N) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hκ1
      _ = 2 * Real.log N := Real.rpow_one _
  have hLκ : L ≤ Real.log X ^ κ := by rw [hlogX]
  have hsqrt : Real.sqrt X = (N : ℝ) := by rw [hX, Real.sqrt_sq hNpos.le]
  have hNX : (N : ℝ) ≤ X := by rw [hX]; nlinarith
  have hshift : ∀ i : Fin K, (((i : ℕ) + 1 : ℕ) : ℝ) ≤ L ^ c := by
    intro i
    rw [hpow]
    have : ((i : ℕ) : ℝ) + 1 ≤ (K : ℝ) + 1 := by
      have : ((i : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
      linarith
    push_cast
    linarith
  have hspec := hmain (fun i => zOmegaNat (z i))
    (fun i => isCoprimeMultiplicativeNat_zOmegaNat _)
    (fun i n => norm_zOmegaNat_le_one (hz i) n) X L (by linarith) hL1 hLlog
    ⟨⟨0, hK⟩, hnp X L hX3 hL1 hLκ⟩
    N (by rw [hsqrt]) hNX M r (fun i => (i : ℕ) + 1) hM (by rw [hpow]; exact hML) hshift
    (by
      intro i j hij
      have h' : (i : ℕ) + 1 = (j : ℕ) + 1 := hij
      exact Fin.ext (by omega))
  rw [hpow, mul_neg] at hspec
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hspec
  set S : ℂ := ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, zOmegaNat (z i) (n + ((i : ℕ) + 1)) with hS
  have hSrw : (∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1)) = S := by
    rw [hS]
    refine Finset.sum_congr rfl fun n _ => Finset.prod_congr rfl fun i _ => ?_
    simp [zOmegaNat, ← add_assoc]
  rw [hSrw]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [div_mul_eq_mul_div, div_le_iff₀ hNpos] at hspec
  rw [le_div_iff₀ hMpos]
  nlinarith [hspec, norm_nonneg S, hNpos.le, hMpos.le]


/-- **The `K`-point natural-density transfer.**  Everything downstream of the window bound is
`progression_avg_tendsto_of_window` (lap 84), which knows nothing about the point count. -/
theorem logToNatural_K_of_noExc {K : ℕ} (hK : 0 < K) (h : KPointNaturalCorrelationNoExc K)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (z 0)) X L)
    {M : ℕ} (hM : 0 < M) (r : ℕ) :
    Tendsto (fun J : ℕ =>
        (∑ m ∈ range J, ∏ i : Fin K, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)) / (J : ℂ))
      atTop (𝓝 0) :=
  progression_avg_tendsto_of_window
    (g := fun n => ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1))
    (fun n => by
      simp only [norm_prod, norm_pow, hz, one_pow, Finset.prod_const_one])
    (dyadic_window_bound_K hK h z hz hκ hκ1 hnp) hM r

/-- **`LogToNaturalCorrelationNZ K`, from the one named input at `K` points.**  The `D = 2`
barrier of `C3MrtNatural` at every point count: the archimedean side is unconditional
(`ttNonPretentious_zOmegaNat`), so `KPointNaturalCorrelationNoExc K` is the whole hypothesis. -/
theorem logToNaturalCorrelationNZ_of_kPointNoExc {K : ℕ} (hK : 0 < K)
    (h : KPointNaturalCorrelationNoExc K) : LogToNaturalCorrelationNZ K :=
  fun z hz hz0 _M r hM _ =>
    logToNatural_K_of_noExc hK h z hz (ttExponent_pos (hz 0) hz0) (ttExponent_le_one (hz 0))
      (ttNonPretentious_zOmegaNat (hz 0) hz0 le_rfl) hM r

/-- **The depth-`K` rung, natural density, from TWO named inputs.**  `ProgressionLogRung K`
(the log-averaged rung) and `KPointNaturalCorrelationNoExc K` (TT Theorem 3.1(ii) at `K`
points, exceptional set removed).  Nothing else. -/
theorem depthAvg_K_tendsto_of_noExc {K : ℕ} (hK : 0 < K) (h : KPointNaturalCorrelationNoExc K)
    {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ) (hζ : depthRoot b hh 0 ≠ 1)
    (hrung : ProgressionLogRung K) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh K N) atTop (𝓝 0) :=
  depthAvg_tendsto_of_transfer_nz hQ P j hh hζ hrung (logToNaturalCorrelationNZ_of_kPointNoExc hK h)

#print axioms NormalNumbers.CastingOut.twoPointNoExc_of_kPointNoExc
#print axioms NormalNumbers.CastingOut.dyadic_window_bound_K
#print axioms NormalNumbers.CastingOut.logToNaturalCorrelationNZ_of_kPointNoExc
#print axioms NormalNumbers.CastingOut.depthAvg_K_tendsto_of_noExc

end CastingOut

end NormalNumbers
