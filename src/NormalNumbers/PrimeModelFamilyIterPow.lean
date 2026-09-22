import NormalNumbers.PrimeModelFamilyIter

/-!
# Family theorem at every exponent `β > 2`

Part IV of the assembly paper proved normality under `π_P(x)·(log log log x)^3 ≤ π(x)`.  The only
place the exponent enters is the transfer term, which needs `L₃ · L₄ · √δ → 0` with
`δ = 2^β/(L₃N)^β`; this holds for every real `β > 2`.  Everything else (`term_two_iter3`,
`term_three_iter3`, `regime_iter3`, the tail argument) is exponent-free or needs only `β > 1`.

Main theorem: `isNormal_subsetLambert_of_sparseIterPow (hβ : 2 < β) : SparseIterPow P β →
DivergentRecip P → IsNormal 4 (subsetLambert P 4)`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyIter

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilySharp

variable (P : ℕ → Prop) [DecidablePred P]

/-- The density hypothesis at exponent `β`: `π_P(x) · (log log log x)^β ≤ π(x)` eventually. -/
def SparseIterPow (β : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, (piP P x : ℝ) * (L3 x) ^ β ≤ (x.primesBelow.card : ℝ)

theorem sparseIterPow_three_iff : SparseIterPow P 3 ↔ SparseIter3 P := by
  unfold SparseIterPow SparseIter3
  have h : ∀ x : ℕ, (L3 x) ^ (3 : ℝ) = (L3 x) ^ (3 : ℕ) := by
    intro x
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [h]

/-- Dominated-Abel bound with `δ = 2^β/(L₃N)^β` (from `L₃t ≥ L₃N/2` on `(y_N, M+1]`). -/
theorem fresh_bound_pow {β : ℝ} (hβ : 0 ≤ β) (hS : SparseIterPow P β) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, yI N ≤ M →
    recipSumIoc P (yI N) M
      ≤ ((2 : ℝ) ^ β / (L3 N) ^ β) * (9 + 12 * Real.log (Real.log M / Real.log (yI N))) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hS
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, yI_facts,
    yI_tendsto.eventually_ge_atTop x₀] with N hN hL hL3 hyI hy0 M hM
  obtain ⟨-, h2y, -, hloglogy, hlogypos, -⟩ := hyI
  have hpos : 0 < L2 N := by linarith
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  have h2ne : (2 : ℝ) ^ β ≠ 0 := ne_of_gt h2pos
  have hupos : (0 : ℝ) < (L3 N) ^ β := Real.rpow_pos_of_pos hu0 β
  have hune : (L3 N) ^ β ≠ 0 := ne_of_gt hupos
  have hδ : (0 : ℝ) ≤ (2 : ℝ) ^ β / (L3 N) ^ β := le_of_lt (div_pos h2pos hupos)
  have hyr : (2 : ℝ) ≤ ((yI N : ℕ) : ℝ) := by exact_mod_cast h2y
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hdom : ∀ t : ℕ, yI N < t → t ≤ M + 1 →
      (piP P t : ℝ) ≤ ((2 : ℝ) ^ β / (L3 N) ^ β) * (t.primesBelow.card : ℝ) := by
    intro t ht _
    have ht0 : x₀ ≤ t := le_trans hy0 ht.le
    have hsp := hx₀ t ht0
    have hty : ((yI N : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.le
    have hlt : Real.log (yI N) ≤ Real.log t := Real.log_le_log (by linarith) hty
    have hllt : Real.log (Real.log (yI N)) ≤ Real.log (Real.log t) :=
      Real.log_le_log hlogypos hlt
    have hbig : L2 N / 2 ≤ Real.log (Real.log t) := le_trans hloglogy hllt
    have hL3t : L3 N - Real.log 2 ≤ L3 t := by
      have h1 : Real.log (L2 N / 2) ≤ Real.log (Real.log (Real.log t)) :=
        Real.log_le_log (by linarith) hbig
      rw [Real.log_div (ne_of_gt hpos) (by norm_num), ← L3_eq] at h1
      exact h1
    have hhalf : L3 N / 2 ≤ L3 t := by linarith
    have hpow : (L3 N) ^ β / (2 : ℝ) ^ β ≤ (L3 t) ^ β := by
      have h3 := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ L3 N / 2) hhalf hβ
      rwa [Real.div_rpow hu0.le (by norm_num)] at h3
    have hppos : (0 : ℝ) ≤ (piP P t : ℝ) := Nat.cast_nonneg _
    have hkey : (piP P t : ℝ) * ((L3 N) ^ β / (2 : ℝ) ^ β) ≤ (t.primesBelow.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hpow hppos) hsp
    rw [div_mul_eq_mul_div, le_div_iff₀ hupos]
    have h4 := mul_le_mul_of_nonneg_right hkey h2pos.le
    have h5 : (piP P t : ℝ) * ((L3 N) ^ β / (2 : ℝ) ^ β) * (2 : ℝ) ^ β
        = (piP P t : ℝ) * (L3 N) ^ β := by field_simp
    rw [h5] at h4
    linarith
  exact recipSumIoc_le_of_dominated' P hδ h2y hM hdom

theorem fresh_mass_pow {β : ℝ} (hβ : 0 ≤ β) (hS : SparseIterPow P β) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yI N) N ≤ ((2 : ℝ) ^ β / (L3 N) ^ β) * (21 + 48 * L4 N) := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, yI_facts, J1_facts,
    fresh_bound_pow P hβ hS] with N hN _hL hL3 hyI hJ hfb
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  have hupos : (0 : ℝ) < (L3 N) ^ β := Real.rpow_pos_of_pos hu0 β
  have hδ : (0 : ℝ) ≤ (2 : ℝ) ^ β / (L3 N) ^ β := le_of_lt (div_pos h2pos hupos)
  have hj0 : (0 : ℝ) < ((J1 N : ℕ) : ℝ) := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hratiopos : 0 < Real.log N / Real.log (yI N) := div_pos (by linarith) hlogypos
  have hlr : Real.log (Real.log N / Real.log (yI N)) ≤ Real.log (2 * ((J1 N : ℕ) : ℝ) ^ 4) :=
    Real.log_le_log hratiopos hratio
  have hexp : Real.log (2 * ((J1 N : ℕ) : ℝ) ^ 4)
      = Real.log 2 + 4 * Real.log (J1 N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := hfb N hyN
  have hstep : (9 : ℝ) + 12 * Real.log (Real.log N / Real.log (yI N)) ≤ 21 + 48 * L4 N := by
    rw [hexp] at hlr; linarith
  linarith [mul_le_mul_of_nonneg_left hstep hδ]

/-- Fresh mass between `y_N` and `2N` is eventually `≤ 1` (needs `β > 1`: the bound is
`(2^β/u^β)(33 + 48v) ≤ 81 · 2^β · u^{1−β}` since `v = log u ≤ u`). -/
theorem fresh_mass_two_pow {β : ℝ} (hβ : 1 < β) (hS : SparseIterPow P β) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yI N) (2 * N) ≤ 1 := by
  have hbig : ∀ᶠ N : ℕ in atTop, 81 * (2 : ℝ) ^ β ≤ (L3 N) ^ (β - 1) := by
    have h := ((tendsto_rpow_atTop (show (0 : ℝ) < β - 1 by linarith)).comp
      L3_tendsto).eventually_ge_atTop (81 * (2 : ℝ) ^ β)
    simpa [Function.comp_def] using h
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 26, yI_facts, J1_facts,
    fresh_bound_pow P (by linarith) hS, hbig] with N hN hL hL3 hyI hJ hfb hbigN
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  have hupos : (0 : ℝ) < (L3 N) ^ β := Real.rpow_pos_of_pos hu0 β
  have hδ : (0 : ℝ) ≤ (2 : ℝ) ^ β / (L3 N) ^ β := le_of_lt (div_pos h2pos hupos)
  have hj0 : (0 : ℝ) < ((J1 N : ℕ) : ℝ) := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hNpos)]; linarith
  have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hNpos)]; linarith
  have hratio2 : Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N) ≤ 4 * ((J1 N : ℕ) : ℝ) ^ 4 := by
    rw [div_le_iff₀ hlogypos]
    rw [div_le_iff₀ hlogypos] at hratio
    linarith
  have hlr : Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
      ≤ Real.log (4 * ((J1 N : ℕ) : ℝ) ^ 4) :=
    Real.log_le_log (div_pos hlog2Npos hlogypos) hratio2
  have hexp : Real.log (4 * ((J1 N : ℕ) : ℝ) ^ 4)
      = Real.log 4 + 4 * Real.log (J1 N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hb := hfb (2 * N) (le_trans hyN (by omega))
  have hstep : recipSumIoc P (yI N) (2 * N)
      ≤ ((2 : ℝ) ^ β / (L3 N) ^ β) * (9 + 12 * (2 + 4 * L4 N)) := by
    refine le_trans hb ?_
    have h9 : (9 : ℝ) + 12 * Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
        ≤ 9 + 12 * (2 + 4 * L4 N) := by
      rw [hexp] at hlr; linarith
    exact mul_le_mul_of_nonneg_left h9 hδ
  have hL4le : L4 N ≤ L3 N := by
    have h := Real.log_le_sub_one_of_pos hu0
    have he : L4 N = Real.log (L3 N) := rfl
    rw [he]; linarith
  have hupow : (L3 N) ^ (β - 1) * L3 N = (L3 N) ^ β := by
    have h := Real.rpow_add hu0 (β - 1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hfin : ((2 : ℝ) ^ β / (L3 N) ^ β) * (9 + 12 * (2 + 4 * L4 N)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hupos, ← hupow]
    have hA : (2 : ℝ) ^ β * (33 + 48 * L4 N) ≤ (2 : ℝ) ^ β * (81 * L3 N) :=
      mul_le_mul_of_nonneg_left (by linarith) h2pos.le
    have hB : (2 : ℝ) ^ β * (81 * L3 N) ≤ (L3 N) ^ (β - 1) * L3 N := by
      have h := mul_le_mul_of_nonneg_right hbigN hu0.le
      linarith
    linarith
  linarith

/-- Term 1 (transfer) at exponent `β > 2`: `24u √(4v) √(2·2^β(21+48v)/u^β) ≤ C_β v u^{1−β/2} → 0`. -/
theorem term_one_pow {β : ℝ} (hβ : 2 < β) (hS : SparseIterPow P β) :
    Tendsto (fun N : ℕ => 24 * (JI P N : ℝ) *
      (Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * recipSumIoc P (yI N) N)))
      atTop (𝓝 0) := by
  have hG : Tendsto (fun N : ℕ =>
      (24 * Real.sqrt (552 * (2 : ℝ) ^ β)) * (L4 N / (L3 N) ^ ((β - 2) / 2)))
      atTop (𝓝 0) := by
    have h := (tendsto_log_div_rpow (r := (β - 2) / 2) (by linarith)).comp L3_tendsto
    have h2 := h.const_mul (24 * Real.sqrt (552 * (2 : ℝ) ^ β))
    simpa [Function.comp_def, L4] using h2
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hG
  · positivity
  filter_upwards [L2_tendsto.eventually_ge_atTop 2500, L4_tendsto.eventually_ge_atTop 1,
    JI_le_L3 P, epsI_facts, fresh_mass_pow P (by linarith) hS] with N hL hv1 hJ hef hfm
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  set u : ℝ := L3 N with hudef
  set v : ℝ := L4 N with hvdef
  set W : ℝ := recipSumIoc P (yI N) N with hWdef
  have hu0 : (0 : ℝ) < u := by linarith
  have hune0 : u ≠ 0 := ne_of_gt hu0
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  have hupos : (0 : ℝ) < u ^ β := Real.rpow_pos_of_pos hu0 β
  have hune : u ^ β ≠ 0 := ne_of_gt hupos
  have hhpos : (0 : ℝ) < u ^ (β / 2) := Real.rpow_pos_of_pos hu0 _
  have hhne : u ^ (β / 2) ≠ 0 := ne_of_gt hhpos
  have hrpos : (0 : ℝ) < u ^ ((β - 2) / 2) := Real.rpow_pos_of_pos hu0 _
  have hrne : u ^ ((β - 2) / 2) ≠ 0 := ne_of_gt hrpos
  have hepslog : Real.log (1 / epsI N) ≤ 4 * v := hef.2.2.2.2
  have hW0 : 0 ≤ W := recipSumIoc_nonneg P _ _
  have hWuβ : W * u ^ β ≤ (2 : ℝ) ^ β * (21 + 48 * v) := by
    have h := mul_le_mul_of_nonneg_right hfm hupos.le
    calc W * u ^ β ≤ ((2 : ℝ) ^ β / u ^ β * (21 + 48 * v)) * u ^ β := h
      _ = (2 : ℝ) ^ β * (21 + 48 * v) := by field_simp
  have hvv : v ≤ v ^ 2 := by nlinarith
  have hkey : 8 * v * W ≤ 552 * (2 : ℝ) ^ β * v ^ 2 / u ^ β := by
    rw [le_div_iff₀ hupos]
    nlinarith [mul_le_mul_of_nonneg_left hWuβ (by linarith : (0 : ℝ) ≤ 8 * v),
      mul_le_mul_of_nonneg_left hvv h2pos.le]
  have hD0 : (0 : ℝ) ≤ Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hhpos.le
  have hDsq : (Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2)) ^ 2
      = 552 * (2 : ℝ) ^ β * v ^ 2 / u ^ β := by
    have hs : (Real.sqrt (552 * (2 : ℝ) ^ β)) ^ 2 = 552 * (2 : ℝ) ^ β :=
      Real.sq_sqrt (by positivity)
    have hsq : (u ^ (β / 2)) ^ 2 = u ^ β := by
      rw [sq, ← Real.rpow_add hu0]
      congr 1
      ring
    rw [div_pow, mul_pow, hs, hsq]
  have hAB : Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * W)
      ≤ Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2) := by
    have hA : Real.sqrt (Real.log (1 / epsI N)) ≤ Real.sqrt (4 * v) := Real.sqrt_le_sqrt hepslog
    have h1 := mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg (2 * W))
    have h2 : Real.sqrt (4 * v) * Real.sqrt (2 * W) = Real.sqrt (8 * v * W) := by
      rw [← Real.sqrt_mul (by linarith)]
      congr 1
      ring
    have h3 : Real.sqrt (8 * v * W) ≤ Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2) := by
      calc Real.sqrt (8 * v * W)
          ≤ Real.sqrt ((Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2)) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            rw [hDsq]; exact hkey
        _ = _ := Real.sqrt_sq hD0
    linarith [h1, h2.le, h2.ge, h3]
  have hsplit : u ^ (β / 2) = u * u ^ ((β - 2) / 2) := by
    have h := Real.rpow_add hu0 1 ((β - 2) / 2)
    rw [Real.rpow_one] at h
    rw [show β / 2 = 1 + (β - 2) / 2 by ring, h]
  have hfin : 24 * u * (Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2))
      = (24 * Real.sqrt (552 * (2 : ℝ) ^ β)) * (v / u ^ ((β - 2) / 2)) := by
    rw [hsplit]
    field_simp
  calc 24 * (JI P N : ℝ) * (Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * W))
      ≤ 24 * u * (Real.sqrt (552 * (2 : ℝ) ^ β) * v / u ^ (β / 2)) := by
        refine mul_le_mul (by linarith) hAB (by positivity) (by linarith)
    _ = (24 * Real.sqrt (552 * (2 : ℝ) ^ β)) * (v / u ^ ((β - 2) / 2)) := hfin

/-- The L¹ tail; identical to `tail_iter3` with `fresh_mass_two_pow`. -/
theorem tail_pow {β : ℝ} (hβ : 1 < β) (hS : SparseIterPow P β) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ JI P N)
      atTop (𝓝 0) := by
  set ρ : ℝ := Real.log 4 - 1 with hρdef
  have hlog4 : 1 < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  -- majorant 1
  have hf : Tendsto (fun N : ℕ => (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N))
      atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
    have hsum : Tendsto
        (fun n : ℕ => 13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n))
        atTop (𝓝 0) := by
      simpa using (h1.const_mul (13 : ℝ)).add (h0.const_mul (21 : ℝ))
    refine Tendsto.congr (fun N => ?_) (hsum.comp (JI_tendsto P hP))
    simp only [Function.comp_apply, pow_one, pow_zero]
    ring
  -- majorant 2
  have hgt : Tendsto (fun N : ℕ => 120 * (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hρ0).comp L2_tendsto
      simpa [Function.comp_def] using this
    simpa using h1.const_mul (120 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ (by simpa using hf.add hgt)
  · have := recipSumLe_nonneg P (2 * N)
    positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JI_le_L3 P,
    fresh_mass_two_pow P hβ hS, yI_facts] with N hN hL hJle hfm2 hyf
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  obtain ⟨-, -, hyN, -⟩ := hyf
  have ht0 : 0 < L2 N := by linarith
  have hulog : L3 N = Real.log (L2 N) := L3_eq N
  have hrp : (0 : ℝ) < (L2 N) ^ (-ρ) := Real.rpow_pos_of_pos ht0 _
  have hpow0 : (0 : ℝ) < (4 : ℝ) ^ (JI P N) := by positivity
  have hfnn : (0 : ℝ) ≤ (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N) := by positivity
  have hgnn : (0 : ℝ) ≤ 120 * (L2 N) ^ (-ρ) := by positivity
  rcases le_total (J1 N) (⌊recipSumLe P (yI N) / 8⌋₊) with hcase | hcase
  · -- `J = J₁ = ⌊L₃⌋₊`, so `4^J ≥ (L₂N)^{log 4}/4`
    have hJlow : L3 N - 1 ≤ (JI P N : ℝ) := JI_lower P hcase (by linarith)
    have hpow : (L2 N) ^ Real.log 4 / 4 ≤ (4 : ℝ) ^ (JI P N) := by
      have h1 : (4 : ℝ) ^ (JI P N) = (4 : ℝ) ^ ((JI P N : ℕ) : ℝ) := (Real.rpow_natCast 4 _).symm
      have h2 : (4 : ℝ) ^ (L3 N - 1) ≤ (4 : ℝ) ^ ((JI P N : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (4 : ℝ) ^ (L3 N - 1) = (L2 N) ^ Real.log 4 / 4 := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        congr 1
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4), Real.rpow_def_of_pos ht0, hulog]
        congr 1
        ring
      rw [h1, ← h3]; exact h2
    -- the numerator
    have hL2two : L2 (2 * N) ≤ L2 N + 1 := by
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
      have h1 : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by rw [hlog2N]; linarith
      have h2 : L2 (2 * N) ≤ Real.log (2 * Real.log N) := Real.log_le_log hlog2Npos h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h4 : Real.log (Real.log N) = L2 N := rfl
      linarith [h2, h4.le, h4.ge]
    have hcrude : recipSumLe P (2 * N) ≤ 12 * L2 (2 * N) + 21 :=
      recipSumLe_le_crude P (by omega)
    have hnum : recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12 ≤ 30 * L2 N := by
      have h5 : (JI P N : ℝ) ≤ L3 N := hJle
      linarith
    have h30 : (0 : ℝ) ≤ 30 * L2 N := by linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ (JI P N)
        ≤ (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) :=
      div_le_div₀ h30 hnum (by positivity) hpow
    have hfin : (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) = 120 * (L2 N) ^ (-ρ) := by
      rw [hρdef, show -(Real.log 4 - 1) = 1 - Real.log 4 by ring, Real.rpow_sub ht0,
        Real.rpow_one]
      field_simp
      norm_num
    linarith [hstep, hfin.le, hfin.ge, hfnn]
  · -- `J = ⌊S/8⌋₊`
    have hJeq : JI P N = ⌊recipSumLe P (yI N) / 8⌋₊ := min_eq_right hcase
    have hSlt : recipSumLe P (yI N) < 8 * (JI P N : ℝ) + 8 := by
      have := Nat.lt_floor_add_one (recipSumLe P (yI N) / 8)
      rw [← hJeq] at this
      linarith
    have hsplit : recipSumLe P (2 * N)
        = recipSumLe P (yI N) + recipSumIoc P (yI N) (2 * N) :=
      recipSumLe_add_recipSumIoc P (le_trans hyN (by omega))
    have hnum : recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12 ≤ 13 * (JI P N : ℝ) + 21 := by
      rw [hsplit]; linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ (JI P N)
        ≤ (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N) :=
      div_le_div_of_nonneg_right hnum hpow0.le
    linarith [hstep, hgnn]

theorem tailOK_pow {β : ℝ} (hβ : 1 < β) (hS : SparseIterPow P β) (hP : DivergentRecip P) :
    TailOK P (JI P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_pow P hβ hS hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JI P N) N hN

theorem kmt_along_pow {β : ℝ} (hβ : 2 < β) (hS : SparseIterPow P β) (hP : DivergentRecip P) :
    KMT_along P (JI P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      24 * (JI P N : ℝ) * (Real.sqrt (Real.log (1 / epsI N))
          * Real.sqrt (2 * recipSumIoc P (yI N) N))
        + Real.exp (3 * (JI P N : ℝ)) * Real.exp (- recipSumLe P (yI N))
        + (2 * (JI P N : ℝ) ^ 2 + 2 * (JI P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
            * Real.exp (-1 / (8 * (JI P N : ℝ) ^ 2 * epsI N))) atTop (𝓝 0) := by
    have := ((term_one_pow P hβ hS).add (term_two_iter3 P hP)).add (term_three_iter3 P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [regime_iter3 P hP,
    (JI_tendsto P hP).eventually_ge_atTop (h.natAbs + 1)] with N hR hJ
  have hntw : NontrivialWindow (JI P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := window_bound_regime P h hntw hR
  have hy : yOf N (epsI N) = yI N := rfl
  rw [hy] at hb
  linarith [hb]

/-- **Family theorem at every exponent `β > 2`.**  Every prime set with
`π_P(x) (log log log x)^β ≤ π(x)` eventually and divergent reciprocal sum has a normal base-4
Lambert constant. -/
theorem isNormal_subsetLambert_of_sparseIterPow {β : ℝ} (hβ : 2 < β) (hS : SparseIterPow P β)
    (hP : DivergentRecip P) : IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JI P) (tailOK_pow P (by linarith) hS hP)
    (kmt_along_pow P hβ hS hP)

end NormalNumbers.PrimeModel.FamilyIter
