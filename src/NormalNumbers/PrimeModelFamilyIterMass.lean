import NormalNumbers.PrimeModelFamilySharp

/-!
# Family theorem with `ε = J₁^{-4}`, part A: schedule and mass bounds

Part III of the assembly paper used `ε_N = 2/L₂N`, so `log(1/ε_N) ≈ L₃N` entered the transfer
term and forced the exponent `5` on `log log log x`.  The sieve term only needs
`ε ≪ 1/J³`, so `ε` may be taken as large as `J₁^{-4}` with `J₁ = ⌊L₃N⌋₊` (`P`-independent),
giving `log(1/ε) = 4 log J₁ ≤ 4 L₄N` and the weaker hypothesis

    π_P(x) · (log log log x)^3 ≤ π(x)   eventually            (`SparseIter3`).

Definitions: `L4 N = log L3 N`, `J1 N = ⌊L3 N⌋₊`, `epsI N = 1/(J1 N)^4`, `yI N = ⌊N^{epsI N}⌋₊`,
`JI P N = min (J1 N) ⌊S_P(yI N)/8⌋₊`.  Since `epsN N ≤ epsI N` eventually, `yN N ≤ yI N` and all
the `yN_core` facts transfer by monotonicity.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyIter

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilySharp

variable (P : ℕ → Prop) [DecidablePred P]

/-- The density hypothesis: `π_P(x) · (log log log x)^3 ≤ π(x)` eventually. -/
def SparseIter3 : Prop :=
  ∀ᶠ x : ℕ in atTop, (piP P x : ℝ) * (L3 x) ^ 3 ≤ (x.primesBelow.card : ℝ)

theorem sparseIter3_of_sparseIter (hS : SparseIter P) : SparseIter3 P := by
  filter_upwards [hS, L3_tendsto.eventually_ge_atTop (1 : ℝ)] with x hx h1
  have hp : (0 : ℝ) ≤ (piP P x : ℝ) := Nat.cast_nonneg _
  have h35 : (L3 x) ^ 3 ≤ (L3 x) ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  exact le_trans (mul_le_mul_of_nonneg_left h35 hp) hx

/-- `L₄ N = log log log log N`. -/
noncomputable def L4 (N : ℕ) : ℝ := Real.log (L3 N)

/-- `J₁ N = ⌊L₃N⌋₊`, the `P`-independent cap of the schedule. -/
noncomputable def J1 (N : ℕ) : ℕ := ⌊L3 N⌋₊

/-- `ε_N = 1/(J₁N)^4`. -/
noncomputable def epsI (N : ℕ) : ℝ := 1 / ((J1 N : ℝ)) ^ 4

/-- `y_N = ⌊N^{ε_N}⌋₊`. -/
noncomputable def yI (N : ℕ) : ℕ := ⌊(N : ℝ) ^ epsI N⌋₊

/-- The schedule `J_N = min(J₁N, ⌊S_P(y_N)/8⌋₊)`. -/
noncomputable def JI (N : ℕ) : ℕ := min (J1 N) ⌊recipSumLe P (yI N) / 8⌋₊

theorem L4_tendsto : Tendsto L4 atTop atTop :=
  Real.tendsto_log_atTop.comp L3_tendsto

theorem J1_tendsto : Tendsto J1 atTop atTop :=
  tendsto_nat_floor_atTop.comp L3_tendsto

/-- `L₃N − 1 ≤ J₁N ≤ L₃N` and `log J₁N ≤ L₄N`, eventually. -/
theorem J1_facts : ∀ᶠ N : ℕ in atTop,
    L3 N - 1 ≤ (J1 N : ℝ) ∧ (J1 N : ℝ) ≤ L3 N ∧ 1 ≤ (J1 N : ℝ) ∧
      Real.log (J1 N) ≤ L4 N := by
  filter_upwards [L3_tendsto.eventually_ge_atTop (2 : ℝ)] with N hL
  have h0 : (0 : ℝ) ≤ L3 N := by linarith
  have hle : ((J1 N : ℕ) : ℝ) ≤ L3 N := Nat.floor_le h0
  have hgt : L3 N - 1 ≤ ((J1 N : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (L3 N)
    have h2 : L3 N < ((J1 N : ℕ) : ℝ) + 1 := this
    linarith
  refine ⟨hgt, hle, by linarith, ?_⟩
  exact Real.log_le_log (by linarith) hle

/-- `2 (L₃N)^4 ≤ L₂N` eventually (since `2 (log t)^4 ≤ t` for large `t`). -/
private theorem eventually_two_L3_pow_four_le : ∀ᶠ N : ℕ in atTop, 2 * (L3 N) ^ 4 ≤ L2 N := by
  filter_upwards [L2_tendsto.eventually
    (eventually_pow_log_le 4 (r := (1 : ℝ)) (c := (2 : ℝ)) (by norm_num) (by norm_num))] with N h
  rw [Real.rpow_one] at h
  rw [L3_eq]
  exact h

/-- The `ε`-window facts: `epsN N ≤ epsI N`, `epsI N ≤ 1/(7680 J₁N)`, `1/L₂N < epsI N < 1/2`,
and `log(1/epsI N) ≤ 4 L₄N`, eventually.  (`2 (L₃N)^4 ≤ L₂N` and `(J₁N)^3 ≥ 7680` eventually.) -/
theorem epsI_facts : ∀ᶠ N : ℕ in atTop,
    epsN N ≤ epsI N ∧ epsI N ≤ 1 / (7680 * (J1 N : ℝ)) ∧
      1 / Real.log (Real.log N) < epsI N ∧ epsI N < 1 / 2 ∧
      Real.log (1 / epsI N) ≤ 4 * L4 N := by
  filter_upwards [eventually_two_L3_pow_four_le, J1_facts,
    J1_tendsto.eventually_ge_atTop 20, L2_tendsto.eventually_ge_atTop 2500] with N h4 hJ hj20 hL
  obtain ⟨-, hj2, -, hjlog⟩ := hJ
  have heps : epsI N = 1 / ((J1 N : ℕ) : ℝ) ^ 4 := rfl
  set j : ℝ := ((J1 N : ℕ) : ℝ) with hjdef
  have hj20' : (20 : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj20
  have hj0 : (0 : ℝ) < j := by linarith
  have hj4pos : (0 : ℝ) < j ^ 4 := by positivity
  have ht0 : (0 : ℝ) < L2 N := by linarith
  have hju : j ^ 4 ≤ (L3 N) ^ 4 := pow_le_pow_left₀ hj0.le hj2 4
  have hkey : 2 * j ^ 4 ≤ L2 N := by linarith
  have hcube : (8000 : ℝ) ≤ j ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hj20' 3
    norm_num at h
    linarith
  have hq : 7680 * j ≤ j ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left hcube hj0.le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 2 / L2 N ≤ epsI N
    rw [heps, div_le_div_iff₀ ht0 hj4pos]
    linarith
  · rw [heps]
    exact one_div_le_one_div_of_le (by positivity) hq
  · show 1 / L2 N < epsI N
    rw [heps]
    exact one_div_lt_one_div_of_lt hj4pos (by linarith)
  · rw [heps]
    exact one_div_lt_one_div_of_lt (by norm_num) (by nlinarith)
  · rw [heps, one_div_one_div, Real.log_pow]
    push_cast
    linarith

/-- The `y_N` facts, inherited from `yN_core` by monotonicity (`yN N ≤ yI N`), plus the ratio
`log N / log y_N ≤ 2 (J₁N)^4` (from `⌊x⌋₊ ≥ x/2` for `x ≥ 2` and `epsI N · log N ≥ 2`). -/
theorem yI_facts : ∀ᶠ N : ℕ in atTop,
    yN N ≤ yI N ∧ 2 ≤ yI N ∧ yI N ≤ N ∧ L2 N / 2 ≤ Real.log (Real.log (yI N)) ∧
      0 < Real.log (yI N) ∧ Real.log N / Real.log (yI N) ≤ 2 * (J1 N : ℝ) ^ 4 := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    eventually_two_L3_pow_four_le, J1_facts, J1_tendsto.eventually_ge_atTop 20,
    epsI_facts] with N hN hL h4 hJ hj20 heI
  obtain ⟨-, hj2, -, -⟩ := hJ
  obtain ⟨hepsle, -, -, -, -⟩ := heI
  obtain ⟨h2yN, -, -, hloglogyN, -⟩ := yN_core hN hL
  have heps : epsI N = 1 / ((J1 N : ℕ) : ℝ) ^ 4 := rfl
  set j : ℝ := ((J1 N : ℕ) : ℝ) with hjdef
  have hj20' : (20 : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj20
  have hj0 : (0 : ℝ) < j := by linarith
  have hj4pos : (0 : ℝ) < j ^ 4 := by positivity
  have ht0 : (0 : ℝ) < L2 N := by linarith
  have hju : j ^ 4 ≤ (L3 N) ^ 4 := pow_le_pow_left₀ hj0.le hj2 4
  have hkey : 2 * j ^ 4 ≤ L2 N := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  -- `yN N ≤ yI N`
  have hmono : (N : ℝ) ^ epsN N ≤ (N : ℝ) ^ epsI N :=
    Real.rpow_le_rpow_of_exponent_le hN1 hepsle
  have hyNyI : yN N ≤ yI N := Nat.floor_le_floor hmono
  have h2yI : 2 ≤ yI N := le_trans h2yN hyNyI
  -- `yI N ≤ N`
  have hepsle1 : epsI N ≤ 1 := by
    rw [heps, div_le_one hj4pos]
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ j ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hyIN : yI N ≤ N := by
    have hle : (N : ℝ) ^ epsI N ≤ (N : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hN1 hepsle1
      rwa [Real.rpow_one] at h
    have h2 := Nat.floor_le_floor hle
    rwa [Nat.floor_natCast] at h2
  -- logarithms
  have hyNrpos : (0 : ℝ) < ((yN N : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((yN N : ℕ) : ℝ) := by exact_mod_cast h2yN
    linarith
  have hyIr : (2 : ℝ) ≤ ((yI N : ℕ) : ℝ) := by exact_mod_cast h2yI
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogyNpos : 0 < Real.log (yN N) := by
    have h2 : (2 : ℝ) ≤ ((yN N : ℕ) : ℝ) := by exact_mod_cast h2yN
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
    linarith
  have hlogyIpos : 0 < Real.log (yI N) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hyIr
    linarith
  have hlogmono : Real.log (yN N) ≤ Real.log (yI N) := by
    have hc : ((yN N : ℕ) : ℝ) ≤ ((yI N : ℕ) : ℝ) := by exact_mod_cast hyNyI
    exact Real.log_le_log hyNrpos hc
  have hloglog : L2 N / 2 ≤ Real.log (Real.log (yI N)) :=
    le_trans hloglogyN (Real.log_le_log hlogyNpos hlogmono)
  refine ⟨hyNyI, h2yI, hyIN, hloglog, hlogyIpos, ?_⟩
  -- the ratio bound
  have hloglogN : L2 N ≤ Real.log N := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log N by linarith)
    have he : L2 N = Real.log (Real.log N) := rfl
    rw [he]; linarith
  have h2j4 : 2 * j ^ 4 ≤ Real.log N := le_trans hkey hloglogN
  set x : ℝ := (N : ℝ) ^ epsI N with hxdef
  have hx0 : 0 < x := by rw [hxdef]; exact Real.rpow_pos_of_pos hNpos _
  have hlogx : Real.log x = epsI N * Real.log N := by
    rw [hxdef, Real.log_rpow hNpos]
  have hlogx2 : (2 : ℝ) ≤ Real.log x := by
    rw [hlogx, heps, div_mul_eq_mul_div, le_div_iff₀ hj4pos]
    linarith
  have hx2 : (2 : ℝ) ≤ x := by
    have h1 : Real.exp 2 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hlogx2
    rw [Real.exp_log hx0] at h1
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hydef : ((yI N : ℕ) : ℝ) = ((⌊x⌋₊ : ℕ) : ℝ) := rfl
  have hyIx : x - 1 < ((yI N : ℕ) : ℝ) := by
    rw [hydef]; linarith [Nat.lt_floor_add_one x]
  have hhalf : x / 2 ≤ ((yI N : ℕ) : ℝ) := by linarith
  have hlogyI_ge : Real.log x - Real.log 2 ≤ Real.log (yI N) := by
    have h := Real.log_le_log (by positivity) hhalf
    rwa [Real.log_div (ne_of_gt hx0) (by norm_num)] at h
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlow : epsI N * Real.log N / 2 ≤ Real.log (yI N) := by
    rw [hlogx] at hlogyI_ge
    have h2 : (2 : ℝ) ≤ epsI N * Real.log N := by rw [← hlogx]; exact hlogx2
    linarith
  rw [div_le_iff₀ hlogyIpos]
  have hid : 2 * j ^ 4 * (epsI N * Real.log N / 2) = Real.log N := by
    rw [heps]
    field_simp
  linarith [mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * j ^ 4)]

theorem yI_tendsto : Tendsto yI atTop atTop :=
  tendsto_atTop_mono' atTop (by filter_upwards [yI_facts] with N h using h.1) yN_tendsto

theorem JI_le_J1 (N : ℕ) : JI P N ≤ J1 N := min_le_left _ _

theorem JI_le_L3 : ∀ᶠ N : ℕ in atTop, (JI P N : ℝ) ≤ L3 N := by
  filter_upwards [L3_tendsto.eventually_ge_atTop 0] with N hL
  have h1 : JI P N ≤ J1 N := min_le_left _ _
  have h2 : ((J1 N : ℕ) : ℝ) ≤ L3 N := Nat.floor_le (by linarith)
  have h3 : (JI P N : ℝ) ≤ ((J1 N : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem JI_le_mass (N : ℕ) : 8 * (JI P N : ℝ) ≤ recipSumLe P (yI N) := by
  have hS := recipSumLe_nonneg P (yI N)
  have h1 : JI P N ≤ ⌊recipSumLe P (yI N) / 8⌋₊ := min_le_right _ _
  have h2 : ((⌊recipSumLe P (yI N) / 8⌋₊ : ℕ) : ℝ) ≤ recipSumLe P (yI N) / 8 :=
    Nat.floor_le (by positivity)
  have h3 : (JI P N : ℝ) ≤ ((⌊recipSumLe P (yI N) / 8⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem JI_tendsto (hP : DivergentRecip P) : Tendsto (JI P) atTop atTop := by
  have hA : Tendsto J1 atTop atTop := J1_tendsto
  have hB : Tendsto (fun N : ℕ => ⌊recipSumLe P (yI N) / 8⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (((recipSumLe_tendsto_atTop P hP).comp yI_tendsto).atTop_div_const (by norm_num))
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hA.eventually_ge_atTop b, hB.eventually_ge_atTop b] with N h1 h2
  exact le_min h1 h2

/-- In the first branch of the `min`, `J_N ≥ L₃N − 1`. -/
theorem JI_lower {N : ℕ} (hcase : J1 N ≤ ⌊recipSumLe P (yI N) / 8⌋₊) (hL : 0 ≤ L3 N) :
    L3 N - 1 ≤ (JI P N : ℝ) := by
  have h : JI P N = J1 N := min_eq_left hcase
  rw [h]
  have h2 : L3 N < ((J1 N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (L3 N)
  linarith

/-! ### Fresh mass under `SparseIter3` -/

/-- Dominated-Abel bound, uniformly in the upper endpoint: on `(y_N, M+1]`,
`L₃t ≥ L₃(y_N) ≥ L₃N − log 2 ≥ L₃N/2`, so the relative density is `≤ 8/(L₃N)^3`. -/
theorem fresh_bound_iter3 (hS : SparseIter3 P) : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, yI N ≤ M →
    recipSumIoc P (yI N) M
      ≤ (8 / (L3 N) ^ 3) * (9 + 12 * Real.log (Real.log M / Real.log (yI N))) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hS
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, yI_facts,
    yI_tendsto.eventually_ge_atTop x₀] with N hN hL hL3 hyI hy0 M hM
  obtain ⟨-, h2y, -, hloglogy, hlogypos, -⟩ := hyI
  have hpos : 0 < L2 N := by linarith
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hδ : (0 : ℝ) ≤ 8 / (L3 N) ^ 3 := by positivity
  have hyr : (2 : ℝ) ≤ ((yI N : ℕ) : ℝ) := by exact_mod_cast h2y
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hdom : ∀ t : ℕ, yI N < t → t ≤ M + 1 →
      (piP P t : ℝ) ≤ (8 / (L3 N) ^ 3) * (t.primesBelow.card : ℝ) := by
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
    have hpow : (L3 N) ^ 3 / 8 ≤ (L3 t) ^ 3 := by
      have h3 := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ L3 N / 2) hhalf 3
      calc (L3 N) ^ 3 / 8 = (L3 N / 2) ^ 3 := by ring
        _ ≤ (L3 t) ^ 3 := h3
    have hppos : (0 : ℝ) ≤ (piP P t : ℝ) := Nat.cast_nonneg _
    have hkey : (piP P t : ℝ) * ((L3 N) ^ 3 / 8) ≤ (t.primesBelow.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hpow hppos) hsp
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (L3 N) ^ 3)]
    nlinarith
  exact recipSumIoc_le_of_dominated' P hδ h2y hM hdom

/-- Fresh mass between `y_N` and `N`: `log(log N/log y_N) ≤ log(2 J₁^4) ≤ 1 + 4 L₄N`. -/
theorem fresh_mass_iter3 (hS : SparseIter3 P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yI N) N ≤ (8 / (L3 N) ^ 3) * (21 + 48 * L4 N) := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, yI_facts, J1_facts,
    fresh_bound_iter3 P hS] with N hN _hL hL3 hyI hJ hfb
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
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
  linarith [mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 8 / (L3 N) ^ 3)]

/-- Fresh mass between `y_N` and `2N` is eventually at most `1`
(`log(log 2N/log y_N) ≤ log(4 J₁^4) ≤ 2 + 4 L₄N`, and `(8/(L₃N)^3)(33 + 48 L₄N) → 0`). -/
theorem fresh_mass_two_iter3 (hS : SparseIter3 P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yI N) (2 * N) ≤ 1 := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 26, yI_facts, J1_facts,
    fresh_bound_iter3 P hS] with N hN hL hL3 hyI hJ hfb
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
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
      ≤ (8 / (L3 N) ^ 3) * (9 + 12 * (2 + 4 * L4 N)) := by
    refine le_trans hb ?_
    have h9 : (9 : ℝ) + 12 * Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
        ≤ 9 + 12 * (2 + 4 * L4 N) := by
      rw [hexp] at hlr; linarith
    exact mul_le_mul_of_nonneg_left h9 (by positivity)
  have hL4le : L4 N ≤ L3 N := by
    have h := Real.log_le_sub_one_of_pos hu0
    have he : L4 N = Real.log (L3 N) := rfl
    rw [he]; linarith
  have hfin : (8 / (L3 N) ^ 3) * (9 + 12 * (2 + 4 * L4 N)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    have h2 : (676 : ℝ) ≤ (L3 N) ^ 2 := by nlinarith
    have h3 : 648 * L3 N ≤ (L3 N) ^ 3 := by nlinarith
    linarith
  linarith

end NormalNumbers.PrimeModel.FamilyIter
