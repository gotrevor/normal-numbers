import NormalNumbers.PrimeModelFamilyIterMass

/-!
# Family theorem with `ε = J₁^{-4}`, part B: the four limits and the assembly

Main theorem: `isNormal_subsetLambert_of_sparseIter3 : SparseIter3 P → DivergentRecip P →
IsNormal 4 (subsetLambert P 4)`: every prime set with `π_P(x)(log log log x)^3 ≤ π(x)`
eventually and divergent reciprocal sum has a normal base-4 Lambert constant.

Write `u = L₃N`, `v = L₄N = log u`, `J₁ = J1 N ≤ u`, `J = JI P N ≤ J₁`, `ε = epsI N = J₁^{-4}`.
1. Transfer: `24J √log(1/ε) √(2R)` with `log(1/ε) ≤ 4v`, `R ≤ (8/u³)(21 + 48v) ≤ 552 v/u³`
   (`v ≥ 1`): `≤ 24u · 2√v · √(1104 v/u³) ≤ 1600 v/√u → 0`.
2. Old mass: `e^{3J} e^{−S(y_N)} ≤ e^{−5S/8} → 0`.
3. Sieve: exponent `−1/(8J²ε) = −J₁⁴/(8J²) ≤ −J₁²/8`; coefficient `≤ e^{22} 4^{J₁}`; product
   `≤ exp(22 + J₁ log 4 − J₁²/8) ≤ exp(−J₁) → 0` once `J₁ ≥ 40`.
4. Tail: as in `tail_iter` with `JI_lower`, `recipSumLe_le_crude`, `fresh_mass_two_iter3`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyIter

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilySharp

variable (P : ℕ → Prop) [DecidablePred P]

/-- Term 1 (transfer): `24 J √log(1/ε_N) √(2 recipSumIoc P y_N N) → 0`. -/
theorem term_one_iter3 (hS : SparseIter3 P) :
    Tendsto (fun N : ℕ => 24 * (JI P N : ℝ) *
      (Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * recipSumIoc P (yI N) N)))
      atTop (𝓝 0) := by
  have hG : Tendsto (fun N : ℕ => 1600 * L4 N / Real.sqrt (L3 N)) atTop (𝓝 0) := by
    have h := (tendsto_log_div_rpow (r := (1/2 : ℝ)) (by norm_num)).comp L3_tendsto
    have h2 := h.const_mul (1600 : ℝ)
    simpa [Function.comp_def, Real.sqrt_eq_rpow, L4, mul_div_assoc] using h2
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hG
  · positivity
  filter_upwards [L2_tendsto.eventually_ge_atTop 2500, L4_tendsto.eventually_ge_atTop 1,
    JI_le_L3 P, epsI_facts, fresh_mass_iter3 P hS] with N hL hv1 hJ hef hfm
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  set u : ℝ := L3 N with hudef
  set v : ℝ := L4 N with hvdef
  set W : ℝ := recipSumIoc P (yI N) N with hWdef
  have hu0 : (0 : ℝ) < u := by linarith
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hepslog : Real.log (1 / epsI N) ≤ 4 * v := hef.2.2.2.2
  have hW0 : 0 ≤ W := recipSumIoc_nonneg P _ _
  have hWu : W * u ^ 3 ≤ 8 * (21 + 48 * v) := by
    calc W * u ^ 3 ≤ (8 / u ^ 3) * (21 + 48 * v) * u ^ 3 :=
          mul_le_mul_of_nonneg_right hfm hu3.le
      _ = 8 * (21 + 48 * v) := by field_simp
  have hCnn : (0 : ℝ) ≤ (200 / 3) * v / (u * Real.sqrt u) :=
    div_nonneg (by linarith) (mul_nonneg hu0.le (Real.sqrt_nonneg u))
  have hCsq : ((200 / 3 : ℝ) * v / (u * Real.sqrt u)) ^ 2 = (40000 / 9) * v ^ 2 / u ^ 3 := by
    have hsq : (u * Real.sqrt u) ^ 2 = u ^ 3 := by
      rw [mul_pow, Real.sq_sqrt hu0.le]; ring
    rw [div_pow, hsq]; ring
  have hkey : 8 * v * W ≤ (40000 / 9) * v ^ 2 / u ^ 3 := by
    rw [le_div_iff₀ hu3]
    nlinarith [mul_le_mul_of_nonneg_left hWu (by linarith : (0:ℝ) ≤ 8 * v), hv1, sq_nonneg v]
  have hAB : Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * W)
      ≤ (200 / 3) * v / (u * Real.sqrt u) := by
    have hA : Real.sqrt (Real.log (1 / epsI N)) ≤ Real.sqrt (4 * v) := Real.sqrt_le_sqrt hepslog
    have h1 : Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * W)
        ≤ Real.sqrt (4 * v) * Real.sqrt (2 * W) :=
      mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (4 * v) * Real.sqrt (2 * W) = Real.sqrt (8 * v * W) := by
      rw [← Real.sqrt_mul (by linarith)]
      congr 1
      ring
    have h3 : Real.sqrt (8 * v * W) ≤ (200 / 3) * v / (u * Real.sqrt u) := by
      calc Real.sqrt (8 * v * W)
          ≤ Real.sqrt (((200 / 3 : ℝ) * v / (u * Real.sqrt u)) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            rw [hCsq]; exact hkey
        _ = (200 / 3) * v / (u * Real.sqrt u) := Real.sqrt_sq hCnn
    linarith [h1, h2.le, h2.ge, h3]
  have hfin : 24 * u * ((200 / 3 : ℝ) * v / (u * Real.sqrt u)) = 1600 * v / Real.sqrt u := by
    field_simp
    ring
  calc 24 * (JI P N : ℝ) * (Real.sqrt (Real.log (1 / epsI N)) * Real.sqrt (2 * W))
      ≤ 24 * u * ((200 / 3 : ℝ) * v / (u * Real.sqrt u)) := by
        refine mul_le_mul (by linarith) hAB (by positivity) (by linarith)
    _ = 1600 * v / Real.sqrt u := hfin

/-- Term 2 (old mass): `e^{3J} exp(−recipSumLe P y_N) → 0`. -/
theorem term_two_iter3 (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => Real.exp (3 * (JI P N : ℝ)) * Real.exp (- recipSumLe P (yI N)))
      atTop (𝓝 0) := by
  have hmass : Tendsto (fun N : ℕ => recipSumLe P (yI N)) atTop atTop :=
    (recipSumLe_tendsto_atTop P hP).comp yI_tendsto
  have hg : Tendsto (fun N : ℕ => Real.exp (- (recipSumLe P (yI N) / 2))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp (hmass.atTop_div_const (by norm_num))
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N => ?_) hg
  · positivity
  · have hJ := JI_le_mass P N
    have hS0 := recipSumLe_nonneg P (yI N)
    calc Real.exp (3 * (JI P N : ℝ)) * Real.exp (- recipSumLe P (yI N))
        = Real.exp (3 * (JI P N : ℝ) + - recipSumLe P (yI N)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (- (recipSumLe P (yI N) / 2)) := Real.exp_le_exp.mpr (by linarith)

/-- Term 3 (sieve): `(2J² + 2J e^{20} + 4 + 2·4^J) exp(−1/(8J²ε_N)) → 0`. -/
theorem term_three_iter3 (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ =>
      (2 * (JI P N : ℝ) ^ 2 + 2 * (JI P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
        * Real.exp (-1 / (8 * (JI P N : ℝ) ^ 2 * epsI N)))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => Real.exp (-(J1 N : ℝ))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop (R := ℝ).comp J1_tendsto))
    simpa [Function.comp_def] using h
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hg
  · positivity
  filter_upwards [(JI_tendsto P hP).eventually_ge_atTop 1,
    J1_tendsto.eventually_ge_atTop 40] with N hJ1 hj40
  set J : ℝ := (JI P N : ℝ) with hJdef
  set j : ℝ := (J1 N : ℝ) with hjdef
  have hJ1' : (1 : ℝ) ≤ J := by rw [hJdef]; exact_mod_cast hJ1
  have hj40' : (40 : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj40
  have hJj : J ≤ j := by rw [hJdef, hjdef]; exact_mod_cast JI_le_J1 P N
  have hJ0 : (0 : ℝ) < J := by linarith
  have hj0 : (0 : ℝ) < j := by linarith
  -- the coefficient
  have hJsqn : (JI P N) ^ 2 ≤ 4 ^ (JI P N) := by
    have h := Nat.lt_two_pow_self (n := JI P N)
    calc (JI P N) ^ 2 ≤ (2 ^ (JI P N)) ^ 2 := Nat.pow_le_pow_left h.le 2
      _ = 4 ^ (JI P N) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hJlen : (JI P N) ≤ 4 ^ (JI P N) := by
    have h := Nat.lt_two_pow_self (n := JI P N)
    calc (JI P N) ≤ 2 ^ (JI P N) := h.le
      _ ≤ 4 ^ (JI P N) := Nat.pow_le_pow_left (by norm_num) _
  have hJsq : J ^ 2 ≤ (4 : ℝ) ^ (JI P N) := by rw [hJdef]; exact_mod_cast hJsqn
  have hJle4 : J ≤ (4 : ℝ) ^ (JI P N) := by rw [hJdef]; exact_mod_cast hJlen
  have h1le4 : (1 : ℝ) ≤ (4 : ℝ) ^ (JI P N) := one_le_pow₀ (by norm_num)
  have hexp22 : (8 : ℝ) + 2 * Real.exp 20 ≤ Real.exp 22 := by
    have h1 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h2 : (8 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
    have h3 : Real.exp 22 = Real.exp 20 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 20]
  have hmono4 : (4 : ℝ) ^ (JI P N) ≤ (4 : ℝ) ^ (J1 N) :=
    pow_le_pow_right₀ (by norm_num) (JI_le_J1 P N)
  have hcoef : 2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N)
      ≤ Real.exp 22 * (4 : ℝ) ^ (J1 N) := by
    have he20 : (0 : ℝ) < Real.exp 20 := Real.exp_pos 20
    have hstep : 2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N)
        ≤ Real.exp 22 * (4 : ℝ) ^ (JI P N) := by
      nlinarith [hJsq, hJle4, h1le4, hexp22, he20]
    have : Real.exp 22 * (4 : ℝ) ^ (JI P N) ≤ Real.exp 22 * (4 : ℝ) ^ (J1 N) :=
      mul_le_mul_of_nonneg_left hmono4 (Real.exp_pos 22).le
    linarith
  -- the exponent
  have he : epsI N = 1 / j ^ 4 := rfl
  have hden : -1 / (8 * J ^ 2 * epsI N) = -(j ^ 4 / (8 * J ^ 2)) := by
    rw [he]
    field_simp
  have hexpcmp : -(j ^ 4 / (8 * J ^ 2)) ≤ -(j ^ 2 / 8) := by
    have h8J : (0 : ℝ) < 8 * J ^ 2 := by nlinarith
    have hJ2 : J ^ 2 ≤ j ^ 2 := by nlinarith [hJj, hJ1', hj0]
    have : j ^ 2 / 8 ≤ j ^ 4 / (8 * J ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) h8J]
      nlinarith [mul_le_mul_of_nonneg_left hJ2 (by positivity : (0:ℝ) ≤ 8 * j ^ 2)]
    linarith
  have h4j : (4 : ℝ) ^ (J1 N) = Real.exp (Real.log 4 * j) := by
    rw [hjdef, ← Real.rpow_natCast (4 : ℝ) (J1 N),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4)]
  have hlog4 : Real.log 4 < 1.4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h2]; linarith [Real.log_two_lt_d9]
  have harith : 22 + Real.log 4 * j + -(j ^ 4 / (8 * J ^ 2)) ≤ -j := by
    have hq : 5 * j ≤ j ^ 2 / 8 := by nlinarith [hj40']
    nlinarith [hexpcmp, hlog4, hj40', hq]
  calc (2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
        * Real.exp (-1 / (8 * J ^ 2 * epsI N))
      = (2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
        * Real.exp (-(j ^ 4 / (8 * J ^ 2))) := by rw [hden]
    _ ≤ (Real.exp 22 * (4 : ℝ) ^ (J1 N)) * Real.exp (-(j ^ 4 / (8 * J ^ 2))) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = Real.exp (22 + Real.log 4 * j + -(j ^ 4 / (8 * J ^ 2))) := by
        rw [h4j, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-j) := Real.exp_le_exp.mpr harith

/-- The L¹ tail: `(recipSumLe P (2N) + 5J + 12)/4^J → 0`. -/
theorem tail_iter3 (hS : SparseIter3 P) (hP : DivergentRecip P) :
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
    fresh_mass_two_iter3 P hS, yI_facts] with N hN hL hJle hfm2 hyf
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

theorem tailOK_iter3 (hS : SparseIter3 P) (hP : DivergentRecip P) : TailOK P (JI P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_iter3 P hS hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JI P N) N hN

/-- Eventually `Regime N (JI P N) (epsI N)`. -/
theorem regime_iter3 (hP : DivergentRecip P) :
    ∀ᶠ N : ℕ in atTop, Regime N (JI P N) (epsI N) := by
  filter_upwards [eventually_ge_atTop 3, epsI_facts, (JI_tendsto P hP).eventually_ge_atTop 1]
    with N hN hef hJ1
  refine ⟨hN, hJ1, hef.2.2.1, ?_⟩
  have hJ1' : (1 : ℝ) ≤ (JI P N : ℝ) := by exact_mod_cast hJ1
  have hJj : ((JI P N : ℕ) : ℝ) ≤ ((J1 N : ℕ) : ℝ) := by exact_mod_cast JI_le_J1 P N
  have hle : 1 / (7680 * (J1 N : ℝ)) ≤ 1 / (7680 * (JI P N : ℝ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  exact le_trans hef.2.1 hle

theorem kmt_along_iter3 (hS : SparseIter3 P) (hP : DivergentRecip P) : KMT_along P (JI P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      24 * (JI P N : ℝ) * (Real.sqrt (Real.log (1 / epsI N))
          * Real.sqrt (2 * recipSumIoc P (yI N) N))
        + Real.exp (3 * (JI P N : ℝ)) * Real.exp (- recipSumLe P (yI N))
        + (2 * (JI P N : ℝ) ^ 2 + 2 * (JI P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
            * Real.exp (-1 / (8 * (JI P N : ℝ) ^ 2 * epsI N))) atTop (𝓝 0) := by
    have := ((term_one_iter3 P hS).add (term_two_iter3 P hP)).add (term_three_iter3 P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [regime_iter3 P hP,
    (JI_tendsto P hP).eventually_ge_atTop (h.natAbs + 1)] with N hR hJ
  have hntw : NontrivialWindow (JI P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := window_bound_regime P h hntw hR
  have hy : yOf N (epsI N) = yI N := rfl
  rw [hy] at hb
  linarith [hb]

/-- **Family theorem, exponent 3.**  Every prime set with `π_P(x) (log log log x)^3 ≤ π(x)`
eventually and divergent reciprocal sum has a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sparseIter3 (hS : SparseIter3 P) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JI P) (tailOK_iter3 P hS hP) (kmt_along_iter3 P hS hP)

end NormalNumbers.PrimeModel.FamilyIter
