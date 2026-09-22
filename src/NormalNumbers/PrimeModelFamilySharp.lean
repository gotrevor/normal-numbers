import NormalNumbers.PrimeModelFamilySharpMass

/-!
# Sharper family theorem, part B: the four limits and the assembly

Consumes `window_bound_regime` (polynomial constants) directly, along the schedule
`JS P N = min(⌊L₃N⌋₊, ⌊S_P(y_N)/8⌋₊)`, `ε_N = 2/L₂N`, `y_N = ⌊N^{ε_N}⌋₊`.

Main theorem: `isNormal_subsetLambert_of_sparseIter : SparseIter P → DivergentRecip P →
IsNormal 4 (subsetLambert P 4)`, i.e. every prime set with `π_P(x)(log log log x)^5 ≤ π(x)`
eventually and divergent reciprocal sum has a normal base-4 Lambert constant.

Write `t = L₂N`, `u = L₃N = log t`, `J = JS P N ≤ u`.
1. Transfer: `24J √log(1/ε) √(2R)` with `R ≤ 672/u^4`, `log(1/ε) ≤ u`: `≤ 24u √u √(1344/u^4)
   ≤ 880/√u → 0`.
2. Old mass: `e^{3J} e^{−S(y_N)} ≤ e^{−5S/8} → 0` (`8J ≤ S`, `S → ∞`).
3. Sieve: coefficient `2J² + 2J e^{20} + 4 + 2·4^J ≤ e^{22} 4^u = e^{22} t^{log 4}`, exponent
   `−1/(8J²ε) = −t/(16J²) ≤ −t/(16u²)`; product `→ 0` since `t/(16u²) − (log 4)u − 22 → ∞`.
4. Tail: `(S_P(2N) + 5J + 12)/4^J`.  Branch `J = ⌊u⌋₊`: `4^J ≥ t^{log 4}/4`, numerator
   `≤ 12(t+1) + 21 + 5u + 12 ≤ 30t`, ratio `≤ 120 t^{1 − log 4} → 0`.  Branch `J = ⌊S/8⌋₊`:
   `S_P(2N) ≤ S + 1 ≤ 8J + 9`, ratio `≤ (13J + 21)/4^J → 0`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilySharp

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family

variable (P : ℕ → Prop) [DecidablePred P]

/-- `c (log t)^k ≤ t^r` eventually, for any `k`, `r, c > 0`. -/
theorem eventually_pow_log_le (k : ℕ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, c * (Real.log t) ^ k ≤ t ^ r := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    filter_upwards [(tendsto_rpow_atTop hr).eventually_ge_atTop c] with t ht
    simpa using ht
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hrk : 0 < r / (k : ℝ) := by positivity
    have h := tendsto_log_div_rpow (r := r / (k : ℝ)) hrk
    have hpow : Tendsto (fun t : ℝ => (Real.log t / t ^ (r / (k : ℝ))) ^ k) atTop (𝓝 0) := by
      simpa [zero_pow hk.ne'] using h.pow k
    have h3 : ∀ᶠ t : ℝ in atTop, (Real.log t / t ^ (r / (k : ℝ))) ^ k ≤ 1 / c :=
      hpow.eventually_le_const (by positivity)
    filter_upwards [h3, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hrp : (0 : ℝ) < t ^ (r / (k : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have hmul : (t ^ (r / (k : ℝ))) ^ k = t ^ r := by
      rw [← Real.rpow_natCast (t ^ (r / (k : ℝ))) k, ← Real.rpow_mul ht0.le]
      congr 1
      field_simp
    have h4 := mul_le_mul_of_nonneg_right ht (pow_pos hrp k).le
    rw [div_pow, hmul, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos ht0 r))] at h4
    have h6 := mul_le_mul_of_nonneg_left h4 hc.le
    rwa [show c * (1 / c * t ^ r) = t ^ r by field_simp] at h6

/-- Term 1 (transfer): `24 J √log(1/ε_N) √(2 recipSumIoc P y_N N) → 0`. -/
theorem term_one_iter (hS : SparseIter P) :
    Tendsto (fun N : ℕ => 24 * (JS P N : ℝ) *
      (Real.sqrt (Real.log (1 / epsN N)) * Real.sqrt (2 * recipSumIoc P (yN N) N)))
      atTop (𝓝 0) := by
  have hsqrtL3 : Tendsto (fun N : ℕ => Real.sqrt (L3 N)) atTop atTop := by
    have := Real.tendsto_sqrt_atTop.comp L3_tendsto
    simpa [Function.comp_def] using this
  have hG : Tendsto (fun N : ℕ => 880 / Real.sqrt (L3 N)) atTop (𝓝 0) := by
    simpa using hsqrtL3.const_div_atTop (880 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hG
  · positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    fresh_mass_iter P hS, JS_le_L3 P] with N hN hL hfm hJ
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  set t : ℝ := L2 N with htdef
  set u : ℝ := L3 N with hudef
  have ht0 : 0 < t := by rw [htdef]; linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hulog : u = Real.log t := L3_eq N
  have hA0 : 0 ≤ recipSumIoc P (yN N) N := recipSumIoc_nonneg P _ _
  have hepslog : Real.log (1 / epsN N) ≤ u := by
    have he : (1 : ℝ) / epsN N = t / 2 := by
      show (1 : ℝ) / (2 / t) = t / 2
      field_simp
    rw [he, Real.log_div (ne_of_gt ht0) (by norm_num), ← hulog]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have h2A : 2 * recipSumIoc P (yN N) N ≤ 1344 / u ^ 4 := by
    have : (2 : ℝ) * recipSumIoc P (yN N) N ≤ 2 * (672 / u ^ 4) := by linarith
    calc 2 * recipSumIoc P (yN N) N ≤ 2 * (672 / u ^ 4) := this
      _ = 1344 / u ^ 4 := by ring
  have hsq1 : Real.sqrt (Real.log (1 / epsN N)) ≤ Real.sqrt u := Real.sqrt_le_sqrt hepslog
  have hsq2 : Real.sqrt (2 * recipSumIoc P (yN N) N) ≤ Real.sqrt (1344 / u ^ 4) :=
    Real.sqrt_le_sqrt h2A
  have hprod : Real.sqrt u * Real.sqrt (1344 / u ^ 4) ≤ (110 / 3) / (u * Real.sqrt u) := by
    rw [← Real.sqrt_mul hu0.le]
    have hCsq : ((110 / 3 : ℝ) / (u * Real.sqrt u)) ^ 2 = (12100 / 9) / u ^ 3 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hu0.le, show u ^ 2 * u = u ^ 3 by ring]
      norm_num
    have hle : u * (1344 / u ^ 4) ≤ ((110 / 3 : ℝ) / (u * Real.sqrt u)) ^ 2 := by
      rw [hCsq, show u * (1344 / u ^ 4) = 1344 / u ^ 3 by field_simp]
      gcongr
      norm_num
    calc Real.sqrt (u * (1344 / u ^ 4))
        ≤ Real.sqrt (((110 / 3 : ℝ) / (u * Real.sqrt u)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (110 / 3) / (u * Real.sqrt u) := Real.sqrt_sq (by positivity)
  have hAB : Real.sqrt (Real.log (1 / epsN N)) * Real.sqrt (2 * recipSumIoc P (yN N) N)
      ≤ (110 / 3) / (u * Real.sqrt u) :=
    le_trans (mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hprod
  have hfin : 24 * u * ((110 / 3 : ℝ) / (u * Real.sqrt u)) = 880 / Real.sqrt u := by
    field_simp
    ring
  calc 24 * (JS P N : ℝ) * (Real.sqrt (Real.log (1 / epsN N))
        * Real.sqrt (2 * recipSumIoc P (yN N) N))
      ≤ 24 * u * ((110 / 3 : ℝ) / (u * Real.sqrt u)) := by
        refine mul_le_mul (by linarith) hAB (by positivity) (by linarith)
    _ = 880 / Real.sqrt u := hfin

/-- Term 2 (old mass): `e^{3J} exp(−recipSumLe P y_N) → 0`. -/
theorem term_two_iter (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => Real.exp (3 * (JS P N : ℝ)) * Real.exp (- recipSumLe P (yN N)))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => Real.exp (- (recipSumLe P (yN N) / 2))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp ((mass_tendsto P hP).atTop_div_const (by norm_num))
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N => ?_) hg
  · positivity
  · have hJ := JS_le_mass P N
    have hS0 := recipSumLe_nonneg P (yN N)
    calc Real.exp (3 * (JS P N : ℝ)) * Real.exp (- recipSumLe P (yN N))
        = Real.exp (3 * (JS P N : ℝ) + - recipSumLe P (yN N)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (- (recipSumLe P (yN N) / 2)) := Real.exp_le_exp.mpr (by linarith)

/-- Term 3 (sieve): `(2J² + 2J e^{20} + 4 + 2·4^J) exp(−1/(8J²ε_N)) → 0`. -/
theorem term_three_iter (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ =>
      (2 * (JS P N : ℝ) ^ 2 + 2 * (JS P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JS P N))
        * Real.exp (-1 / (8 * (JS P N : ℝ) ^ 2 * epsN N)))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => Real.exp (- Real.sqrt (L2 N))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.sqrt (L2 N)) atTop atTop := by
      have := Real.tendsto_sqrt_atTop.comp L2_tendsto
      simpa [Function.comp_def] using this
    have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hg
  · positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JS_le_L3 P,
    (JS_tendsto P hP).eventually_ge_atTop 1,
    L2_tendsto.eventually (eventually_pow_log_le 3 (r := (1/2 : ℝ)) (c := (400 : ℝ))
      (by norm_num) (by norm_num)),
    L2_tendsto.eventually (eventually_pow_log_le 2 (r := (1/2 : ℝ)) (c := (32 : ℝ))
      (by norm_num) (by norm_num))] with N hN hL hJle hJ1 ha hb
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  set t : ℝ := L2 N with htdef
  set u : ℝ := L3 N with hudef
  set J : ℝ := (JS P N : ℝ) with hJdef
  have ht0 : 0 < t := by rw [htdef]; linarith
  have hulog : u = Real.log t := L3_eq N
  rw [← Real.sqrt_eq_rpow, ← hulog] at ha hb
  set s : ℝ := Real.sqrt t with hsdef
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hs50 : (50 : ℝ) ≤ s := by
    have : Real.sqrt (2500 : ℝ) ≤ s := Real.sqrt_le_sqrt hL
    rwa [show (2500 : ℝ) = 50 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 50)] at this
  have hJpos : (1 : ℝ) ≤ J := by rw [hJdef]; exact_mod_cast hJ1
  have hJu : J ≤ u := hJle
  -- the coefficient
  have hJsqn : (JS P N) ^ 2 ≤ 4 ^ (JS P N) := by
    have h := Nat.lt_two_pow_self (n := JS P N)
    calc (JS P N) ^ 2 ≤ (2 ^ (JS P N)) ^ 2 := Nat.pow_le_pow_left h.le 2
      _ = 4 ^ (JS P N) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hJlen : (JS P N) ≤ 4 ^ (JS P N) := by
    have h := Nat.lt_two_pow_self (n := JS P N)
    calc (JS P N) ≤ 2 ^ (JS P N) := h.le
      _ ≤ 4 ^ (JS P N) := Nat.pow_le_pow_left (by norm_num) _
  have hJsq : J ^ 2 ≤ (4 : ℝ) ^ (JS P N) := by
    rw [hJdef]; exact_mod_cast hJsqn
  have hJle4 : J ≤ (4 : ℝ) ^ (JS P N) := by
    rw [hJdef]; exact_mod_cast hJlen
  have h1le4 : (1 : ℝ) ≤ (4 : ℝ) ^ (JS P N) := one_le_pow₀ (by norm_num)
  have hexp22 : (8 : ℝ) + 2 * Real.exp 20 ≤ Real.exp 22 := by
    have h1 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h2 : (8 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
    have h3 : Real.exp 22 = Real.exp 20 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 20]
  have hcoef : 2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JS P N)
      ≤ Real.exp 22 * (4 : ℝ) ^ (JS P N) := by
    have he20 : (0 : ℝ) < Real.exp 20 := Real.exp_pos 20
    nlinarith [hJsq, hJle4, h1le4, hexp22, he20]
  -- the exponent
  have hden : -1 / (8 * J ^ 2 * epsN N) = -(t / (16 * J ^ 2)) := by
    have he : epsN N = 2 / t := rfl
    rw [he]
    field_simp
    ring
  have h4J : (4 : ℝ) ^ (JS P N) = Real.exp (Real.log 4 * J) := by
    rw [hJdef, ← Real.rpow_natCast (4 : ℝ) (JS P N),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4)]
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
  have hlog40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- the arithmetic
  have hquot : 22 + 3 * u + s ≤ t / (16 * u ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have k1 : 352 * u ^ 2 + 48 * u ^ 3 ≤ s := by nlinarith
    have k2 : 16 * u ^ 2 * s ≤ s ^ 2 / 2 := by nlinarith
    have k3 : s ≤ s ^ 2 / 2 := by nlinarith
    nlinarith [k1, k2, k3, hs2]
  have hmono : t / (16 * u ^ 2) ≤ t / (16 * J ^ 2) := by
    apply div_le_div_of_nonneg_left ht0.le (by positivity)
    nlinarith
  have hlin : Real.log 4 * J ≤ 3 * u := by nlinarith
  calc (2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JS P N))
        * Real.exp (-1 / (8 * J ^ 2 * epsN N))
      = (2 * J ^ 2 + 2 * J * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JS P N))
        * Real.exp (-(t / (16 * J ^ 2))) := by rw [hden]
    _ ≤ (Real.exp 22 * (4 : ℝ) ^ (JS P N)) * Real.exp (-(t / (16 * J ^ 2))) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = Real.exp (22 + Real.log 4 * J + -(t / (16 * J ^ 2))) := by
        rw [h4J, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)

/-- The L¹ tail: `(recipSumLe P (2N) + 5J + 12)/4^J → 0`. -/
theorem tail_iter (hS : SparseIter P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JS P N : ℝ) + 12) / (4 : ℝ) ^ JS P N)
      atTop (𝓝 0) := by
  set ρ : ℝ := Real.log 4 - 1 with hρdef
  have hlog4 : 1 < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  -- majorant 1
  have hf : Tendsto (fun N : ℕ => (13 * (JS P N : ℝ) + 21) / (4 : ℝ) ^ (JS P N))
      atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
    have hsum : Tendsto
        (fun n : ℕ => 13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n))
        atTop (𝓝 0) := by
      simpa using (h1.const_mul (13 : ℝ)).add (h0.const_mul (21 : ℝ))
    refine Tendsto.congr (fun N => ?_) (hsum.comp (JS_tendsto P hP))
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
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JS_le_L3 P,
    fresh_mass_two_iter P hS, yN_facts] with N hN hL hJle hfm2 hyf
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  obtain ⟨-, hyN, -⟩ := hyf
  have ht0 : 0 < L2 N := by linarith
  have hulog : L3 N = Real.log (L2 N) := L3_eq N
  have hrp : (0 : ℝ) < (L2 N) ^ (-ρ) := Real.rpow_pos_of_pos ht0 _
  have hpow0 : (0 : ℝ) < (4 : ℝ) ^ (JS P N) := by positivity
  have hfnn : (0 : ℝ) ≤ (13 * (JS P N : ℝ) + 21) / (4 : ℝ) ^ (JS P N) := by positivity
  have hgnn : (0 : ℝ) ≤ 120 * (L2 N) ^ (-ρ) := by positivity
  rcases le_total (⌊L3 N⌋₊) (⌊recipSumLe P (yN N) / 8⌋₊) with hcase | hcase
  · -- `J = ⌊L₃⌋₊`, so `4^J ≥ (L₂N)^{log 4}/4`
    have hJlow : L3 N - 1 ≤ (JS P N : ℝ) := JS_lower P hcase (by linarith)
    have hpow : (L2 N) ^ Real.log 4 / 4 ≤ (4 : ℝ) ^ (JS P N) := by
      have h1 : (4 : ℝ) ^ (JS P N) = (4 : ℝ) ^ ((JS P N : ℕ) : ℝ) := (Real.rpow_natCast 4 _).symm
      have h2 : (4 : ℝ) ^ (L3 N - 1) ≤ (4 : ℝ) ^ ((JS P N : ℕ) : ℝ) :=
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
    have hnum : recipSumLe P (2 * N) + 5 * (JS P N : ℝ) + 12 ≤ 30 * L2 N := by
      have h5 : (JS P N : ℝ) ≤ L3 N := hJle
      linarith
    have h30 : (0 : ℝ) ≤ 30 * L2 N := by linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JS P N : ℝ) + 12) / (4 : ℝ) ^ (JS P N)
        ≤ (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) :=
      div_le_div₀ h30 hnum (by positivity) hpow
    have hfin : (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) = 120 * (L2 N) ^ (-ρ) := by
      rw [hρdef, show -(Real.log 4 - 1) = 1 - Real.log 4 by ring, Real.rpow_sub ht0,
        Real.rpow_one]
      field_simp
      norm_num
    linarith [hstep, hfin.le, hfin.ge, hfnn]
  · -- `J = ⌊S/8⌋₊`
    have hJeq : JS P N = ⌊recipSumLe P (yN N) / 8⌋₊ := min_eq_right hcase
    have hSlt : recipSumLe P (yN N) < 8 * (JS P N : ℝ) + 8 := by
      have := Nat.lt_floor_add_one (recipSumLe P (yN N) / 8)
      rw [← hJeq] at this
      linarith
    have hsplit : recipSumLe P (2 * N)
        = recipSumLe P (yN N) + recipSumIoc P (yN N) (2 * N) :=
      recipSumLe_add_recipSumIoc P (le_trans hyN (by omega))
    have hnum : recipSumLe P (2 * N) + 5 * (JS P N : ℝ) + 12 ≤ 13 * (JS P N : ℝ) + 21 := by
      rw [hsplit]; linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JS P N : ℝ) + 12) / (4 : ℝ) ^ (JS P N)
        ≤ (13 * (JS P N : ℝ) + 21) / (4 : ℝ) ^ (JS P N) :=
      div_le_div_of_nonneg_right hnum hpow0.le
    linarith [hstep, hgnn]

/-- `TailOK P (JS P)`. -/
theorem tailOK_iter (hS : SparseIter P) (hP : DivergentRecip P) : TailOK P (JS P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_iter P hS hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JS P N) N hN

/-- Eventually `Regime N (JS P N) (epsN N)` (needs `15360 · L₃N ≤ L₂N`, `JS ≥ 1`, `N ≥ 3`). -/
theorem regime_iter (hP : DivergentRecip P) :
    ∀ᶠ N : ℕ in atTop, Regime N (JS P N) (epsN N) := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, epsN_range,
    (JS_tendsto P hP).eventually_ge_atTop 1, JS_le_L3 P,
    L2_tendsto.eventually (eventually_pow_log_le 1 (r := (1 : ℝ)) (c := (15360 : ℝ))
      (by norm_num) (by norm_num))] with N hN hL hε hJ1 hJle hlog
  refine ⟨hN, hJ1, hε.1, ?_⟩
  have ht0 : 0 < L2 N := by linarith
  have hJpos : (1 : ℝ) ≤ (JS P N : ℝ) := by exact_mod_cast hJ1
  have hlog' : 15360 * L3 N ≤ L2 N := by
    rw [L3_eq]
    simpa [Real.rpow_one, pow_one] using hlog
  show epsN N ≤ 1 / (7680 * (JS P N : ℝ))
  have he : epsN N = 2 / L2 N := rfl
  rw [he, div_le_div_iff₀ ht0 (by positivity)]
  linarith

/-- `KMT_along P (JS P)` from `window_bound_regime` and the three limits. -/
theorem kmt_along_iter (hS : SparseIter P) (hP : DivergentRecip P) : KMT_along P (JS P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      24 * (JS P N : ℝ) * (Real.sqrt (Real.log (1 / epsN N))
          * Real.sqrt (2 * recipSumIoc P (yN N) N))
        + Real.exp (3 * (JS P N : ℝ)) * Real.exp (- recipSumLe P (yN N))
        + (2 * (JS P N : ℝ) ^ 2 + 2 * (JS P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JS P N))
            * Real.exp (-1 / (8 * (JS P N : ℝ) ^ 2 * epsN N))) atTop (𝓝 0) := by
    have := ((term_one_iter P hS).add (term_two_iter P hP)).add (term_three_iter P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [regime_iter P hP,
    (JS_tendsto P hP).eventually_ge_atTop (h.natAbs + 1)] with N hR hJ
  have hntw : NontrivialWindow (JS P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := window_bound_regime P h hntw hR
  have hy : yOf N (epsN N) = yN N := rfl
  rw [hy] at hb
  linarith [hb]

/-- **The sharper family theorem.**  Every prime set with `π_P(x) (log log log x)^5 ≤ π(x)`
eventually and divergent reciprocal sum has a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sparseIter (hS : SparseIter P) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JS P) (tailOK_iter P hS hP) (kmt_along_iter P hS hP)

end NormalNumbers.PrimeModel.FamilySharp
