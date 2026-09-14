/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4GridTube

/-!
# G4 §5, the `B` inequality: the tube volume really does tend to zero

`gridFrame_propB_of_bound` reduces brief §4B to **one real inequality** in the schedule
parameters — the `hB` field of `ScheduleWitness`.  This file proves it.

It is the only one of the five witness inequalities that mentions **no** outer scale `X`, no
primes and no progression: it is a statement about `K`, the omitted word's length `ℓ`, the
cylinder depth `M`, and the good-coordinate count `g` alone.  Writing `s = K²`, `r = s^K`,
`H = (s+1)^K`, `η ≤ 2^{−K/4}`, `Lg ≤ r(log 2 + 23√K)` and `(1−1/K)r ≤ g ≤ r`:

    ((4^ℓ−1)^M)^H · η^g · e^{Lg/2} · (√(2πe/g)·√(H+g))^g  ≤  (1/8)/2^r

as soon as `K ≥ 33856·ℓ²·16^ℓ = (184·ℓ·4^ℓ)²`.

The mechanism, on the logarithmic scale and per unit of `r`: the cylinder count contributes
`+(K/4)log 2` (because `4^{ℓM} ≈ η^{−1}`) but is **short** by `K·4^{−ℓ}/(8ℓ)`, since
`log(4^ℓ−1) = 2ℓ log 2 − Θ(4^{−ℓ})` — that deficit is the whole content of "an omitted word
forces covering exponent `d < 1`".  Against it stand the `ε`-fraction of bad coordinates
(`(log 2)/4`), the shape constant (`log 6`), the `2^r` union over good coordinate sets
(`log 2`) and, dominantly, the spectral term `11.5√K`.  The deficit beats them once
`√K ≥ 184·ℓ·4^ℓ`, which is why `K → ∞` is needed and why the bound is uniform in nothing
else.  Bounding the zonotope by a coordinatewise box would delete the deficit, which is
exactly the brief's prohibition.
-/

open Real Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- `log(4^ℓ − 1) ≤ 2ℓ log 2 − 4^{−ℓ}`: the covering-exponent deficit of an omitted word. -/
lemma log_four_pow_sub_one_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Real.log ((4 : ℝ) ^ ℓ - 1) ≤ 2 * ℓ * Real.log 2 - (1 / 4 : ℝ) ^ ℓ := by
  have h4 : (4 : ℝ) ≤ (4 : ℝ) ^ ℓ := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have hpos : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
  have hq : (0 : ℝ) < 1 - (1 / 4 : ℝ) ^ ℓ := by
    have : (1 / 4 : ℝ) ^ ℓ ≤ 1 / 4 := by
      calc (1 / 4 : ℝ) ^ ℓ ≤ (1 / 4 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hℓ
        _ = 1 / 4 := by norm_num
    linarith
  have hfac : (4 : ℝ) ^ ℓ - 1 = (4 : ℝ) ^ ℓ * (1 - (1 / 4 : ℝ) ^ ℓ) := by
    have : (1 / 4 : ℝ) ^ ℓ = ((4 : ℝ) ^ ℓ)⁻¹ := by
      rw [one_div, inv_pow]
    rw [this]
    field_simp
  rw [hfac, Real.log_mul (by positivity) (ne_of_gt hq), Real.log_pow]
  have h1 : Real.log (1 - (1 / 4 : ℝ) ^ ℓ) ≤ -(1 / 4 : ℝ) ^ ℓ := by
    have := Real.log_le_sub_one_of_pos hq
    linarith
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [h2]
  have : (ℓ : ℝ) * (2 * Real.log 2) = 2 * ℓ * Real.log 2 := by ring
  linarith [this]

/-- `H = (K²+1)^K ≤ e^{1/K} · K^{2K} = e^{1/K} r`. -/
lemma hDim_le_exp_mul_rDim {K : ℕ} (hK : 1 ≤ K) :
    (((K ^ 2 + 1) ^ K : ℕ) : ℝ) ≤ Real.exp (1 / K) * (((K ^ 2) ^ K : ℕ) : ℝ) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
  have hsplit : (((K : ℝ)) ^ 2 + 1) ^ K = ((K : ℝ) ^ 2) ^ K * (1 + 1 / (K : ℝ) ^ 2) ^ K := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hstep : (1 : ℝ) + 1 / (K : ℝ) ^ 2 ≤ Real.exp (1 / (K : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (1 / (K : ℝ) ^ 2)
    linarith
  have hpow : ((1 : ℝ) + 1 / (K : ℝ) ^ 2) ^ K ≤ (Real.exp (1 / (K : ℝ) ^ 2)) ^ K :=
    pow_le_pow_left₀ (by positivity) hstep K
  have hexp : (Real.exp (1 / (K : ℝ) ^ 2)) ^ K = Real.exp ((K : ℝ) * (1 / (K : ℝ) ^ 2)) := by
    rw [← Real.exp_nat_mul]
  have hKK : (K : ℝ) * (1 / (K : ℝ) ^ 2) = 1 / (K : ℝ) := by field_simp
  rw [hexp, hKK] at hpow
  push_cast
  rw [hsplit]
  calc ((K : ℝ) ^ 2) ^ K * (1 + 1 / (K : ℝ) ^ 2) ^ K
      ≤ ((K : ℝ) ^ 2) ^ K * Real.exp (1 / (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp (1 / (K : ℝ)) * ((K : ℝ) ^ 2) ^ K := by ring

/-- `r = K^{2K} ≤ (K²+1)^K = H`. -/
lemma rDim_le_hDim (K : ℕ) : (((K ^ 2) ^ K : ℕ) : ℝ) ≤ (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
  have : (K ^ 2) ^ K ≤ (K ^ 2 + 1) ^ K := Nat.pow_le_pow_left (Nat.le_succ _) K
  exact_mod_cast this


/-- `e^{1/K}·(1 − 1/K) ≤ 1` — the only estimate on `H/r` the argument needs. -/
lemma exp_inv_mul_le {K : ℝ} (hK : 0 < K) : Real.exp (1 / K) * (1 - 1 / K) ≤ 1 := by
  have hneg : 1 - 1 / K ≤ Real.exp (-(1 / K)) := by
    have := Real.add_one_le_exp (-(1 / K)); linarith
  have h := mul_le_mul_of_nonneg_left hneg (le_of_lt (Real.exp_pos (1 / K)))
  rwa [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _)] at h

/-- **The shape constant.**  `√(2πe/g)·√(H+g) ≤ 7` whenever `0 ≤ H ≤ e^{1/K}r`,
`(1−1/K)r ≤ g` and `K ≥ 100`: the Gaussian-comparison factor is bounded by an absolute
constant because `H/r → 1` and `g/r → 1`. -/
lemma shape_factor_le {K r H gr : ℝ} (hK : 100 ≤ K) (hr : 0 < r) (hH0 : 0 ≤ H)
    (hH : H ≤ Real.exp (1 / K) * r) (hg : (1 - 1 / K) * r ≤ gr) :
    Real.sqrt (2 * Real.pi * Real.exp 1 / gr) * Real.sqrt (H + gr) ≤ 7 := by
  have hK0 : (0 : ℝ) < K := by linarith
  have h1 : 1 / K ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hK
  have h1Kpos : (0 : ℝ) < 1 / K := by positivity
  have ht : (99 / 100 : ℝ) ≤ 1 - 1 / K := by linarith
  have ht1 : 1 - 1 / K ≤ 1 := by linarith
  have hgr : 0 < gr := lt_of_lt_of_le (by nlinarith) hg
  have hexp := exp_inv_mul_le hK0
  have hexp0 : 0 < Real.exp (1 / K) := Real.exp_pos _
  -- `H (1−1/K)² ≤ gr`
  have hHt : H * (1 - 1 / K) ^ 2 ≤ gr := by
    have h2 : H * (1 - 1 / K) ≤ Real.exp (1 / K) * r * (1 - 1 / K) :=
      mul_le_mul_of_nonneg_right hH (by linarith)
    nlinarith [hg, hexp, hr.le, mul_nonneg hH0 (by linarith : (0:ℝ) ≤ 1 - 1/K)]
  have hH3 : H ≤ (10000 / 9801 : ℝ) * gr := by nlinarith [hHt, ht, hH0]
  -- numeric: `2πe(H+gr) ≤ 49 gr`
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpe : 2 * Real.pi * Real.exp 1 ≤ 22 := by nlinarith [Real.pi_pos]
  have hpe0 : (0 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by positivity
  have hkey : 2 * Real.pi * Real.exp 1 / gr * (H + gr) ≤ 49 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hgr]
    nlinarith [hpe, hH3, hgr, hpe0]
  rw [← Real.sqrt_mul (by positivity)]
  calc Real.sqrt (2 * Real.pi * Real.exp 1 / gr * (H + gr)) ≤ Real.sqrt 49 :=
        Real.sqrt_le_sqrt hkey
    _ = 7 := by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The deficit dominates.**  `K ≥ (184·ℓ·4^ℓ)²` makes the omitted word's covering deficit
`K·4^{−ℓ}/(8ℓ)` beat the spectral term `11.5√K` and every absolute constant. -/
lemma deficit_dominates {ℓ K : ℕ} (hℓ : 1 ≤ ℓ) (hK : 33856 * ℓ ^ 2 * 16 ^ ℓ ≤ K) :
    (11.5 : ℝ) * Real.sqrt K + 2.8 * ℓ + 5.66 ≤ (K : ℝ) / (8 * ℓ) * (1 / 4 : ℝ) ^ ℓ := by
  have hℓ0 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have h4 : (4 : ℝ) ≤ (4 : ℝ) ^ ℓ := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  set c : ℝ := (ℓ : ℝ) * 4 ^ ℓ with hc
  have hc4 : (4 : ℝ) ≤ c := by rw [hc]; nlinarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hcast : ((184 * c) ^ 2 : ℝ) ≤ (K : ℝ) := by
    have h16 : ((16 : ℝ)) ^ ℓ = (4 : ℝ) ^ ℓ * (4 : ℝ) ^ ℓ := by rw [← mul_pow]; norm_num
    have hmain : ((33856 * ℓ ^ 2 * 16 ^ ℓ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    calc ((184 * c) ^ 2 : ℝ) = 33856 * (ℓ : ℝ) ^ 2 * ((4 : ℝ) ^ ℓ * (4 : ℝ) ^ ℓ) := by
          rw [hc]; ring
      _ = ((33856 * ℓ ^ 2 * 16 ^ ℓ : ℕ) : ℝ) := by push_cast [h16]; ring
      _ ≤ (K : ℝ) := hmain
  set u : ℝ := Real.sqrt K with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = (K : ℝ) := Real.sq_sqrt (by positivity)
  have hu184 : 184 * c ≤ u := by
    rw [hu]
    calc 184 * c = Real.sqrt ((184 * c) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hcast
  have hinv : (1 / 4 : ℝ) ^ ℓ = 1 / (4 : ℝ) ^ ℓ := by rw [one_div, inv_pow, one_div]
  have h4ne : ((4 : ℝ) ^ ℓ) ≠ 0 := by positivity
  have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓpos
  have hgoal : (K : ℝ) / (8 * ℓ) * (1 / 4 : ℝ) ^ ℓ = (K : ℝ) / (8 * c) := by
    rw [hinv, hc]; field_simp
  have hlc : (ℓ : ℝ) ≤ c := by rw [hc]; nlinarith
  have hu2 : 184 * c * u ≤ u ^ 2 := by nlinarith [hu184, hu0]
  have huc : 184 * c * c ≤ u * c := mul_le_mul_of_nonneg_right hu184 hcpos.le
  have h1 : 22.4 * (ℓ : ℝ) * c ≤ 22.4 * c * c := by nlinarith [hlc, hcpos]
  have h2 : 45.28 * c ≤ 11.32 * c * c := by nlinarith [hc4, hcpos]
  rw [hgoal, ← husq, le_div_iff₀ (by positivity)]
  nlinarith [hu2, huc, h1, h2, hcpos, hu0, mul_pos hcpos hcpos]


/-- `log 7 ≤ 2`. -/
lemma log_seven_le_two : Real.log 7 ≤ 2 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (7 : ℝ) ≤ Real.exp 2 := by
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  calc Real.log 7 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h2
    _ = 2 := Real.log_exp 2

set_option maxHeartbeats 1600000 in
/-- **The `B` inequality of the §5 schedule** (the `hB` field of `ScheduleWitness`, with
`δ₁ = 1/8`).  With `s = K²`, `r = s^K`, `H = (s+1)^K`, a cylinder depth `M ≈ K/(8ℓ)`, a
resolution `η ≤ 2^{−K/4}` (as `η⁴ ≤ 2^{−K}`), the spectral bound `Lg ≤ r(log 2 + 23√K)` and
`(1−1/K)r ≤ g ≤ r`, the tube volume bound is below `(1/8)/2^r` — hence `PropB (1/8)` through
`gridFrame_propB_of_bound` — as soon as

    K ≥ 33856·ℓ²·16^ℓ = (184·ℓ·4^ℓ)².

The omitted word enters only through `log(4^ℓ−1) = 2ℓ log 2 − Θ(4^{−ℓ})`; that deficit,
multiplied by `H ≥ r`, is what defeats the spectral term `11.5 r√K`. -/
theorem gridB_bound {ℓ K M g : ℕ} {η Lg : ℝ}
    (hℓ : 1 ≤ ℓ) (hK : 33856 * ℓ ^ 2 * 16 ^ ℓ ≤ K)
    (hMlo : K ≤ 8 * ℓ * M) (hMhi : 8 * ℓ * M ≤ K + 8 * ℓ)
    (hη0 : 0 < η) (hη : η ^ 4 ≤ (1 / 2 : ℝ) ^ K)
    (hLg : Lg ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
    (hglo : (1 - 1 / (K : ℝ)) * (((K ^ 2) ^ K : ℕ) : ℝ) ≤ (g : ℝ))
    (hghi : g ≤ (K ^ 2) ^ K) :
    (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ ((K ^ 2 + 1) ^ K) * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g)
            * Real.sqrt ((((K ^ 2 + 1) ^ K : ℕ) : ℝ) + g)) ^ g
      ≤ (1 / 8 : ℝ) / 2 ^ ((K ^ 2) ^ K) := by
  -- ### sizes
  have hℓ0 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hKnat : 541696 ≤ K := by
    have h1 : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 16 ≤ 16 ^ ℓ := by
      calc (16 : ℕ) = 16 ^ 1 := by norm_num
        _ ≤ 16 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
    calc 541696 = 33856 * 1 * 16 := by norm_num
      _ ≤ 33856 * ℓ ^ 2 * 16 ^ ℓ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ ≤ K := hK
  have hK1 : 1 ≤ K := by omega
  have hK100 : (100 : ℝ) ≤ (K : ℝ) := by
    have : (541696 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKnat
    linarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  set r : ℝ := (((K ^ 2) ^ K : ℕ) : ℝ) with hrdef
  set H : ℝ := (((K ^ 2 + 1) ^ K : ℕ) : ℝ) with hHdef
  clear_value r H
  have hr1 : (1 : ℝ) ≤ r := by
    rw [hrdef]
    have : 1 ≤ (K ^ 2) ^ K := Nat.one_le_pow _ _ (pow_pos (show 0 < K by omega) 2)
    exact_mod_cast this
  have hr0 : (0 : ℝ) < r := by linarith
  have hH0 : (0 : ℝ) ≤ H := by rw [hHdef]; exact Nat.cast_nonneg _
  have hHr : H ≤ Real.exp (1 / (K : ℝ)) * r := by
    rw [hHdef, hrdef]; exact hDim_le_exp_mul_rDim hK1
  have hrH : r ≤ H := by rw [hHdef, hrdef]; exact rDim_le_hDim K
  have hgr : (g : ℝ) ≤ r := by rw [hrdef]; exact_mod_cast hghi
  have hgnn : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hgpos : (0 : ℝ) < (g : ℝ) := by
    have hinv0 : 1 / (K : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hK100
    nlinarith [hglo, hr0]
  -- ### the base `b = 4^ℓ − 1`
  have h1le : 1 ≤ 4 ^ ℓ := Nat.one_le_pow _ _ (by norm_num)
  set b : ℝ := (4 : ℝ) ^ ℓ - 1 with hbdef
  clear_value b
  have h4ge : (4 : ℝ) ≤ (4 : ℝ) ^ ℓ := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have hbpos : (0 : ℝ) < b := by rw [hbdef]; linarith
  have hbcast : (((4 ^ ℓ - 1 : ℕ)) : ℝ) = b := by
    rw [hbdef, Nat.cast_sub h1le]; push_cast; ring
  -- ### numeric constants
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  have hlog7 : Real.log 7 ≤ 2 := log_seven_le_two
  have hlog7nn : (0 : ℝ) ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  -- ### `(E − 1)·K/4 ≤ 1/2` for `E = exp(1/K)`
  set E : ℝ := Real.exp (1 / (K : ℝ)) with hEdef
  clear_value E
  have hEpos : (0 : ℝ) < E := by rw [hEdef]; exact Real.exp_pos _
  have hE1 : (1 : ℝ) ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
  have hEmul : E * (1 - 1 / (K : ℝ)) ≤ 1 := by rw [hEdef]; exact exp_inv_mul_le hK0
  have hinvK : 1 / (K : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hK100
  have hEle : E ≤ 100 / 99 := by nlinarith [hEmul, hEpos, hinvK]
  have hEK1 : (E - 1) * ((K : ℝ) / 4) ≤ 1 / 2 := by
    have hmulK := mul_le_mul_of_nonneg_right hEmul (le_of_lt hK0)
    have h1 : (E - 1) * (K : ℝ) ≤ E := by
      have hdiv : E * (1 / (K : ℝ)) * (K : ℝ) = E := by field_simp
      nlinarith [hmulK, hdiv]
    nlinarith [h1, hEle, hK0]
  -- ### the three factor bounds
  have hlogb : Real.log b ≤ 2 * (ℓ : ℝ) * Real.log 2 - (1 / 4 : ℝ) ^ ℓ := by
    rw [hbdef]; exact log_four_pow_sub_one_le hℓ
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hM2 : 2 * (ℓ : ℝ) * (M : ℝ) ≤ (K : ℝ) / 4 + 2 * ℓ := by
    have h : ((8 * ℓ * M : ℕ) : ℝ) ≤ ((K + 8 * ℓ : ℕ) : ℝ) := by exact_mod_cast hMhi
    push_cast at h; linarith
  have hM1 : (K : ℝ) / (8 * ℓ) ≤ (M : ℝ) := by
    have h : ((K : ℕ) : ℝ) ≤ ((8 * ℓ * M : ℕ) : ℝ) := by exact_mod_cast hMlo
    push_cast at h
    rw [div_le_iff₀ (by positivity)]; linarith
  set dfc : ℝ := (K : ℝ) / (8 * ℓ) * (1 / 4 : ℝ) ^ ℓ with hdfc
  clear_value dfc
  have hdef := deficit_dominates hℓ hK
  -- T1
  have hT1 : H * ((M : ℝ) * Real.log b)
      ≤ r * (E * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2) - dfc) := by
    have s1 : (M : ℝ) * Real.log b
        ≤ (2 * (ℓ : ℝ) * (M : ℝ)) * Real.log 2 - (M : ℝ) * (1 / 4 : ℝ) ^ ℓ := by
      have h := mul_le_mul_of_nonneg_left hlogb hMnn
      have e : (M : ℝ) * (2 * (ℓ : ℝ) * Real.log 2 - (1 / 4 : ℝ) ^ ℓ)
          = (2 * (ℓ : ℝ) * (M : ℝ)) * Real.log 2 - (M : ℝ) * (1 / 4 : ℝ) ^ ℓ := by ring
      linarith only [h, e]
    have s2 := mul_le_mul_of_nonneg_left s1 hH0
    have s2' : H * ((2 * (ℓ : ℝ) * (M : ℝ)) * Real.log 2 - (M : ℝ) * (1 / 4 : ℝ) ^ ℓ)
        = H * ((2 * (ℓ : ℝ) * (M : ℝ)) * Real.log 2) - H * ((M : ℝ) * (1 / 4 : ℝ) ^ ℓ) := by
      ring
    have s3 : H * ((2 * (ℓ : ℝ) * (M : ℝ)) * Real.log 2)
        ≤ (E * r) * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2) := by
      refine mul_le_mul hHr (mul_le_mul_of_nonneg_right hM2 hlog2pos.le) ?_ ?_
      · positivity
      · exact mul_nonneg hEpos.le hr0.le
    have s4 : r * dfc ≤ H * ((M : ℝ) * (1 / 4 : ℝ) ^ ℓ) := by
      have e1 : r * dfc = (r * ((K : ℝ) / (8 * ℓ))) * (1 / 4 : ℝ) ^ ℓ := by rw [hdfc]; ring
      have e2 : H * ((M : ℝ) * (1 / 4 : ℝ) ^ ℓ) = (H * (M : ℝ)) * (1 / 4 : ℝ) ^ ℓ := by ring
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul hrH hM1 (by positivity) hH0
    have e3 : r * (E * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2) - dfc)
        = (E * r) * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2) - r * dfc := by ring
    rw [e3]; linarith [s2, s2', s3, s4]
  -- T2
  have hlogη : Real.log η ≤ -((K : ℝ) / 4) * Real.log 2 := by
    have hlp : Real.log (η ^ 4) ≤ Real.log ((1 / 2 : ℝ) ^ K) :=
      Real.log_le_log (pow_pos hη0 4) hη
    rw [Real.log_pow, Real.log_pow] at hlp
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hhalf] at hlp
    push_cast at hlp
    linarith
  have hL0neg : -((K : ℝ) / 4) * Real.log 2 ≤ 0 := by nlinarith [hlog2pos, hK100]
  have hT2 : (g : ℝ) * Real.log η
      ≤ r * (-((K : ℝ) / 4) * Real.log 2 + Real.log 2 / 4) := by
    have e1 : (g : ℝ) * Real.log η ≤ (g : ℝ) * (-((K : ℝ) / 4) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogη hgnn
    have e2 : (g : ℝ) * (-((K : ℝ) / 4) * Real.log 2)
        ≤ ((1 - 1 / (K : ℝ)) * r) * (-((K : ℝ) / 4) * Real.log 2) :=
      mul_le_mul_of_nonpos_right hglo hL0neg
    have e3 : ((1 - 1 / (K : ℝ)) * r) * (-((K : ℝ) / 4) * Real.log 2)
        = r * (-((K : ℝ) / 4) * Real.log 2 + Real.log 2 / 4) := by
      field_simp; ring
    linarith
  -- T3, T4
  have hT3 : Lg / 2 ≤ r * ((Real.log 2 + 23 * Real.sqrt K) / 2) := by
    have e : r * ((Real.log 2 + 23 * Real.sqrt K) / 2)
        = r * (Real.log 2 + 23 * Real.sqrt K) / 2 := by ring
    rw [e]; linarith [hLg]
  have hT4 : (g : ℝ) * Real.log 7 ≤ r * 2 := by nlinarith [hgr, hlog7, hlog7nn, hgnn]
  have hlog8r : Real.log 8 ≤ r * (3 * Real.log 2) := by
    rw [hlog8]; nlinarith [hr1, hlog2pos]
  -- ### the bracket is nonpositive
  set BR : ℝ := E * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2) - dfc
      + (-((K : ℝ) / 4) * Real.log 2 + Real.log 2 / 4)
      + (Real.log 2 + 23 * Real.sqrt K) / 2 + 2 + 3 * Real.log 2 + Real.log 2 with hBR
  have hbracket : BR ≤ 0 := by
    have hE2ℓ : E * (2 * (ℓ : ℝ) * Real.log 2) ≤ 2.8 * ℓ := by
      have h1 : (0 : ℝ) ≤ 2 * (ℓ : ℝ) * Real.log 2 :=
        mul_nonneg (by linarith) hlog2pos.le
      have h2 : E * (2 * (ℓ : ℝ) * Real.log 2) ≤ (100 / 99 : ℝ) * (2 * (ℓ : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right hEle h1
      have h3 : (2 * (ℓ : ℝ)) * Real.log 2 ≤ (2 * (ℓ : ℝ)) * 0.6932 :=
        mul_le_mul_of_nonneg_left hlog2le (by linarith)
      nlinarith [h2, h3, hℓ0]
    have hsplit : E * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2)
        = (E - 1) * ((K : ℝ) / 4) * Real.log 2 + ((K : ℝ) / 4) * Real.log 2
          + E * (2 * (ℓ : ℝ) * Real.log 2) := by ring
    have hEK : (E - 1) * ((K : ℝ) / 4) * Real.log 2 ≤ Real.log 2 / 2 := by
      nlinarith [hEK1, hlog2pos, hE1, hK0]
    have hsk : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg _
    rw [hBR, hsplit]
    nlinarith [hEK, hE2ℓ, hdef, hlog2le, hlog2pos, hsk]
  -- ### the exponent
  have hfinal : H * ((M : ℝ) * Real.log b) + (g : ℝ) * Real.log η + Lg / 2
      + (g : ℝ) * Real.log 7 ≤ -(Real.log 8) - r * Real.log 2 := by
    have hexpand : r * (E * (((K : ℝ) / 4 + 2 * ℓ) * Real.log 2) - dfc)
        + r * (-((K : ℝ) / 4) * Real.log 2 + Real.log 2 / 4)
        + r * ((Real.log 2 + 23 * Real.sqrt K) / 2) + r * 2
        + r * (3 * Real.log 2) + r * Real.log 2 = r * BR := by rw [hBR]; ring
    have hrBR : r * BR ≤ 0 := by nlinarith [mul_nonneg hr0.le (neg_nonneg.mpr hbracket)]
    linarith [hT1, hT2, hT3, hT4, hlog8r, hexpand, hrBR]
  -- ### assemble
  have hSnn : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (H + g) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hHrE : H ≤ Real.exp (1 / (K : ℝ)) * r := by rw [hHdef, hrdef]; exact hDim_le_exp_mul_rDim hK1
  have hS : Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (H + g) ≤ 7 :=
    shape_factor_le hK100 hr0 hH0 hHrE hglo
  have hA : (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ ((K ^ 2 + 1) ^ K)
      = Real.exp (H * ((M : ℝ) * Real.log b)) := by
    have hcast : (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) = b ^ M := by rw [Nat.cast_pow, hbcast]
    rw [hcast, ← Real.exp_log (pow_pos (pow_pos hbpos M) ((K ^ 2 + 1) ^ K))]
    congr 1
    rw [Real.log_pow, Real.log_pow, hHdef]
  have hηeq : η ^ g = Real.exp ((g : ℝ) * Real.log η) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hη0 g)]
  have h7eq : (7 : ℝ) ^ g = Real.exp ((g : ℝ) * Real.log 7) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 7) g)]
  have hpre : (0 : ℝ) ≤ (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ ((K ^ 2 + 1) ^ K) * η ^ g
      * Real.exp (Lg / 2) :=
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hη0.le _))
      (Real.exp_pos _).le
  have hRHS : Real.exp (-(Real.log 8) - r * Real.log 2) = (1 / 8 : ℝ) / 2 ^ ((K ^ 2) ^ K) := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8), hrdef,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ ((K ^ 2 + 1) ^ K) * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (H + g)) ^ g
      ≤ (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ ((K ^ 2 + 1) ^ K) * η ^ g * Real.exp (Lg / 2)
          * (7 : ℝ) ^ g := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSnn hS g) hpre
    _ = Real.exp (H * ((M : ℝ) * Real.log b) + (g : ℝ) * Real.log η + Lg / 2
          + (g : ℝ) * Real.log 7) := by
        rw [hA, hηeq, h7eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(Real.log 8) - r * Real.log 2) := Real.exp_le_exp.mpr hfinal
    _ = (1 / 8 : ℝ) / 2 ^ ((K ^ 2) ^ K) := hRHS


/-- **The `hB` field of `ScheduleWitness`, discharged** for any `GridParams` with `s = K²`,
`δ₁ = 1/8` and `ε = 1/K`.  Feeding this to `gridFrame_propB_of_bound` gives `PropB (1/8)`. -/
theorem gridParams_hB {G : GridParams} {ℓ M : ℕ} {η Lg : ℝ}
    (hs : G.s = G.K ^ 2) (hℓ : 1 ≤ ℓ) (hK : 33856 * ℓ ^ 2 * 16 ^ ℓ ≤ G.K)
    (hMlo : G.K ≤ 8 * ℓ * M) (hMhi : 8 * ℓ * M ≤ G.K + 8 * ℓ)
    (hη0 : 0 < η) (hη : η ^ 4 ≤ (1 / 2 : ℝ) ^ G.K)
    (hLg : Lg ≤ (G.rDim : ℝ) * (Real.log 2 + 23 * Real.sqrt G.K)) :
    ∀ g : ℕ, (1 - 1 / (G.K : ℝ)) * (G.rDim : ℝ) ≤ (g : ℝ) → g ≤ G.rDim →
      (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt ((G.hDim : ℝ) + g)) ^ g
        ≤ (1 / 8 : ℝ) / 2 ^ G.rDim := by
  intro g hglo hghi
  have hr : G.rDim = (G.K ^ 2) ^ G.K := by rw [GridParams.rDim, hs]
  have hH : G.hDim = (G.K ^ 2 + 1) ^ G.K := by rw [GridParams.hDim, hs]
  rw [hr] at hLg hglo hghi
  rw [hr, hH]
  exact gridB_bound hℓ hK hMlo hMhi hη0 hη hLg hglo hghi


end NormalNumbers.G4
