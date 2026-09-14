/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleB
import NormalNumbers.G4ScheduleAssembly
import NormalNumbers.G4EntropyE0

/-!
# Entropy expedition §4: the **E0 budget**, discharged for the implemented schedule

`G4EntropyE0.entropy_gt_of_budget` reduces E0 to one numeric inequality; this file proves that
inequality.  Its left-hand side has four terms, three of which are *already* bounded by the
disjunctivity machinery (`PropD`, the Jackson term, `Λ·smallPrimeBound`).  The one genuinely new
term is the cover term

    `2^{(1−δ/2)·m·H} · ∑_{G good} η^{|G|} · vol(pieceCube G)`,

which replaces the disjunctivity argument's `((b^ℓ−1)^M)^H · …`.

**The mechanism.**  `gridB_bound` beats the cylinder count `((b^ℓ−1)^M)^H ≈ η^{−H}` by the
*covering deficit* of an omitted word.  Here there is no omitted word: the prefactor is exactly
`(2^m)^H` with `2^{−m} ≤ η`, so per unit of `r` the prefactor contributes `+(K/4)log 2` and the
tube fraction `η^g` contributes `−(1−1/K)(K/4)log 2` — they cancel to `O(1)·log 2`, which is *not*
enough against the spectral term `11.5√K`.  The entropy deficit `δ` is what supplies the missing
room: the prefactor is only `2^{(1−δ/2)mH}`, so the cancellation leaves `−δK(log 2)/8`, and

    `δ·K·log 2 ≥ 92√K + 46`

makes it beat `11.5√K` and every absolute constant.  Since `δ ≥ 0` and `K` is free, this holds
for a **fixed** `δ` once `K ≳ (133/δ)²`; the `δ ≍ 1/√K` regime that E1 wants is the same
inequality read the other way, and is the next lap's target (it additionally needs the three
error allowances `δbig, δfar, κ, Λδ₃`, currently fixed at `1/8`, to shrink with `K`).

Main results:

* `entropy_cover_bound` — the per-good-set cover inequality, the analogue of `gridB_bound`.
* `entropy_cover_sum_le` — its sum over `goodSets`, i.e. the whole cover term is `≤ 1/8`.
-/

open Real Finset MeasureTheory
open scoped BigOperators

namespace NormalNumbers.G4

/-- `exp(1/K) ≤ 1 + 2/K` for `K ≥ 100`, in the form `H ≤ (1 + 2/K)·r`. -/
lemma hDim_le_one_add_mul_rDim {K : ℕ} {r H : ℝ} (hK : (100 : ℝ) ≤ K) (hr : 0 < r)
    (hH0 : 0 ≤ H) (hH : H ≤ Real.exp (1 / (K : ℝ)) * r) :
    H ≤ (1 + 2 / (K : ℝ)) * r := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hexp := exp_inv_mul_le hK0
  have hinv : 1 / (K : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hK
  have hinv0 : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  -- `H·(1 − 1/K) ≤ r`
  have h1 : H * (1 - 1 / (K : ℝ)) ≤ r := by
    have h2 : H * (1 - 1 / (K : ℝ)) ≤ Real.exp (1 / (K : ℝ)) * r * (1 - 1 / (K : ℝ)) :=
      mul_le_mul_of_nonneg_right hH (by linarith)
    nlinarith [hexp, hr.le]
  -- `(1 + 2/K)(1 − 1/K) ≥ 1`
  have h3 : (1 : ℝ) ≤ (1 + 2 / (K : ℝ)) * (1 - 1 / (K : ℝ)) := by
    have hsq : 2 / (K : ℝ) * (1 / (K : ℝ)) ≤ 1 / (K : ℝ) := by
      rw [div_mul_div_comm]
      rw [div_le_div_iff₀ (by positivity) hK0]
      nlinarith
    have : (1 + 2 / (K : ℝ)) * (1 - 1 / (K : ℝ))
        = 1 + (2 / (K : ℝ) - 1 / (K : ℝ)) - 2 / (K : ℝ) * (1 / (K : ℝ)) := by ring
    rw [this]
    have : 1 / (K : ℝ) ≤ 2 / (K : ℝ) - 1 / (K : ℝ) := by
      rw [div_sub_div_same]; norm_num
    linarith
  nlinarith [h1, hH0, mul_nonneg hH0 (by linarith : (0:ℝ) ≤ 1 - 1 / (K : ℝ))]

/-- **The entropy cover inequality.**  With `r = (K²)^K`, `H = (K²+1)^K`, `m ≤ K/4`,
`η ≤ 2^{−K/4}`, `Lg ≤ r(log 2 + 23√K)` and `(1−1/K)r ≤ g ≤ r`,

    `2^{(1−δ/2)·m·H} · η^g · e^{Lg/2} · (√(2πe/g)·√(H+g))^g ≤ (1/8)/2^r`

whenever the entropy deficit satisfies `92√K + 46 ≤ δ·K·log 2`.  This is `gridB_bound` with the
covering deficit of an omitted word replaced by the entropy deficit `δ`. -/
theorem entropy_cover_bound {K m g : ℕ} {η Lg δ : ℝ}
    (hK : 33856 ≤ K) (hm : (m : ℝ) ≤ (K : ℝ) / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδK : 92 * Real.sqrt K + 51 ≤ δ * K * Real.log 2)
    (hη0 : 0 < η) (hη : η ^ 4 ≤ (1 / 2 : ℝ) ^ K)
    (hLg : Lg ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
    (hglo : (1 - 1 / (K : ℝ)) * (((K ^ 2) ^ K : ℕ) : ℝ) ≤ (g : ℝ))
    (hghi : g ≤ (K ^ 2) ^ K) :
    (2 : ℝ) ^ ((1 - δ / 2) * ((m : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ))) * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g)
            * Real.sqrt ((((K ^ 2 + 1) ^ K : ℕ) : ℝ) + g)) ^ g
      ≤ (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) := by
  -- ### sizes
  have hK1 : 1 ≤ K := by omega
  have hK100 : (100 : ℝ) ≤ (K : ℝ) := by
    have : (33856 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
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
  have hHb : H ≤ (1 + 2 / (K : ℝ)) * r := hDim_le_one_add_mul_rDim hK100 hr0 hH0 hHr
  have hgr : (g : ℝ) ≤ r := by rw [hrdef]; exact_mod_cast hghi
  have hgnn : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hinv0 : 1 / (K : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hK100
  have hinvpos : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  have hgpos : (0 : ℝ) < (g : ℝ) := by
    have h : (0 : ℝ) < (1 - 1 / (K : ℝ)) * r := mul_pos (by linarith) hr0
    linarith
  -- ### `√K`
  have hS0 : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hSsq : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt (by positivity)
  have hS184 : (184 : ℝ) ≤ Real.sqrt K := by
    have h : Real.sqrt (33856 : ℝ) ≤ Real.sqrt K :=
      Real.sqrt_le_sqrt (by exact_mod_cast hK)
    have : Real.sqrt (33856 : ℝ) = 184 := by
      rw [show (33856 : ℝ) = 184 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [this ▸ h]
  -- ### the four terms of the exponent
  have hlogη : Real.log η ≤ -((K : ℝ) / 4) * Real.log 2 := by
    have hlp : Real.log (η ^ 4) ≤ Real.log ((1 / 2 : ℝ) ^ K) :=
      Real.log_le_log (pow_pos hη0 4) hη
    rw [Real.log_pow, Real.log_pow] at hlp
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hhalf] at hlp
    push_cast at hlp
    linarith
  have hL0neg : -((K : ℝ) / 4) * Real.log 2 ≤ 0 := by
    have h : (0 : ℝ) ≤ (K : ℝ) / 4 * Real.log 2 :=
      mul_nonneg (by linarith) hlog2pos.le
    linarith [h, (by ring : -((K : ℝ) / 4) * Real.log 2 = -((K : ℝ) / 4 * Real.log 2))]
  -- T1
  have hT1 : (1 - δ / 2) * ((m : ℝ) * H) * Real.log 2
      ≤ r * Real.log 2 * ((K : ℝ) / 4 - δ * K / 8 + 1 / 2) := by
    have hmH : (m : ℝ) * H ≤ ((K : ℝ) / 4) * ((1 + 2 / (K : ℝ)) * r) := by
      refine mul_le_mul hm hHb hH0 (by positivity)
    have hid : ((K : ℝ) / 4) * ((1 + 2 / (K : ℝ)) * r) = r * ((K : ℝ) / 4 + 1 / 2) := by
      field_simp; ring
    rw [hid] at hmH
    have hc0 : (0 : ℝ) ≤ 1 - δ / 2 := by linarith
    have h1 : (1 - δ / 2) * ((m : ℝ) * H) * Real.log 2
        ≤ (1 - δ / 2) * (r * ((K : ℝ) / 4 + 1 / 2)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmH hc0) hlog2pos.le
    have hgap : (1 - δ / 2) * ((K : ℝ) / 4 + 1 / 2)
        ≤ (K : ℝ) / 4 - δ * K / 8 + 1 / 2 := by
      have he : (1 - δ / 2) * ((K : ℝ) / 4 + 1 / 2)
          = (K : ℝ) / 4 - δ * K / 8 + 1 / 2 - δ / 4 := by ring
      linarith
    have h2 : (1 - δ / 2) * (r * ((K : ℝ) / 4 + 1 / 2)) * Real.log 2
        ≤ r * Real.log 2 * ((K : ℝ) / 4 - δ * K / 8 + 1 / 2) := by
      have he : (1 - δ / 2) * (r * ((K : ℝ) / 4 + 1 / 2)) * Real.log 2
          = r * Real.log 2 * ((1 - δ / 2) * ((K : ℝ) / 4 + 1 / 2)) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hgap (mul_pos hr0 hlog2pos).le
    linarith
  -- T2
  have hT2 : (g : ℝ) * Real.log η ≤ r * Real.log 2 * (-((K : ℝ) / 4) + 1 / 4) := by
    have e1 : (g : ℝ) * Real.log η ≤ (g : ℝ) * (-((K : ℝ) / 4) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogη hgnn
    have e2 : (g : ℝ) * (-((K : ℝ) / 4) * Real.log 2)
        ≤ ((1 - 1 / (K : ℝ)) * r) * (-((K : ℝ) / 4) * Real.log 2) :=
      mul_le_mul_of_nonpos_right hglo hL0neg
    have e3 : ((1 - 1 / (K : ℝ)) * r) * (-((K : ℝ) / 4) * Real.log 2)
        = r * Real.log 2 * (-((K : ℝ) / 4) + 1 / 4) := by
      field_simp; ring
    linarith
  -- T3, T4
  have hT3 : Lg / 2 ≤ r * ((Real.log 2 + 23 * Real.sqrt K) / 2) := by
    linarith
  have hlog7 : Real.log 7 ≤ 2 := log_seven_le_two
  have hT4 : (g : ℝ) * Real.log 7 ≤ r * 2 := by
    have h := mul_le_mul_of_nonneg_left hlog7 hgnn
    linarith
  have hlog8r : Real.log 8 ≤ r * (3 * Real.log 2) := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have h : 1 * (3 * Real.log 2) ≤ r * (3 * Real.log 2) :=
      mul_le_mul_of_nonneg_right hr1 (by linarith)
    rw [h8]; linarith
  -- ### the bracket is `≤ −4 log 2`
  have hbracket : Real.log 2 * ((K : ℝ) / 4 - δ * K / 8 + 1 / 2)
      + Real.log 2 * (-((K : ℝ) / 4) + 1 / 4)
      + (Real.log 2 + 23 * Real.sqrt K) / 2 + 2 ≤ -(5 * Real.log 2) := by
    have hδ8 : 11.5 * Real.sqrt K + 6.375 ≤ δ * K * Real.log 2 / 8 := by linarith
    have hsimp : Real.log 2 * ((K : ℝ) / 4 - δ * K / 8 + 1 / 2)
        + Real.log 2 * (-((K : ℝ) / 4) + 1 / 4)
        = -(δ * K * Real.log 2 / 8) + (3 / 4) * Real.log 2 := by ring
    rw [hsimp]
    linarith
  -- ### the exponent
  have hfinal : (1 - δ / 2) * ((m : ℝ) * H) * Real.log 2 + (g : ℝ) * Real.log η + Lg / 2
      + (g : ℝ) * Real.log 7 ≤ -(Real.log 8) - ((K : ℝ) + r) * Real.log 2 := by
    set BR : ℝ := Real.log 2 * ((K : ℝ) / 4 - δ * K / 8 + 1 / 2)
      + Real.log 2 * (-((K : ℝ) / 4) + 1 / 4)
      + (Real.log 2 + 23 * Real.sqrt K) / 2 + 2 with hBRdef
    have hKr : (K : ℝ) ≤ r := by
      rw [hrdef]
      have : K ≤ (K ^ 2) ^ K := by
        calc K = K ^ 1 := (pow_one K).symm
          _ ≤ (K ^ 2) ^ 1 := Nat.pow_le_pow_left (Nat.le_self_pow (by norm_num) K) 1
          _ ≤ (K ^ 2) ^ K := Nat.pow_le_pow_right (by positivity) hK1
      exact_mod_cast this
    have hexpand : r * Real.log 2 * ((K : ℝ) / 4 - δ * K / 8 + 1 / 2)
        + r * Real.log 2 * (-((K : ℝ) / 4) + 1 / 4)
        + r * ((Real.log 2 + 23 * Real.sqrt K) / 2) + r * 2 = r * BR := by
      rw [hBRdef]; ring
    have hrBR : r * BR ≤ r * (-(5 * Real.log 2)) :=
      mul_le_mul_of_nonneg_left hbracket hr0.le
    have hKlog : (K : ℝ) * Real.log 2 ≤ r * Real.log 2 :=
      mul_le_mul_of_nonneg_right hKr hlog2pos.le
    have hle : r * (-(5 * Real.log 2))
        = -(r * (3 * Real.log 2)) - r * Real.log 2 - r * Real.log 2 := by ring
    have hgoal : -(Real.log 8) - ((K : ℝ) + r) * Real.log 2
        = -(Real.log 8) - (K : ℝ) * Real.log 2 - r * Real.log 2 := by ring
    rw [hgoal]
    linarith [hT1, hT2, hT3, hT4, hlog8r]
  -- ### assemble
  have hSnn : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (H + g) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSh : Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (H + g) ≤ 7 :=
    shape_factor_le hK100 hr0 hH0 hHr hglo
  have hA : (2 : ℝ) ^ ((1 - δ / 2) * ((m : ℝ) * H))
      = Real.exp ((1 - δ / 2) * ((m : ℝ) * H) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    ring_nf
  have hηeq : η ^ g = Real.exp ((g : ℝ) * Real.log η) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hη0 g)]
  have h7eq : (7 : ℝ) ^ g = Real.exp ((g : ℝ) * Real.log 7) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 7) g)]
  have hpre : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 - δ / 2) * ((m : ℝ) * H)) * η ^ g * Real.exp (Lg / 2) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (pow_nonneg hη0.le _))
      (Real.exp_pos _).le
  have hRHS : Real.exp (-(Real.log 8) - ((K : ℝ) + r) * Real.log 2)
      = (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) := by
    have hc : ((K : ℝ) + r) = ((K + (K ^ 2) ^ K : ℕ) : ℝ) := by rw [hrdef]; push_cast; ring
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8), hc,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc (2 : ℝ) ^ ((1 - δ / 2) * ((m : ℝ) * H)) * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (H + g)) ^ g
      ≤ (2 : ℝ) ^ ((1 - δ / 2) * ((m : ℝ) * H)) * η ^ g * Real.exp (Lg / 2)
          * (7 : ℝ) ^ g := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSnn hSh g) hpre
    _ = Real.exp ((1 - δ / 2) * ((m : ℝ) * H) * Real.log 2 + (g : ℝ) * Real.log η + Lg / 2
          + (g : ℝ) * Real.log 7) := by
        rw [hA, hηeq, h7eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(Real.log 8) - ((K : ℝ) + r) * Real.log 2) := Real.exp_le_exp.mpr hfinal
    _ = (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) := hRHS

/-- **The cover term, summed over good coordinate sets.**  A general prefactor `Pf ≥ 0` in place
of the disjunctivity argument's cylinder count: if `Pf·η^g·e^{Lg/2}·(shape)^g ≤ δ₁/2^r` for every
admissible `g`, then `Pf · ∑_{G good} η^{|G|} vol(pieceCube G) ≤ δ₁`.  (The `2^r` divisor pays for
the union over the at most `2^r` good sets, `card_goodSets_le`.) -/
theorem entropy_cover_sum_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) (hε1 : ε < 1) (hr : 1 ≤ G.rDim)
    {Lg : ℝ} (hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg)
    {Pf δ₁ : ℝ} (hPf : 0 ≤ Pf) (hδ : 0 ≤ δ₁)
    (hbound : ∀ g : ℕ, (1 - ε) * (G.rDim : ℝ) ≤ (g : ℝ) → g ≤ G.rDim →
      Pf * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt ((G.hDim : ℝ) + g)) ^ g
        ≤ δ₁ / 2 ^ G.rDim) :
    Pf * ∑ Gs ∈ (gridFrame bb hbb G X hne sm γ hη hε D).goodSets,
        η ^ Gs.card * (volume ((gridFrame bb hbb G X hne sm γ hη hε D).pieceCube Gs)).toReal
      ≤ δ₁ := by
  classical
  set fr := gridFrame bb hbb G X hne sm γ hη hε D with hfr
  have hterm : ∀ Gs ∈ fr.goodSets,
      Pf * (η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal) ≤ δ₁ / 2 ^ G.rDim := by
    intro Gs hGs
    unfold Frame.goodSets at hGs
    rw [Finset.mem_filter] at hGs
    have hge : (1 - ε) * (G.rDim : ℝ) ≤ (Gs.card : ℝ) := hGs.2
    have hle : Gs.card ≤ G.rDim := by
      have := Finset.card_le_card (Finset.mem_powerset.1 hGs.1)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have hpos : 0 < Gs.card := by
      have hr' : (1 : ℝ) ≤ (G.rDim : ℝ) := by exact_mod_cast hr
      have h0 : (0 : ℝ) < (1 - ε) * (G.rDim : ℝ) := mul_pos (by linarith) (by linarith)
      exact_mod_cast (lt_of_lt_of_le h0 hge)
    have hpc := gridFrame_volume_pieceCube_le bb hbb G X hne sm γ hη hε D Gs hpos hlog
    refine le_trans ?_ (hbound Gs.card hge hle)
    have hη' : (0 : ℝ) ≤ η ^ Gs.card := pow_nonneg hη.le _
    calc Pf * (η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal)
        ≤ Pf * (η ^ Gs.card * (Real.exp (Lg / 2)
            * (Real.sqrt (2 * Real.pi * Real.exp 1 / Gs.card)
                * Real.sqrt ((G.hDim : ℝ) + Gs.card)) ^ Gs.card)) := by
          gcongr
      _ = _ := by ring
  calc Pf * ∑ Gs ∈ fr.goodSets, η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal
      = ∑ Gs ∈ fr.goodSets, Pf * (η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _Gs ∈ fr.goodSets, δ₁ / 2 ^ G.rDim := Finset.sum_le_sum hterm
    _ = (fr.goodSets.card : ℝ) * (δ₁ / 2 ^ G.rDim) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ G.rDim : ℝ) * (δ₁ / 2 ^ G.rDim) := by
        have hc : ((fr.goodSets.card : ℕ) : ℝ) ≤ 2 ^ G.rDim := by
          exact_mod_cast card_goodSets_le fr
        have hδnn : (0 : ℝ) ≤ δ₁ / 2 ^ G.rDim := by positivity
        exact mul_le_mul_of_nonneg_right hc hδnn
    _ = δ₁ := by field_simp

/-! ### E0 for the implemented base-four schedule -/

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- `b₀ < X`: the sample `P_K` is nonempty at the schedule's outer scale. -/
lemma b₀_lt_X {K : ℕ} (hK : 100 ≤ K) : (gridOf K (N K) (by omega)).b₀ < X K := by
  have h1 := (gridOf K (N K) (by omega : 1 ≤ K)).b₀_lt_P₀
  have h2 := two_mul_P₀_le_X hK
  omega

/-- The five `smallPrimeBound` terms bounded individually, rather than only in the sum
`< 1` that `budget_assembly` needs.  The entropy budget must beat `δ/(2−δ)`, not `1`. -/
lemma budget_terms_le {Λ Λ' t0 ta tb tc td : ℝ} (hΛ : Λ ≤ Λ') (hΛ0 : 0 ≤ Λ)
    (h0' : 0 ≤ t0) (ha' : 0 ≤ ta) (hb' : 0 ≤ tb) (hc' : 0 ≤ tc) (hd' : 0 ≤ td)
    (h0 : Λ' * t0 ≤ Real.exp (-4)) (ha : Λ' * ta ≤ 1 / 64) (hb : Λ' * tb ≤ Real.exp (-4))
    (hc : Λ' * tc ≤ Real.exp (-4)) (hd : Λ' * td ≤ 1 / 64) :
    Λ * (t0 + (ta + tb + tc + td)) ≤ 3 * Real.exp (-4) + 1 / 32 := by
  have hsum : Λ * (t0 + (ta + tb + tc + td))
      ≤ Λ' * t0 + Λ' * ta + Λ' * tb + Λ' * tc + Λ' * td := by
    have he : Λ * (t0 + (ta + tb + tc + td))
        = Λ * t0 + Λ * ta + Λ * tb + Λ * tc + Λ * td := by ring
    rw [he]; gcongr
  linarith

/-- **`Λ·δ₃ ≤ 3e^{−4} + 1/32 < 0.107`.** -/
lemma smallPrime_term_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
          (T K) (R K) (Mc K)
          (apSample (X K) (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ 3 * Real.exp (-4) + 1 / 32 := by
  have hk : 25 ≤ k₄ := by omega
  unfold smallPrimeBound
  exact budget_terms_le (Lambda_le hK4 hk) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (main_term_le hK) (term_a_le hK)
    (term_b_le hK) (term_c_le hK) (term_d_le hK)

/-- **E0 for the implemented base-four schedule, unconditionally.**  For every `K = 4k₄` with
`K ≥ 33856`, the joint quantized sample of `G₄ = ∑_p 1/(4^p−1)` at scale `K`, read as `k₄`-bit
binary windows at the base-four orbit positions, carries at least a *fifth* of the maximal
entropy `m_K·H_K`:

    `(1/5)·k₄·(K²+1)^K  <  H₂(Z^{G4}_K)`.

The four terms of the budget: the cover term is `≤ 1/8` (`entropy_cover_bound`), `δ₂ = 1/4`
(`hbig_holds`, `hfar_holds`), the Jackson term is `≤ 1/8` (`jackson_term_le`) and
`Λδ₃ ≤ 3e^{−4}+1/32` (`smallPrime_term_le`); their sum is `< 0.607 < 2/3 = δ/(2−δ)` at
`δ = 4/5`.  The allowances `δbig, δfar, κ` are the disjunctivity argument's fixed `1/8`s, which
is why `δ` cannot yet be taken small; driving `δ ↓ C/√K` (which `entropy_cover_bound` already
permits) is what E1 needs. -/
theorem entropy_E0 {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 33856 ≤ K) :
    (1 / 5 : ℝ) * ((k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ))
      < (NormalNumbers.G4Entropy.jointLaw (gridOf K (N K) (by omega))
          (b₀_lt_X (show 100 ≤ K by omega)) k₄ (primeLambertAtBase 4)).H₂ := by
  have hK100 : 100 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK100
  set G := gridOf K (N K) hK1 with hGdef
  set hX := b₀_lt_X (show 100 ≤ K by omega) with hXdef
  set η : ℝ := (1 / 2 : ℝ) ^ k₄ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; positivity
  set ε : ℝ := 1 / (K : ℝ) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; positivity
  set hne := NormalNumbers.G4Entropy.apSample_nonempty G hX with hnedef
  set fr := gridFrame 4 (by norm_num) G (X K) hne (smallPrimes (R K) G.P₀)
    (frozenGamma 4 G) hη hε (Dj K k₄) with hfrdef
  -- real lifts of `θ` and `γ`
  choose θr hθr using fun ν => QuotientAddGroup.mk_surjective (fr.θ ν)
  choose γr hγr using fun ν => QuotientAddGroup.mk_surjective (fr.γ ν)
  set M : ℝ := (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ) with hMdef
  have hMpos : (0 : ℝ) < M := by
    rw [hMdef]
    have : (0 : ℝ) < (k₄ : ℝ) := by exact_mod_cast (show 0 < k₄ by omega)
    have h2 : (0 : ℝ) < (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
      have : 0 < (K ^ 2 + 1) ^ K := Nat.pow_pos (by positivity)
      exact_mod_cast this
    positivity
  -- ### the four terms
  -- (1) the cover term
  have hcover : (2 : ℝ) ^ ((1 - (4 / 5 : ℝ) / 2) * M)
      * (∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal)
      ≤ (1 / 8 : ℝ) / 2 ^ K := by
    refine entropy_cover_sum_le 4 (by norm_num) G (X K) hne _ _ hη hε (Dj K k₄)
      (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
      (by rw [hεdef, div_lt_one (by linarith)]; linarith)
      (Nat.one_le_pow _ _ (show 0 < K ^ 2 by positivity)) ?_ (by positivity) (by positivity) ?_
    · have h := log_det_one_add_tensorGram_le' (K := K) hK1
      show Real.log (1 + tensorGram G.K G.s).det
        ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
      push_cast
      exact h
    · intro g hglo hghi
      have := entropy_cover_bound (K := K) (m := k₄) (g := g) (η := η)
        (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)) (δ := 4 / 5)
        hK ?_ (by norm_num) (by norm_num) ?_ hη ?_ le_rfl ?_ ?_
      · refine this.trans_eq ?_
        show (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) = (1 / 8 : ℝ) / 2 ^ K / 2 ^ G.rDim
        rw [show G.rDim = (K ^ 2) ^ K from rfl, pow_add]
        field_simp
      · rw [hK4]; push_cast; ring_nf; rfl
      · -- `92√K + 46 ≤ (4/5)·K·log 2`
        have hs : (184 : ℝ) * Real.sqrt K ≤ (K : ℝ) := by
          have h1 : (184 : ℝ) ≤ Real.sqrt K := by
            have h : Real.sqrt (33856 : ℝ) ≤ Real.sqrt K :=
              Real.sqrt_le_sqrt (by exact_mod_cast hK)
            have he : Real.sqrt (33856 : ℝ) = 184 := by
              rw [show (33856 : ℝ) = 184 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            linarith [he ▸ h]
          have h2 : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt (by positivity)
          nlinarith [Real.sqrt_nonneg (K : ℝ)]
        have hKb : (33856 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
        have hl2 : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        nlinarith [hs, hKb, hl2]
      · rw [hηdef, ← pow_mul, hK4, mul_comm]
      · exact hglo
      · exact hghi
  -- (2) the Jackson term
  have hjack : 2 * (1 / (fr.res * Real.sqrt ((Dj K k₄ : ℕ) + 1))) ≤ 1 / 8 := by
    have h := Sched.jackson_term_le (K := K) (k₄ := k₄) hK1
    have hres : fr.res = (1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄ := by
      rw [hfrdef]; rfl
    rw [hres]
    exact h
  -- (3) `PropD`
  have hD : fr.PropD ((1 / 8 : ℝ) + (1 / 8 : ℝ)) := by
    refine gridFrame_propD_of_bounds 4 (by norm_num) G (X K) (R K) (Y K) hne
      (show 0 < K from hK1) (R_ge_two K) (R_le_Y K)
      (Mx := ((X K + J K * gridDm K (N K) : ℕ) : ℝ)) ?_ ?_
      (Dm := gridDm K (N K)) (gridOf.d_le hK1) hη hε (Dj K k₄) ?_ ?_
    · have : 1 ≤ X K := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    · exact fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    · have h := hbig_holds hK4 hK100
      simp only [Nat.cast_ofNat, rowL1_four, rowL2_four, hεdef, hηdef,
        show G.K = K from rfl, show G.P₀ = (gridOf K (N K) hK1).P₀ from rfl,
        show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      ring_nf
      ring_nf at h
      linarith
    · have h := hfar_holds hK100
      simp only [Nat.cast_ofNat, farBound_four, hεdef, hηdef,
        show G.K = K from rfl, show G.N = N K from rfl,
        show G.P₀ = (gridOf K (N K) hK1).P₀ from rfl,
        show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      have hkK : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ k₄ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hKpos : (0 : ℝ) < K := by linarith
      calc _ ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := h
        _ ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by gcongr
  -- (4) `PropC` and the small-prime term
  set δ₃ : ℝ := smallPrimeBound (smallPrimes (R K) G.P₀) (Fintype.card G.Idx) (R K) (Mc K)
    (apSample (X K) G.P₀ G.b₀).card (Real.exp 1) (13 / 2)
    (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K) with hδ₃def
  have hC : fr.PropC δ₃ :=
    gridFrame_propC_four G (X K) hne _ _ hη hε (R := R K)
      (fun p hp => (mem_smallPrimes.1 hp).1) (fun p hp => (mem_smallPrimes.1 hp).2.2)
      (by have := R_ge_two K; omega) (fun p hp => (mem_smallPrimes.1 hp).2.1)
      (by
        show 1 + Nat.clog 4 (2 ^ K * Dj K k₄) ≤ N K
        have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 (two_pow_mul_Dj_le hK4 hK100)
        have hN : 1 ≤ N K := N_pos hK1
        omega)
      (Mc_pos hK1) (Real.one_le_exp zero_le_one) (by norm_num)
  have hδ₃nn : (0 : ℝ) ≤ δ₃ :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hsmall : (((2 * Dj K k₄ + 1) ^ G.rDim : ℕ) : ℝ) * δ₃ ≤ 3 * Real.exp (-4) + 1 / 32 := by
    have h := smallPrime_term_le hK4 hK100
    have hcard : Fintype.card G.Idx = T K := gridOf.card_Idx hK1
    rw [hδ₃def, hcard]
    exact h
  -- ### E0
  have hmη : ((2 : ℝ)⁻¹) ^ k₄ ≤ η := by rw [hηdef]; norm_num
  have hmain := NormalNumbers.G4Entropy.entropy_gt_of_budget G (X K) hX (by norm_num)
    (smallPrimes (R K) G.P₀) (frozenGamma 4 G) hη hε (Dj K k₄) k₄ θr γr hθr hγr hmη
    (δ := 4 / 5) (M := M) (by norm_num) (by norm_num) hMpos hD hC hδ₃nn ?_
  · have he : (1 : ℝ) - 4 / 5 = 1 / 5 := by norm_num
    rw [he] at hmain
    exact hmain
  · have he4 := Sched.exp_neg_four_le
    have hR : (4 / 5 : ℝ) / (2 - 4 / 5) = 2 / 3 := by norm_num
    have hc8 : (1 / 8 : ℝ) / 2 ^ K ≤ 1 / 8 := by
      have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [hR]
    linarith [hcover, hjack, hsmall]

end Sched

end NormalNumbers.G4
