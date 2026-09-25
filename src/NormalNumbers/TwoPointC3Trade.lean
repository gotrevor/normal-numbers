/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointC3Alt

/-!
# The price of the alternating sum, and why `b ≥ 3`

`TwoPointC3Alt.altSum_depthHead_eq_zero` (TT2025 §5.2) kills the first `K` frequencies of the tail
at the cost of `2^K` shifted copies.  Whether that is a *gain* is a quantitative question: the
surviving frequencies start at `h = K+1`, so they are damped by `b^{−K}`, and the trade is
favourable exactly when

    2^K · b^{−K}  →  0   ⟺   b ≥ 3 .

This file proves that.  For a `1`-bounded-by-`M` summand,

    ‖∑_{S ⊆ Fin K} (−1)^{|S|} ∑_{h=1}^{H} g(n + r_{S,h})·b^{−h}‖  ≤  2^{K+1}·M·b^{−(K+1)}

for every `H` (`altSum_bound`), hence `≤ M·(2/3)^K` once `b ≥ 3` (`altSum_bound_three`), which
tends to `0` in `K` for fixed `M` (`tendsto_altSum_bound_three`).

**This is the first place in the campaign where `b ≥ 3` is forced by the method rather than
assumed.**  `ConjC3` carries the hypothesis `3 ≤ b`, and TT2025 remarks of its own base-`b`
extension that *"the case `b > 2` is somewhat easier"*; both are explained by this one inequality.
For `b = 2` the trade is exactly break-even (`2^K·2^{−K} = 1`) and the method needs a different
accounting — which is precisely the paper's extra work in base 2.
-/

open Filter Topology Finset

namespace NormalNumbers.CastingOut

variable {K : ℕ}

/-! ### The head cancels for an arbitrary summand -/

/-- `altSum_depthHead_eq_zero` for an arbitrary function of the shifted argument. -/
theorem altSum_head_eq_zero (b : ℕ) (p₀ : ℤ) (v : Fin K → ℤ) (n : ℤ) (g : ℤ → ℝ) :
    ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 K, g (n + altShift p₀ v h S) / (b : ℝ) ^ h = 0 := by
  classical
  have step1 : ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 K, g (n + altShift p₀ v h S) / (b : ℝ) ^ h
      = ∑ S : Finset (Fin K), ∑ h ∈ Finset.Icc 1 K, (-1 : ℝ) ^ S.card
            * (g (n + altShift p₀ v h S) / (b : ℝ) ^ h) :=
    Finset.sum_congr rfl fun S _ => by rw [Finset.mul_sum]
  rw [step1, Finset.sum_comm]
  refine Finset.sum_eq_zero fun h hh => ?_
  rw [Finset.mem_Icc] at hh
  have hfac : ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * (g (n + altShift p₀ v h S) / (b : ℝ) ^ h)
      = (∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card * g (n + altShift p₀ v h S)) / (b : ℝ) ^ h := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun S _ => by ring
  rw [hfac, altSum_shift_eq_zero p₀ v hh.1 hh.2 n g, zero_div]

/-- Splitting the depth-`H` sum at `K`: only the frequencies above `K` survive the alternating
sum. -/
theorem altSum_eq_tailPart (b : ℕ) (p₀ : ℤ) (v : Fin K → ℤ) (n : ℤ) (g : ℤ → ℝ) {H : ℕ}
    (hHK : K ≤ H) :
    ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 H, g (n + altShift p₀ v h S) / (b : ℝ) ^ h
      = ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc (K + 1) H, g (n + altShift p₀ v h S) / (b : ℝ) ^ h := by
  classical
  have hsplit : ∀ S : Finset (Fin K),
      ∑ h ∈ Finset.Icc 1 H, g (n + altShift p₀ v h S) / (b : ℝ) ^ h
        = ∑ h ∈ Finset.Icc 1 K, g (n + altShift p₀ v h S) / (b : ℝ) ^ h
          + ∑ h ∈ Finset.Icc (K + 1) H, g (n + altShift p₀ v h S) / (b : ℝ) ^ h := by
    intro S
    have hunion : Finset.Icc 1 H = Finset.Icc 1 K ∪ Finset.Icc (K + 1) H := by
      ext h
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) H) := by
      refine Finset.disjoint_left.2 fun h h1 h2 => ?_
      rw [Finset.mem_Icc] at h1 h2
      omega
    rw [hunion, Finset.sum_union hdisj]
  rw [Finset.sum_congr rfl fun S _ => by rw [hsplit S, mul_add]]
  rw [Finset.sum_add_distrib, altSum_head_eq_zero b p₀ v n g, zero_add]

/-! ### The bound -/

/-- A finite geometric tail: `∑_{h=K+1}^{H} b^{−h} ≤ 2·b^{−(K+1)}` for `b ≥ 2`. -/
lemma sum_Icc_inv_pow_le {b : ℕ} (hb : 2 ≤ b) (K H : ℕ) :
    ∑ h ∈ Finset.Icc (K + 1) H, ((b : ℝ) ^ h)⁻¹ ≤ 2 * ((b : ℝ) ^ (K + 1))⁻¹ := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  -- reindex and compare with the full geometric series
  have hIcc : Finset.Icc (K + 1) H = Finset.Ico (K + 1) (H + 1) := by
    ext h; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hre : ∑ h ∈ Finset.Icc (K + 1) H, ((b : ℝ) ^ h)⁻¹
      = ((b : ℝ) ^ (K + 1))⁻¹ * ∑ m ∈ range (H + 1 - (K + 1)), ((b : ℝ)⁻¹) ^ m := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pow_add, mul_inv, inv_pow]
  rw [hre]
  have hgeo : ∑ m ∈ range (H + 1 - (K + 1)), ((b : ℝ)⁻¹) ^ m ≤ 2 := by
    have hinv : (b : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hb0 (by norm_num)]
      have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      linarith
    have hnn : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
    calc ∑ m ∈ range (H + 1 - (K + 1)), ((b : ℝ)⁻¹) ^ m
        ≤ ∑ m ∈ range (H + 1 - (K + 1)), ((1 : ℝ) / 2) ^ m :=
          Finset.sum_le_sum fun m _ => pow_le_pow_left₀ hnn hinv m
      _ ≤ 2 := sum_geometric_two_le _
  have hcoef : (0 : ℝ) ≤ ((b : ℝ) ^ (K + 1))⁻¹ := by positivity
  calc ((b : ℝ) ^ (K + 1))⁻¹ * ∑ m ∈ range (H + 1 - (K + 1)), ((b : ℝ)⁻¹) ^ m
      ≤ ((b : ℝ) ^ (K + 1))⁻¹ * 2 := by exact mul_le_mul_of_nonneg_left hgeo hcoef
    _ = 2 * ((b : ℝ) ^ (K + 1))⁻¹ := by ring

/-- **The price of the trade.**  `2^K` copies, each damped by `b^{−(K+1)}`. -/
theorem altSum_bound {b : ℕ} (hb : 2 ≤ b) (p₀ : ℤ) (v : Fin K → ℤ) (n : ℤ) (g : ℤ → ℝ)
    {M : ℝ} (hM : ∀ m : ℤ, ‖g m‖ ≤ M) {H : ℕ} (hHK : K ≤ H) :
    ‖∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 H, g (n + altShift p₀ v h S) / (b : ℝ) ^ h‖
      ≤ 2 ^ (K + 1) * M * ((b : ℝ) ^ (K + 1))⁻¹ := by
  classical
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  rw [altSum_eq_tailPart b p₀ v n g hHK]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ S : Finset (Fin K),
      ‖(-1 : ℝ) ^ S.card * ∑ h ∈ Finset.Icc (K + 1) H,
          g (n + altShift p₀ v h S) / (b : ℝ) ^ h‖
        ≤ M * (2 * ((b : ℝ) ^ (K + 1))⁻¹) := by
    intro S
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine (norm_sum_le _ _).trans ?_
    have hstep : ∀ h ∈ Finset.Icc (K + 1) H,
        ‖g (n + altShift p₀ v h S) / (b : ℝ) ^ h‖ ≤ M * ((b : ℝ) ^ h)⁻¹ := by
      intro h _
      have hbh : ‖((b : ℝ) ^ h)‖ = (b : ℝ) ^ h := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (b : ℝ) ^ h)]
      rw [norm_div, hbh, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Icc_inv_pow_le hb K H) hM0
  refine (Finset.sum_le_sum fun S _ => hterm S).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ : Finset (Finset (Fin K))).card : ℝ) = 2 ^ K := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    push_cast
    ring
  rw [hcard]
  have hgoal : (2 : ℝ) ^ K * (M * (2 * ((b : ℝ) ^ (K + 1))⁻¹))
      = 2 ^ (K + 1) * M * ((b : ℝ) ^ (K + 1))⁻¹ := by
    rw [pow_succ]
    ring
  linarith [hgoal.le, hgoal.ge]

/-- **`b ≥ 3` makes the trade a gain.**  The `2^K` cost is beaten by the `b^{−K}` damping. -/
theorem altSum_bound_three {b : ℕ} (hb : 3 ≤ b) (p₀ : ℤ) (v : Fin K → ℤ) (n : ℤ) (g : ℤ → ℝ)
    {M : ℝ} (hM : ∀ m : ℤ, ‖g m‖ ≤ M) {H : ℕ} (hHK : K ≤ H) :
    ‖∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 H, g (n + altShift p₀ v h S) / (b : ℝ) ^ h‖
      ≤ M * (2 / 3 : ℝ) ^ K := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hb2 : 2 ≤ b := by omega
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  refine (altSum_bound hb2 p₀ v n g hM hHK).trans ?_
  have hpow : ((b : ℝ) ^ (K + 1))⁻¹ ≤ ((3 : ℝ) ^ (K + 1))⁻¹ := by
    have h3 : (3 : ℝ) ^ (K + 1) ≤ (b : ℝ) ^ (K + 1) := by gcongr
    have hp3 : (0 : ℝ) < (3 : ℝ) ^ (K + 1) := by positivity
    have := one_div_le_one_div_of_le hp3 h3
    simpa [one_div] using this
  have hcalc : (2 : ℝ) ^ (K + 1) * M * ((3 : ℝ) ^ (K + 1))⁻¹ = M * (2 / 3 : ℝ) ^ (K + 1) := by
    rw [div_pow]
    field_simp
  have hstep : (2 : ℝ) ^ (K + 1) * M * ((b : ℝ) ^ (K + 1))⁻¹
      ≤ (2 : ℝ) ^ (K + 1) * M * ((3 : ℝ) ^ (K + 1))⁻¹ := by
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (K + 1) * M := by positivity
    exact mul_le_mul_of_nonneg_left hpow hnn
  refine hstep.trans ?_
  rw [hcalc]
  have hmono : (2 / 3 : ℝ) ^ (K + 1) ≤ (2 / 3 : ℝ) ^ K := by
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  exact mul_le_mul_of_nonneg_left hmono hM0

/-- And the bound tends to `0` in the depth. -/
theorem tendsto_altSum_bound_three (M : ℝ) :
    Tendsto (fun K : ℕ => M * (2 / 3 : ℝ) ^ K) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
  simpa using h.const_mul M

end NormalNumbers.CastingOut
