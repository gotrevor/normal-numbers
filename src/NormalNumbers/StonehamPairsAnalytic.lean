/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsNormal

/-!
# The analytic Stoneham engine with power denominator growth

The arithmetic of Stoneham families with overlapping prime support need not make the reduced
orbit-state denominator grow linearly.  The Bailey--Borwein pair argument only needs a positive
power lower bound.  This file isolates that weaker interface without changing Theorem A or its
linear-lower-bound specialization in `StonehamSumsNormal`.
-/

namespace NormalNumbers.StonehamSumsNormal

open Literature.VandeheyDiff NormalNumbers.G4
open Finset Filter Topology

/-- The reduced Stoneham-state denominator grows at least like a positive power of time, up to
an arbitrary fixed real constant.  Positivity of `ρ` and `C` is imposed by consumers, so the
definition remains a clean arithmetic interface. -/
def StonehamStateDenPowerLower (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (ρ C : ℝ) : Prop :=
  ∀ n : ℕ, (n : ℝ) ^ ρ ≤ C * (stonehamState b L c m p n).den

/-- A linear lower bound supplies the power interface at exponent one. -/
lemma stonehamState_den_powerLower_one_of_linearLower
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (hlower : StonehamStateDenLinearLower b L c m p) :
    StonehamStateDenPowerLower b L c m p 1 (stonehamCoeffBound c m p) := by
  intro n
  rw [Real.rpow_one]
  exact_mod_cast (by simpa [mul_comm] using hlower n)

/-- On a square block, a power lower bound gives the denominator lower estimate needed by
Vandehey's complete-sum bound.  The polynomial upper estimate is unchanged. -/
lemma stonehamState_block_den_bounds_of_powerLower
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ)
    (p : Fin r → ℤ) (ρ C : ℝ) (J j : ℕ)
    (hρ : 0 < ρ) (hJ : 1 ≤ J) (hj1 : 1 ≤ j) (hj : j < J)
    (hL : L ≠ 0) (hc : ∀ i, 2 ≤ c i)
    (hlower : StonehamStateDenPowerLower b L c m p ρ C) :
    (J : ℝ) ^ ρ ≤ C * (stonehamState b L c m p (j * J)).den ∧
      (stonehamState b L c m p (j * J)).den ≤ L * (J ^ 2) ^ r := by
  have hs0 : j * J ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hsN : j * J ≤ J ^ 2 := by nlinarith
  constructor
  · calc
      (J : ℝ) ^ ρ ≤ ((j * J : ℕ) : ℝ) ^ ρ := by
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast (by nlinarith : J ≤ j * J)
        · exact hρ.le
      _ ≤ C * (stonehamState b L c m p (j * J)).den := hlower (j * J)
  · have hc0 : ∀ i, c i ≠ 0 := fun i => by have := hc i; omega
    have hdenDvd := stonehamState_den_dvd b L c m p (j * J) hL hc0
    have hstateDen0 : stonehamStateDen L c m (j * J) ≠ 0 := by
      unfold stonehamStateDen
      exact mul_ne_zero hL (prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hc0 i))
    have hdenle : (stonehamState b L c m p (j * J)).den ≤
        stonehamStateDen L c m (j * J) :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hstateDen0) hdenDvd
    exact hdenle.trans ((stonehamStateDen_le L c m (j * J) hs0).trans (by
      gcongr))

/-- The denominator decay furnished by a power lower bound.  This is the only changed
inequality in the block proof: `J⁻δ` becomes `J⁻(ρδ)`. -/
lemma stoneham_den_neg_rpow_le_of_powerLower
    {J D : ℕ} {ρ C δ : ℝ} (hJ : 1 ≤ J) (hD : 1 ≤ D)
    (hρ : 0 < ρ) (hC : 0 < C) (hδ : 0 < δ)
    (hlower : (J : ℝ) ^ ρ ≤ C * D) :
    (D : ℝ) ^ (-δ) ≤ (((J : ℝ) ^ ρ) / C) ^ (-δ) := by
  have hCR : (0 : ℝ) < C := hC
  have hbase : ((J : ℝ) ^ ρ) / C ≤ D := by
    rw [div_le_iff₀ hCR]
    simpa [mul_comm] using hlower
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)

/-- Vandehey's square-block estimate needs only positive power denominator growth. -/
lemma stonehamState_square_bound_of_powerLower
    (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (ρ C₀ : ℝ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b)
    (hp : ∀ i, p i ≠ 0) (hρ : 0 < ρ) (hC₀ : 0 < C₀)
    (hlower : StonehamStateDenPowerLower b L c m p ρ C₀)
    {δ C : ℝ} (hδ : 0 < δ)
    (hcor : ∀ (M : ℕ), 2 ≤ M →
      (∀ q, q.Prime → q ∣ M → q ∈ stonehamPrimes L c) →
      ∀ (a : ℤ), IsCoprime a (M : ℤ) → ∀ N : ℕ,
        (M : ℝ) ^ (1 / (2 * r + 1 : ℝ)) ≤ N →
        ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / M)‖ ≤
          C * (M : ℝ) ^ (-δ) * N * (1 + Real.log M))
    (J : ℕ) (hJ : 1 ≤ J) (hC₀J : C₀ < (J : ℝ) ^ ρ) (hLJ : L ≤ J) :
    ‖∑ n ∈ Icc 1 (J ^ 2),
        ePhase ((stonehamState b L c m p n : ℚ) : ℝ)‖ ≤
      (1 + r * Nat.log 2 (J ^ 2)) * J +
        |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) * J ^ 2 *
          (1 + Real.log (L * (J ^ 2) ^ r)) := by
  let U := L * (J ^ 2) ^ r
  let B : ℝ := |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) * J * (1 + Real.log U)
  have hU1 : 1 ≤ U := by
    dsimp [U]
    have hJpow : 1 ≤ (J ^ 2) ^ r := one_le_pow₀ (one_le_pow₀ hJ)
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hL) (Nat.one_le_iff_ne_zero.mp hJpow))
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let f : ℕ → ℂ := fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)
  have hf1 : ∀ n, ‖f n‖ = 1 := fun n => norm_ePhase _
  have hblock : ∀ j ∈ range J,
      ‖∑ t ∈ Icc 1 J, f (j * J + t)‖ ≤
        (if j ∈ stonehamKickBlocks c m J then (J : ℝ) else 0) + B := by
    intro j hj
    rw [mem_range] at hj
    by_cases hbad : j ∈ stonehamKickBlocks c m J
    · rw [if_pos hbad]
      have htriv : ‖∑ t ∈ Icc 1 J, f (j * J + t)‖ ≤ J := by
        refine (norm_sum_le _ _).trans ?_
        simp [hf1, Nat.card_Icc]
      linarith
    · rw [if_neg hbad, zero_add]
      have hj1 : 1 ≤ j := by
        by_contra hj0
        have : j = 0 := by omega
        subst j
        exact hbad (by simp [stonehamKickBlocks])
      obtain ⟨hlow, hupper⟩ := stonehamState_block_den_bounds_of_powerLower
        b L c m p ρ C₀ J j hρ hJ hj1 hj (by omega) hc hlower
      let D := (stonehamState b L c m p (j * J)).den
      have hden2 : 2 ≤ D := by
        by_contra hd
        have hDone : D = 1 := by have := Rat.den_pos (stonehamState b L c m p (j * J)); omega
        rw [show (stonehamState b L c m p (j * J)).den = D by rfl, hDone,
          Nat.cast_one, mul_one] at hlow
        exact (not_lt_of_ge hlow) hC₀J
      have hlen := stonehamState_block_length b L c m p J j hJ hLJ hupper
      have hraw := stonehamState_good_block_bound b L c m p hb hL hLb hc hm hcb hcor
        J j hJ hj hbad (by simpa only [D] using hden2) hlen
      have hpow : (D : ℝ) ^ (-δ) ≤ (((J : ℝ) ^ ρ) / C₀) ^ (-δ) :=
        stoneham_den_neg_rpow_le_of_powerLower hJ (by omega) hρ hC₀ hδ
          (by simpa only [D] using hlow)
      have hDU : D ≤ U := by simpa only [D, U] using hupper
      have hlog : Real.log D ≤ Real.log U :=
        Real.log_le_log (by positivity) (by exact_mod_cast hDU)
      have hlogD0 : 0 ≤ 1 + Real.log D := by
        have : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
        linarith [Real.log_nonneg this]
      have hlogU0 : 0 ≤ 1 + Real.log U := by
        have : (1 : ℝ) ≤ U := by exact_mod_cast hU1
        linarith [Real.log_nonneg this]
      have hC0 : 0 ≤ C := by
        have hpos : 0 < (D : ℝ) ^ (-δ) * J * (1 + Real.log D) := by positivity
        nlinarith [norm_nonneg (∑ t ∈ Icc 1 J, f (j * J + t))]
      calc
        ‖∑ t ∈ Icc 1 J, f (j * J + t)‖
            ≤ C * (D : ℝ) ^ (-δ) * J * (1 + Real.log D) := by
              simpa only [f, D] using hraw
        _ ≤ |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) * J * (1 + Real.log U) := by
          gcongr
          exact le_abs_self C
        _ = B := by rfl
  rw [show J ^ 2 = J * J by ring, sum_Icc_mul_blocks]
  refine (norm_sum_le _ _).trans ((sum_le_sum hblock).trans ?_)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hbadcard : ((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card ≤
      1 + r * Nat.log 2 (J ^ 2) := by
    have hsub : ((range J).filter fun j => j ∈ stonehamKickBlocks c m J) ⊆
        stonehamKickBlocks c m J := by
      intro j hj
      exact (mem_filter.mp hj).2
    exact (card_le_card hsub).trans (stonehamKickBlocks_card c m J)
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  have hfin :
      (((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card : ℝ) * J +
          (J : ℝ) * B ≤
        (1 + r * Nat.log 2 (J ^ 2)) * J +
          |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) * J ^ 2 *
            (1 + Real.log (L * (J ^ 2) ^ r)) := by
    calc
      (((range J).filter fun j => j ∈ stonehamKickBlocks c m J).card : ℝ) * J +
            (J : ℝ) * B
          ≤ (1 + r * Nat.log 2 (J ^ 2) : ℕ) * J + (J : ℝ) * B := by
            gcongr
      _ = (1 + r * Nat.log 2 (J ^ 2)) * J +
          |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) * J ^ 2 *
            (1 + Real.log (L * (J ^ 2) ^ r)) := by
        dsimp only [B, U]
        push_cast
        ring
  simpa [pow_two] using hfin

lemma tendsto_stoneham_power_analytic_rate (r L : ℕ) (C₀ C ρ δ : ℝ)
    (hL : 1 ≤ L) (hC₀ : 0 < C₀) (hρ : 0 < ρ) (hδ : 0 < δ) :
    Tendsto (fun J : ℕ =>
      |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) *
        (1 + Real.log (L * (J ^ 2) ^ r))) atTop (𝓝 0) := by
  have hρδ : 0 < ρ * δ := mul_pos hρ hδ
  have hpow : Tendsto (fun J : ℕ => (J : ℝ) ^ (-(ρ * δ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hρδ).comp tendsto_natCast_atTop_atTop
  have hlogpow : Tendsto (fun J : ℕ => Real.log J / (J : ℝ) ^ (ρ * δ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hρδ).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  let K : ℝ := |C| / C₀ ^ (-δ)
  have hmodel : Tendsto (fun J : ℕ => K *
      ((1 + Real.log L) * (J : ℝ) ^ (-(ρ * δ)) +
        (2 * r : ℝ) * (Real.log J / (J : ℝ) ^ (ρ * δ)))) atTop (𝓝 0) := by
    have h1 := hpow.const_mul (1 + Real.log L)
    have h2 := hlogpow.const_mul (2 * r : ℝ)
    simpa using (h1.add h2).const_mul K
  apply hmodel.congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  have hJR : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hLR : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hlogeq : Real.log ((L : ℝ) * ((J : ℝ) ^ 2) ^ r) =
      Real.log L + 2 * r * Real.log J := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [hlogeq, Real.div_rpow (Real.rpow_nonneg _ _) hC₀.le,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ J)]
  have hJpow0 : (J : ℝ) ^ (ρ * δ) ≠ 0 := (Real.rpow_pos_of_pos hJR _).ne'
  have hCneg0 : C₀ ^ (-δ) ≠ 0 := (Real.rpow_pos_of_pos hC₀ _).ne'
  dsimp only [K]
  rw [show ρ * -δ = -(ρ * δ) by ring, Real.rpow_neg hJR.le]
  field_simp [hJpow0, hCneg0]
  ring
  positivity

/-- The Stoneham rational-state Weyl means vanish under any positive power denominator lower
bound. -/
lemma stonehamState_square_mean_tendsto_of_powerLower
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (ρ C₀ : ℝ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b) (hp : ∀ i, p i ≠ 0)
    (hρ : 0 < ρ) (hC₀ : 0 < C₀)
    (hlower : StonehamStateDenPowerLower b L c m p ρ C₀) :
    Tendsto (fun J : ℕ =>
      (∑ n ∈ Icc 1 (J ^ 2), ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) /
        ((J ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
  let P := stonehamPrimes L c
  let ε : ℝ := 1 / (2 * r + 1 : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hP : ∀ q ∈ P, q.Prime ∧ Nat.Coprime q b := by
    simpa only [P] using stonehamPrimes_valid b L c hLb hcb
  obtain ⟨δ, C, hδ, hcor⟩ := hV b hb P hP ε hε
  have hrate : Tendsto (fun J : ℕ =>
      ((1 + r * Nat.log 2 (J ^ 2) : ℕ) : ℝ) / J +
        |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) *
          (1 + Real.log (L * (J ^ 2) ^ r))) atTop (𝓝 0) := by
    simpa only [zero_add] using (tendsto_natLog_square_div r).add
      (tendsto_stoneham_power_analytic_rate r L C₀ C ρ δ hL hC₀ hρ hδ)
  have hJρ : Tendsto (fun J : ℕ => (J : ℝ) ^ ρ) atTop atTop :=
    (tendsto_rpow_atTop hρ).comp tendsto_natCast_atTop_atTop
  have hC₀event : ∀ᶠ J : ℕ in atTop, C₀ < (J : ℝ) ^ ρ :=
    hJρ.eventually (eventually_gt_atTop C₀)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrate
  filter_upwards [eventually_ge_atTop (max 1 L), hC₀event] with J hJlarge hC₀J
  have hJ : 1 ≤ J := (le_max_left _ _).trans hJlarge
  have hLJ : L ≤ J := (le_max_right _ _).trans hJlarge
  have hs := stonehamState_square_bound_of_powerLower
    b L c m p ρ C₀ hb hL hLb hr hc hm hcb hp hρ hC₀ hlower hδ
    (by simpa only [P, ε] using hcor) J hJ hC₀J hLJ
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  rw [norm_div, Complex.norm_natCast]
  push_cast
  calc
    ‖∑ n ∈ Icc 1 (J ^ 2), ePhase ((stonehamState b L c m p n : ℚ) : ℝ)‖ /
          (J : ℝ) ^ 2
        ≤ ((1 + (r : ℝ) * (Nat.log 2 (J ^ 2) : ℝ)) * J +
            |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) * J ^ 2 *
              (1 + Real.log (L * (J ^ 2) ^ r))) / (J : ℝ) ^ 2 := by
          gcongr
    _ = (1 + (r : ℝ) * (Nat.log 2 (J ^ 2) : ℝ)) / J +
        |C| * (((J : ℝ) ^ ρ) / C₀) ^ (-δ) *
          (1 + Real.log (L * (J ^ 2) ^ r)) := by
      push_cast
      field_simp

lemma stonehamState_mean_tendsto_of_powerLower
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (ρ C₀ : ℝ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b) (hp : ∀ i, p i ≠ 0)
    (hρ : 0 < ρ) (hC₀ : 0 < C₀)
    (hlower : StonehamStateDenPowerLower b L c m p ρ C₀) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) /
        (N : ℂ)) atTop (𝓝 0) := by
  let f : ℕ → ℂ := fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)
  let z : ℕ → ℂ := fun n => f (n + 1)
  have hsq : Tendsto (fun J : ℕ =>
      (∑ n ∈ range (J ^ 2), z n) / ((J ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
    convert stonehamState_square_mean_tendsto_of_powerLower
      hV b L c m p ρ C₀ hb hL hLb hr hc hm hcb hp hρ hC₀ hlower using 1
    funext J
    simp only [z, f]
    rw [sum_range_shift_eq_sum_Icc
      (fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)) (J ^ 2)]
  have hz : ∀ n, ‖z n‖ ≤ 1 := fun n => by simp only [z, f, norm_ePhase, le_refl]
  have hall := DecayAeNormal.tendsto_of_tendsto_sq z hz hsq
  exact tendsto_mean_of_shift (fun n => by simp only [f, norm_ePhase, le_refl]) hall

/-- The analytic half of the literal Bailey--Borwein problem: a positive power lower bound for
the rational orbit-state denominator implies the required exponential-mean decay. -/
lemma stonehamCombination_mean_tendsto_of_powerLower
    (hV : VandeheyCor12) (b L : ℕ) {r : ℕ} (c m : Fin r → ℕ) (p : Fin r → ℤ)
    (ρ C₀ : ℝ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hLb : Nat.Coprime L b)
    (hr : 1 ≤ r) (hc : ∀ i, 2 ≤ c i) (hm : ∀ i, 1 ≤ m i)
    (hcb : ∀ i, Nat.Coprime (c i) b) (hp : ∀ i, p i ≠ 0)
    (hρ : 0 < ρ) (hC₀ : 0 < C₀)
    (hlower : StonehamStateDenPowerLower b L c m p ρ C₀) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
        ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)))) / (N : ℂ))
      atTop (𝓝 0) := by
  let a : ℕ → ℂ := fun n => ePhase ((b : ℝ) ^ n * ((1 / (L : ℝ)) *
    ∑ i, (p i : ℝ) * stonehamAlpha (b ^ m i) (c i)))
  let s : ℕ → ℂ := fun n => ePhase ((stonehamState b L c m p n : ℚ) : ℝ)
  have hs : Tendsto (fun N : ℕ => (∑ n ∈ range N, s n) / (N : ℂ))
      atTop (𝓝 0) := by
    simpa only [s] using stonehamState_mean_tendsto_of_powerLower
      hV b L c m p ρ C₀ hb hL hLb hr hc hm hcb hp hρ hC₀ hlower
  have he : Tendsto (fun n : ℕ => a n - s n) atTop (𝓝 0) := by
    simpa only [a, s] using stonehamCombination_phase_error_tendsto b L c m p hb hL hc hm
  have hemean : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (a n - s n)) / (N : ℂ)) atTop (𝓝 0) := by
    convert he.cesaro_smul using 1
    · funext N
      simp only [Complex.real_smul, div_eq_mul_inv]
      rw [show (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by
        simpa using (Complex.ofReal_inv (N : ℝ)).symm]
      ring
  convert hs.add hemean using 1
  · funext N
    simp only [a, s, Finset.sum_sub_distrib]
    ring
  · simp

/-- Weyl wiring for a literal signed pair.  Once every nonzero Fourier multiplier has some
positive-power reduced-denominator lower bound, the corresponding pair is normal.  The exponent
and constant may depend on the multiplier. -/
lemma isNormal_stonehamAlpha_pair_of_powerLower
    (hV : VandeheyThm51) (b c₁ c₂ : ℕ) (σ : ℤ)
    (hb : 2 ≤ b) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b) (hσ : σ ≠ 0)
    (hlower : ∀ h : ℤ, h ≠ 0 → ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      StonehamStateDenPowerLower b 1 ![c₁, c₂] ![1, 1] ![h, σ * h] ρ C) :
    IsNormal b (stonehamAlpha b c₁ + (σ : ℝ) * stonehamAlpha b c₂) := by
  let x : ℝ := stonehamAlpha b c₁ + (σ : ℝ) * stonehamAlpha b c₂
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (orbit_mem_Ico b _) ?_
  intro h hh
  obtain ⟨ρ, C, hρ, hC, hden⟩ := hlower h hh
  have hc : ∀ i : Fin 2, 2 ≤ ![c₁, c₂] i := by
    intro i
    fin_cases i <;> simp_all
  have hm : ∀ i : Fin 2, 1 ≤ ![1, 1] i := by
    intro i
    fin_cases i <;> simp
  have hcb : ∀ i : Fin 2, Nat.Coprime (![c₁, c₂] i) b := by
    intro i
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      assumption
  have hp : ∀ i : Fin 2, ![h, σ * h] i ≠ 0 := by
    intro i
    fin_cases i <;> simp_all
  have hmean := stonehamCombination_mean_tendsto_of_powerLower
    (vandeheyCor12_of_thm51 hV) b 1 ![c₁, c₂] ![1, 1] ![h, σ * h] ρ C
      hb (by omega) (by simp) (by omega) hc hm hcb hp hρ hC hden
  have heq : fourierMean (orbit b x) h = fun N : ℕ =>
      (∑ n ∈ range N, ePhase ((h : ℝ) * orbit b x n)) / (N : ℂ) := by
    funext N
    rw [fourierMean]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [ePhase]
    congr 1
    push_cast
    ring
  rw [heq]
  convert hmean using 1
  funext N
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [ePhase_orbit]
  congr 1
  dsimp only [x]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, pow_one, one_div, one_mul, Int.cast_mul]
  push_cast
  ring

/-- A single Stoneham family is the one-coordinate case of Theorem A. -/
lemma isNormal_stonehamAlpha_of_vandehey
    (hV : VandeheyThm51) (b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hcb : Nat.Coprime c b) :
    IsNormal b (stonehamAlpha b c) := by
  have hcop : Pairwise fun i j : Fin 1 => Nat.Coprime (![c] i) (![c] j) := by
    intro i j hij
    fin_cases i
    fin_cases j
    simp at hij
  have hn := isNormal_stonehamCombination_int_nonzero
    hV b hb ![c] ![1] ![1]
      (by intro i; fin_cases i; simpa)
      hcop
      (by intro i; fin_cases i; simpa)
      (by intro i; fin_cases i; simp)
      (by norm_num)
      (by intro i; fin_cases i; simp)
  simpa only [Fin.sum_univ_one, Matrix.cons_val_zero, Int.cast_one, one_mul, pow_one] using hn

/-- The equal-parameter literal sum is rational scaling of one normal Stoneham family. -/
lemma isNormal_stonehamAlpha_add_self
    (hV : VandeheyThm51) (b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hcb : Nat.Coprime c b) :
    IsNormal b (stonehamAlpha b c + stonehamAlpha b c) := by
  have hn := isNormal_stonehamAlpha_of_vandehey hV b c hb hc hcb
  simpa [two_mul] using
    (isNormal_rat_mul_add b hb (stonehamAlpha b c) (2 : ℚ) 0 (by norm_num) hn)

end NormalNumbers.StonehamSumsNormal
