/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.FamilyDerandomize

/-!
# Family derandomization with a per-index decay exponent

`FamilyDerandomize.exists_computable_absNormal_family` asks for one exponent `δ` for the whole
family.  That suffices for `Ω_k` (the cut runs with a fixed zero count `N = k − 2`), but not for
Manai's `P`/`Q` problem (`ExplicitPQ`), where the zero count of `G_P''` grows with `deg P` and the
cut's exponent `δ_N` shrinks with it.  The decay exponent only ever enters the derandomizer
through `Kc 1 δ` (`ComputableNormal.Kc`), so a per-index `δ i` costs nothing beyond a primitive
recursive bound `κ i ≥ Kc 1 (δ i)`.  The proof is the fixed-`δ` proof with `κN` replaced by `κ i`.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.FamilyDerandomize

open Derandomize DecayAeNormal VisitDeviation VisitDeviationB ComputableNormalB

/-- **Generic family derandomization, per-index exponent.** -/
theorem exists_computable_absNormal_family_var (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2)
    (A : ℕ → List Bool → ℝ) (hΨ : ∀ i b m p, Ψ i b m p = ⌊A i p * (b : ℝ) ^ m⌋₊)
    (hA0 : ∀ i p, 0 ≤ A i p) (G : ℕ → (ℕ → Bool) → ℝ) (hGm : ∀ i, Measurable (G i))
    (hAG : ∀ i ω D, A i (pre ω D) ≤ G i ω ∧ G i ω ≤ A i (pre ω D) + (1 / 2 : ℝ) ^ D)
    (c : ℕ → ℕ) (hc : Primrec c) (δ : ℕ → ℝ) (hδ : ∀ i, 0 < δ i)
    (κ : ℕ → ℕ) (hκ : Primrec κ) (hκδ : ∀ i, ComputableNormal.Kc 1 (δ i) ≤ κ i)
    (hdec : ∀ i, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖∫ ω, ee (ξ * G i ω) ∂coins‖ ≤ c i * |ξ| ^ (-δ i)) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ i b, 2 ≤ b → IsNormal b (G i e) := by
  set c₁ : ℕ → ℕ := fun i => 49344 * (1 + (c i + 1) * κ i) with hc₁
  set Mf : ℕ → ℕ := fun i => (c₁ i + 1) * 4 ^ (i + 2) with hMf
  have hMp : Primrec Mf := by
    have h1 : Primrec c₁ := Primrec.nat_mul.comp (Primrec.const _) (Primrec.nat_add.comp
      (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.succ.comp hc) hκ))
    exact Primrec.nat_mul.comp (Primrec.succ.comp h1)
      (ComputableNormal.primrec_pow.comp (Primrec.const 4)
        (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
  have hM1 : ∀ i, 1 ≤ Mf i := fun i => Nat.mul_pos (Nat.succ_pos _) (by positivity)
  -- per-map level mass
  have hlev : ∀ i n, 8 ≤ n →
      coins.real {ω | 0 < levelBad (Ψ i) n (pre ω (depthL n))} ≤ (c₁ i : ℝ) / (n : ℝ) ^ 2 := by
    intro i n hn
    have hC : (0 : ℝ) < (c i : ℝ) + 1 := by positivity
    have hdec' : ∀ ξ : ℝ, ξ ≠ 0 →
        ‖∫ ω, ee (ξ * G i ω) ∂coins‖ ≤ ((c i : ℝ) + 1) * |ξ| ^ (-δ i) :=
      fun ξ hξ => (hdec i ξ hξ).trans (by
        have := Real.rpow_nonneg (abs_nonneg ξ) (-δ i); nlinarith)
    have h := level_bound_b (Ψ i) (A i) (hΨ i) (hA0 i) (G i) (hGm i) (hAG i) hC (hδ i) hdec' hn
    refine h.trans ?_
    gcongr
    have hK : ComputableNormal.Kc ((c i : ℝ) + 1) (δ i) =
        ((c i : ℝ) + 1) * ComputableNormal.Kc 1 (δ i) := by
      unfold ComputableNormal.Kc; ring
    have hK0 : 0 ≤ ComputableNormal.Kc 1 (δ i) := ComputableNormal.Kc_nonneg one_pos (hδ i)
    have hKN : ComputableNormal.Kc 1 (δ i) ≤ κ i := hκδ i
    have hx : 0 ≤ ComputableNormal.Kc ((c i : ℝ) + 1) (δ i) := by rw [hK]; positivity
    have hs : Real.sqrt (1 + ComputableNormal.Kc ((c i : ℝ) + 1) (δ i)) ≤
        1 + ComputableNormal.Kc ((c i : ℝ) + 1) (δ i) :=
      by rw [Real.sqrt_le_left (by positivity)]; nlinarith
    rw [hc₁]; push_cast
    have : ComputableNormal.Kc ((c i : ℝ) + 1) (δ i) ≤ ((c i : ℝ) + 1) * κ i := by
      rw [hK]; gcongr
    linarith
  -- per-test mass
  have hdj : ∀ j, dens (badF Ψ Mf) (dF Mf) j [] ≤ 1 / ((j : ℝ) + 8) ^ 2 := by
    intro j
    rw [dens_badF]
    have hsub : {ω | badF Ψ Mf j (pre ω (dF Mf j)) = true} ⊆
        ⋃ i ∈ Finset.range (j + 1),
          {ω | 0 < levelBad (Ψ i) (Mf i * (j + 8)) (pre ω (depthL (Mf i * (j + 8))))} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, badF, decide_eq_true_eq] at hω
      rw [ComputableNormalB.list_sum_range_map] at hω
      obtain ⟨i, hi, hpos⟩ := ComputableNormalB.exists_pos_of_sum_pos hω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨i, hi, ?_⟩
      rwa [pre_take ω (le_dF Mf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))] at hpos
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_biUnion_finset_le _ _).trans ?_)
    have hj8 : (0 : ℝ) < (j : ℝ) + 8 := by positivity
    calc ∑ i ∈ Finset.range (j + 1), coins.real
          {ω | 0 < levelBad (Ψ i) (Mf i * (j + 8)) (pre ω (depthL (Mf i * (j + 8))))}
        ≤ ∑ i ∈ Finset.range (j + 1), (1 / 4 : ℝ) ^ (i + 2) * (1 / ((j : ℝ) + 8) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => (hlev i _ ?_).trans ?_
          · nlinarith [hM1 i]
          · have hc1 : (0 : ℝ) ≤ c₁ i := by positivity
            have hMR : ((Mf i : ℕ) : ℝ) = ((c₁ i : ℝ) + 1) * 4 ^ (i + 2) := by
              rw [hMf]; push_cast; ring
            have h4 : (0 : ℝ) < 4 ^ (i + 2) := by positivity
            push_cast
            rw [hMR]
            rw [div_le_iff₀ (by positivity)]
            have e : (1 / 4 : ℝ) ^ (i + 2) * (1 / ((j : ℝ) + 8) ^ 2) *
                (((c₁ i : ℝ) + 1) * 4 ^ (i + 2) * ((j : ℝ) + 8)) ^ 2 =
                ((c₁ i : ℝ) + 1) * (((c₁ i : ℝ) + 1) * 4 ^ (i + 2)) := by
              field_simp
              rw [← mul_pow]; norm_num
            rw [e]
            have : (1 : ℝ) ≤ ((c₁ i : ℝ) + 1) * 4 ^ (i + 2) := by
              nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := i + 2)]
            nlinarith
      _ = (∑ i ∈ Finset.range (j + 1), (1 / 4 : ℝ) ^ (i + 2)) * (1 / ((j : ℝ) + 8) ^ 2) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (1 / ((j : ℝ) + 8) ^ 2) := by gcongr; exact geom_quarter_le _
      _ = _ := one_mul _
  have hnn : ∀ j, 0 ≤ dens (badF Ψ Mf) (dF Mf) j [] := fun j => dens_nonneg j []
  have hdj' : ∀ j, 0 ≤ j → dens (badF Ψ Mf) (dF Mf) j [] ≤ (1 : ℝ) / ((j : ℝ) + (8 : ℕ)) ^ 2 :=
    fun j _ => by push_cast; exact hdj j
  obtain ⟨hs0, ht0⟩ := ComputableNormal.tsum_tail_le _ hnn 1 zero_le_one 0 8 (by norm_num) hdj'
  simp only [zero_le, if_true, Nat.cast_zero, zero_add] at hs0 ht0
  have htot : ∑' j, dens (badF Ψ Mf) (dF Mf) j [] ≤ 1 / 4 := ht0.trans (by norm_num)
  set J : ℕ → ℕ := fun k => 8 ^ (k + 1) with hJdef
  have hJ : Primrec J := ComputableNormal.primrec_pow.comp (Primrec.const 8) Primrec.succ
  have htail : ∀ k, ∑' j, (if J k < j then dens (badF Ψ Mf) (dF Mf) j [] else 0) ≤
      (1 / 8 : ℝ) ^ (k + 1) := by
    intro k
    obtain ⟨_, ht⟩ := ComputableNormal.tsum_tail_le _ hnn 1 zero_le_one (J k + 1) 8 (by omega)
      (fun j _ => hdj' j (Nat.zero_le _))
    have e : (fun j => if J k < j then dens (badF Ψ Mf) (dF Mf) j [] else 0) =
        fun j => if J k + 1 ≤ j then dens (badF Ψ Mf) (dF Mf) j [] else 0 := by
      funext j; simp only [Nat.lt_iff_add_one_le]
    rw [e]
    refine ht.trans ?_
    have hJR : ((J k : ℕ) : ℝ) = 8 ^ (k + 1) := by simp [hJdef]
    rw [div_pow, one_pow, div_le_div_iff₀ (by push_cast; rw [hJR]; linarith [pow_pos (show (0:ℝ) < 8 by norm_num) (k + 1)]) (by positivity)]
    push_cast; rw [hJR]; linarith
  obtain ⟨e, hce, hav⟩ := exists_primrec_avoid (badF Ψ Mf) (primrec_badF Ψ hΨp hMp) (dF Mf)
    (primrec_dF hMp) J hJ hs0 htot htail
  refine ⟨e, hce, fun i b hb => normal_of_good_AP b hb (G i e) (Mf i) (max i b) (hM1 i)
    fun j hj ℓ hℓ hℓn v hv => ?_⟩
  have hij : i ≤ j := le_of_max_le_left hj
  have hbj : b ≤ j := le_of_max_le_right hj
  set n := Mf i * (j + 8) with hn
  have hbn : b ≤ n := by nlinarith [hM1 i]
  have hbad0 := hav j
  simp only [badF, decide_eq_false_iff_not, not_lt, Nat.le_zero] at hbad0
  rw [ComputableNormalB.list_sum_range_map, Finset.sum_eq_zero_iff] at hbad0
  have hbad := hbad0 i (Finset.mem_range.2 (Nat.lt_succ_of_le hij))
  rw [pre_take e (le_dF Mf hij)] at hbad
  obtain ⟨htop, hpass⟩ := pass_of_levelBad_zero (Ψ i) hbad hb hbn
  have hℓle : ℓ ≤ n := (Nat.lt_pow_self (by omega : 1 < b)).le.trans hℓn
  have hax := (hAG i e (n * (n ^ 14 + 2 * n))).1
  exact good_of_pass (Ψ i) (A i) (hΨ i) hb (by omega) hℓle (G i e) _ (hA0 _ _) hax
    (eta_le (A i) hbn (G i e) _ hax (hAG i e _).2) htop (hpass ℓ hℓ hℓn v hv)

/-- **The exponent cost is polynomial in `1/δ`.**  For `0 < δ ≤ 1`,
`Kc 1 δ = 2^δ (1 − 2^{−δ/2})^{−2} ≤ 32/δ²`.

Proved.  English proof: `2^δ ≤ 2`.  With `z = δ log 2 / 2 ∈ (0, 0.35]`,
`1 − 2^{−δ/2} = 1 − e^{−z} ≥ z − z²/2 ≥ 0.82 z ≥ δ/4`, so `(1 − 2^{−δ/2})^{−2} ≤ 16/δ²`. -/
theorem Kc_one_le_of_le_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ComputableNormal.Kc 1 δ ≤ 32 / δ ^ 2 := by
  unfold ComputableNormal.Kc
  set z := Real.log 2 * (δ / 2) with hz
  have hl1 := Real.log_two_gt_d9
  have hz0 : 0 < z := by rw [hz]; have := Real.log_pos one_lt_two; positivity
  have hzδ : δ / 3 ≤ z := by rw [hz]; nlinarith
  have he : (2 : ℝ) ^ (-δ / 2) = Real.exp (-z) := by
    rw [Real.rpow_def_of_pos two_pos, hz]; ring_nf
  have hexp : Real.exp (-z) ≤ 1 / (1 + z) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp z])
  have hgap : δ / 4 ≤ 1 - (2 : ℝ) ^ (-δ / 2) := by
    rw [he]
    have h1 : 1 - 1 / (1 + z) = z / (1 + z) := by field_simp; ring
    have h2 : δ / 4 ≤ z / (1 + z) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hδ1 hz0.le]
    linarith
  have h2 : (2 : ℝ) ^ δ ≤ 2 := by
    calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 2 := Real.rpow_one 2
  have hpos : 0 < 1 - (2 : ℝ) ^ (-δ / 2) := by linarith [show 0 < δ / 4 by positivity]
  have hinv : (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ ≤ 4 / δ := by
    rw [inv_le_comm₀ hpos (by positivity), inv_div]; linarith
  have hinv0 : 0 ≤ (1 - (2 : ℝ) ^ (-δ / 2))⁻¹ := (inv_pos.2 hpos).le
  calc 1 * (2 : ℝ) ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2 ≤ 2 * (4 / δ) ^ 2 := by
        rw [one_mul]; gcongr
    _ = 32 / δ ^ 2 := by ring

end NormalNumbers.FamilyDerandomize
