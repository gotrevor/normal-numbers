/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormalB

/-!
# Derandomization over a primitive recursive family of maps

`ComputableNormalB.exists_computable_absNormal` for countably many maps `G i` at once: one
computable coin sequence `e` with every `G i e` normal in every base.  Test `j` checks, for each
`i ≤ j`, level `N(i, j) = (j + 8)·M_i` of map `i`, with `M_i` large enough (primitive recursive in
`i`) that the union over `i` has mass `≤ 1/(j+8)²`.  Normality then follows along the levels
`n_j = M_i (j + 8)`, whose fourteenth powers still have ratio `→ 1`.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.FamilyDerandomize

open Derandomize DecayAeNormal VisitDeviation VisitDeviationB ComputableNormalB

/-! ## The tests are primitive recursive uniformly in the family index -/

section Primrec

variable (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ)
  (hΨp : Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2)

include hΨp

variable {α : Type*} [Primcodable α]

theorem fprimrec_dA {fi fb fE fr : α → ℕ} {fp : α → List Bool} (hi : Primrec fi) (hb : Primrec fb) (hE : Primrec fE)
    (hr : Primrec fr) (hp : Primrec fp) :
    Primrec fun a => dA (Ψ (fi a)) (fb a) (fE a) (fr a) (fp a) :=
  Primrec.nat_mod.comp (hΨp.comp (Primrec.pair hi (Primrec.pair hb (Primrec.pair (Primrec.nat_add.comp hE hr) hp))))
    (ComputableNormal.primrec_pow.comp hb hr)

theorem fprimrec_Vc {fi fb fl fv fN : α → ℕ} {fp : α → List Bool} (hi : Primrec fi) (hb : Primrec fb)
    (hl : Primrec fl) (hv : Primrec fv) (hN : Primrec fN) (hp : Primrec fp) :
    Primrec fun a => Vc (Ψ (fi a)) (fb a) (fl a) (fv a) (fN a) (fp a) := by
  have hg : Primrec₂ fun (a : α) (k : ℕ) => if dA (Ψ (fi a)) (fb a) k (fl a) (fp a) = fv a then 1 else 0 :=
    (Primrec.ite (Primrec.eq.comp (fprimrec_dA Ψ hΨp (hi.comp Primrec.fst) (hb.comp Primrec.fst) Primrec.snd
      (hl.comp Primrec.fst) (hp.comp Primrec.fst)) (hv.comp Primrec.fst))
      (Primrec.const 1) (Primrec.const 0)).to₂
  exact primrec_sum_map (Primrec.list_range.comp hN) hg

theorem fprimrec_Tc {fi fb fn : α → ℕ} {fp : α → List Bool} (hi : Primrec fi) (hb : Primrec fb) (hn : Primrec fn)
    (hp : Primrec fp) : Primrec fun a => Tc (Ψ (fi a)) (fb a) (fn a) (fp a) := by
  have hg : Primrec₂ fun (a : α) (j : ℕ) =>
      if dA (Ψ (fi a)) (fb a) j (fn a) (fp a) = fb a ^ fn a - 1 then 1 else 0 :=
    (Primrec.ite (Primrec.eq.comp (fprimrec_dA Ψ hΨp (hi.comp Primrec.fst) (hb.comp Primrec.fst) Primrec.snd
      (hn.comp Primrec.fst) (hp.comp Primrec.fst))
      (Primrec.nat_sub.comp (ComputableNormal.primrec_pow.comp (hb.comp Primrec.fst) (hn.comp Primrec.fst))
        (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0)).to₂
  exact primrec_sum_map (Primrec.list_range.comp
    (Primrec.nat_add.comp (ComputableNormal.primrec_pow.comp hn (Primrec.const 14)) hn)) hg

theorem fprimrec_fails_b {fi fb fn fl fv : α → ℕ} {fp : α → List Bool} (hi : Primrec fi) (hb : Primrec fb)
    (hn : Primrec fn) (hl : Primrec fl) (hv : Primrec fv) (hp : Primrec fp) :
    PrimrecPred fun a => fails (Ψ (fi a)) (fb a) (fn a) (fl a) (fv a) (fp a) := by
  have hN : Primrec fun a => fn a ^ 14 := ComputableNormal.primrec_pow.comp hn (Primrec.const 14)
  have hP : Primrec fun a => fb a ^ fl a := ComputableNormal.primrec_pow.comp hb hl
  have hV := fprimrec_Vc Ψ hΨp hi hb hl hv hN hp
  have hVP := Primrec.nat_mul.comp hV hP
  have lhs := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 3) hN) hP
  have rhs := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) hn)
    (Primrec.nat_add.comp (Primrec.nat_sub.comp hVP hN) (Primrec.nat_sub.comp hN hVP))
  exact (Primrec.nat_lt.comp lhs rhs).of_eq fun a => by unfold fails; rfl

theorem fprimrec_failsTop_b {fi fb fn : α → ℕ} {fp : α → List Bool} (hi : Primrec fi) (hb : Primrec fb)
    (hn : Primrec fn) (hp : Primrec fp) :
    PrimrecPred fun a => failsTop (Ψ (fi a)) (fb a) (fn a) (fp a) := by
  have hN : Primrec fun a => fn a ^ 14 := ComputableNormal.primrec_pow.comp hn (Primrec.const 14)
  exact (Primrec.nat_lt.comp hN (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) hn)
    (fprimrec_Tc Ψ hΨp hi hb hn hp))).of_eq fun a => by unfold failsTop; rfl

attribute [local irreducible] fails failsTop in
theorem fprimrec_baseBad {fi fb fn : α → ℕ} {fp : α → List Bool} (hi : Primrec fi) (hb : Primrec fb)
    (hn : Primrec fn) (hp : Primrec fp) :
    Primrec fun a => baseBad (Ψ (fi a)) (fb a) (fn a) (fp a) := by
  have htop : Primrec fun a => if failsTop (Ψ (fi a)) (fb a) (fn a) (fp a) then 1 else 0 :=
    Primrec.ite (fprimrec_failsTop_b Ψ hΨp hi hb hn hp) (Primrec.const 1) (Primrec.const 0)
  -- inner sum over v, context α × ℕ (ℓ)
  have hin : Primrec fun y : α × ℕ =>
      ((List.range (fb y.1 ^ y.2)).map fun v =>
        if fails (Ψ (fi y.1)) (fb y.1) (fn y.1) y.2 v (fp y.1) then 1 else 0).sum := by
    have hfv : Primrec₂ fun (y : α × ℕ) (v : ℕ) =>
        if fails (Ψ (fi y.1)) (fb y.1) (fn y.1) y.2 v (fp y.1) then 1 else 0 :=
      (Primrec.ite (fprimrec_fails_b Ψ hΨp (hi.comp (Primrec.fst.comp Primrec.fst)) (hb.comp (Primrec.fst.comp Primrec.fst))
        (hn.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst) Primrec.snd
        (hp.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 1) (Primrec.const 0)).to₂
    exact primrec_sum_map (Primrec.list_range.comp
      (ComputableNormal.primrec_pow.comp (hb.comp Primrec.fst) Primrec.snd)) hfv
  have hcond : PrimrecPred fun y : α × ℕ => 1 ≤ y.2 ∧ fb y.1 ^ y.2 ≤ fn y.1 :=
    PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
      (Primrec.nat_le.comp (ComputableNormal.primrec_pow.comp (hb.comp Primrec.fst) Primrec.snd)
        (hn.comp Primrec.fst))
  have hg : Primrec₂ fun (a : α) (ℓ : ℕ) => if 1 ≤ ℓ ∧ fb a ^ ℓ ≤ fn a then
      ((List.range (fb a ^ ℓ)).map fun v =>
        if fails (Ψ (fi a)) (fb a) (fn a) ℓ v (fp a) then 1 else 0).sum else 0 :=
    (Primrec.ite hcond hin (Primrec.const 0)).to₂
  exact (Primrec.nat_add.comp htop
    (primrec_sum_map (Primrec.list_range.comp (Primrec.succ.comp hn)) hg)).of_eq
    fun a => rfl


attribute [local irreducible] baseBad in
theorem fprimrec_levelBad :
    Primrec fun x : ℕ × ℕ × List Bool => levelBad (Ψ x.1) x.2.1 x.2.2 := by
  have hg : Primrec₂ fun (x : ℕ × ℕ × List Bool) (b : ℕ) =>
      if 2 ≤ b then baseBad (Ψ x.1) b x.2.1 x.2.2 else 0 :=
    (Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) Primrec.snd)
      (fprimrec_baseBad Ψ hΨp (Primrec.fst.comp Primrec.fst) Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const 0)).to₂
  exact primrec_sum_map (Primrec.list_range.comp (Primrec.succ.comp
    (Primrec.fst.comp Primrec.snd))) hg

end Primrec


/-! ## Normality from good levels along an arithmetic progression -/

theorem normal_of_good_AP (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (M j₀ : ℕ) (hM : 1 ≤ M)
    (hgood : ∀ j, j₀ ≤ j → ∀ ℓ, 1 ≤ ℓ → b ^ ℓ ≤ M * (j + 8) → ∀ v : ℕ, v < b ^ ℓ →
      |(visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ)
        ((M * (j + 8)) ^ 14) : ℝ) / (((M * (j + 8)) ^ 14 : ℕ) : ℝ) - 1 / (b : ℝ) ^ ℓ| ≤
        1 / ((M * (j + 8) : ℕ) : ℝ)) :
    IsNormal b x := by
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_badic b hb _ fun ℓ hℓ v hv => ?_
  refine tendsto_div_of_monotone_of_exists_subseq_tendsto_div _ _
    (fun m n h => by exact_mod_cast ComputableNormal.visitCount_mono_n _ _ _ h) fun a ha =>
      ⟨fun j => (M * (j + 8)) ^ 14, ?_, ?_, ?_⟩
  · have hr := pow14_ratio a ha
    rw [Filter.eventually_atTop] at hr ⊢
    obtain ⟨N, hN⟩ := hr
    refine ⟨N, fun j hj => ?_⟩
    have h := hN (j + 8) (by omega)
    have hM14 : (0 : ℝ) ≤ ((M ^ 14 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h hM14
    push_cast at this ⊢
    have e1 : ((M : ℝ) * ((j : ℝ) + 1 + 8)) ^ 14 = (M : ℝ) ^ 14 * ((j : ℝ) + 8 + 1) ^ 14 := by
      ring
    rw [e1, mul_pow]
    linarith [this]
  · refine Filter.tendsto_atTop_mono (fun j => ?_) Filter.tendsto_id
    calc j ≤ M * (j + 8) := by nlinarith
      _ ≤ (M * (j + 8)) ^ 14 := Nat.le_self_pow (by norm_num) _
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ (tendsto_one_div_add_atTop_nhds_zero_nat)
    filter_upwards [eventually_ge_atTop (max j₀ (b ^ ℓ))] with j hj
    simp only [Real.norm_eq_abs, abs_abs]
    refine (hgood j (le_of_max_le_left hj) ℓ hℓ ?_ v hv).trans ?_
    · have := le_of_max_le_right hj; nlinarith
    · rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
      push_cast; nlinarith [(by exact_mod_cast hM : (1 : ℝ) ≤ M)]


/-! ## The family tests -/

/-- Coins read by a level-`n` test. -/
def depthL (n : ℕ) : ℕ := n * (n ^ 14 + 2 * n)

/-- Test `j`: some map `i ≤ j` fails at its level `M_i (j + 8)`. -/
def badF (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ) (Mf : ℕ → ℕ) (j : ℕ) (p : List Bool) : Bool :=
  decide (0 < ((List.range (j + 1)).map fun i =>
    levelBad (Ψ i) (Mf i * (j + 8)) (p.take (depthL (Mf i * (j + 8))))).sum)

/-- Coins read by test `j`. -/
def dF (Mf : ℕ → ℕ) (j : ℕ) : ℕ :=
  ((List.range (j + 1)).map fun i => depthL (Mf i * (j + 8))).sum

theorem primrec_depthL : Primrec depthL :=
  Primrec.nat_mul.comp Primrec.id (Primrec.nat_add.comp
    (ComputableNormal.primrec_pow.comp Primrec.id (Primrec.const 14))
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))

theorem primrec_dF {Mf : ℕ → ℕ} (hM : Primrec Mf) : Primrec (dF Mf) := by
  have hg : Primrec₂ fun (j i : ℕ) => depthL (Mf i * (j + 8)) :=
    (primrec_depthL.comp (Primrec.nat_mul.comp (hM.comp Primrec.snd)
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 8)))).to₂
  exact primrec_sum_map (Primrec.list_range.comp Primrec.succ) hg

theorem primrec_badF (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2)
    {Mf : ℕ → ℕ} (hM : Primrec Mf) : Primrec₂ (badF Ψ Mf) := by
  have hN : Primrec fun y : (ℕ × List Bool) × ℕ => Mf y.2 * (y.1.1 + 8) :=
    Primrec.nat_mul.comp (hM.comp Primrec.snd)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 8))
  have hg : Primrec₂ fun (x : ℕ × List Bool) (i : ℕ) =>
      levelBad (Ψ i) (Mf i * (x.1 + 8)) (x.2.take (depthL (Mf i * (x.1 + 8)))) :=
    ((fprimrec_levelBad Ψ hΨp).comp (Primrec.pair Primrec.snd (Primrec.pair hN
      (Primrec.list_take.comp (primrec_depthL.comp hN) (Primrec.snd.comp Primrec.fst))))).to₂
  have hs := primrec_sum_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) hg
  exact (Primrec.nat_lt.comp (Primrec.const 0) hs).decide.to₂

theorem pre_take (ω : ℕ → Bool) {m n : ℕ} (h : m ≤ n) : (pre ω n).take m = pre ω m := by
  simp only [pre]
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem le_dF (Mf : ℕ → ℕ) {i j : ℕ} (hi : i ≤ j) : depthL (Mf i * (j + 8)) ≤ dF Mf j := by
  unfold dF
  rw [ComputableNormalB.list_sum_range_map]
  exact Finset.single_le_sum (f := fun i => depthL (Mf i * (j + 8))) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

theorem dens_badF (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ) (Mf : ℕ → ℕ) (j : ℕ) :
    dens (badF Ψ Mf) (dF Mf) j [] = coins.real {ω | badF Ψ Mf j (pre ω (dF Mf j)) = true} := by
  unfold dens
  simp only [List.length_nil, Nat.sub_zero]
  rw [← coins_pre, measureReal_def]
  congr 2
  ext ω
  simp [badAt, List.take_of_length_le (le_of_eq (length_pre ω _))]


theorem geom_quarter_le (n : ℕ) : ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ (i + 2) ≤ 1 := by
  have h := sum_geometric_two_le n
  calc ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ (i + 2)
      ≤ ∑ i ∈ Finset.range n, (1 / 16 : ℝ) * (1 / 2) ^ i := Finset.sum_le_sum fun i _ => by
        rw [pow_add]
        have : (1 / 4 : ℝ) ^ i ≤ (1 / 2) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
        nlinarith
    _ = (1 / 16) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ 1 := by nlinarith


/-- **Generic family derandomization.** -/
theorem exists_computable_absNormal_family (Ψ : ℕ → ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2.1 x.2.2.2)
    (A : ℕ → List Bool → ℝ) (hΨ : ∀ i b m p, Ψ i b m p = ⌊A i p * (b : ℝ) ^ m⌋₊)
    (hA0 : ∀ i p, 0 ≤ A i p) (G : ℕ → (ℕ → Bool) → ℝ) (hGm : ∀ i, Measurable (G i))
    (hAG : ∀ i ω D, A i (pre ω D) ≤ G i ω ∧ G i ω ≤ A i (pre ω D) + (1 / 2 : ℝ) ^ D)
    (c : ℕ → ℕ) (hc : Primrec c) {δ : ℝ} (hδ : 0 < δ)
    (hdec : ∀ i, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖∫ ω, ee (ξ * G i ω) ∂coins‖ ≤ c i * |ξ| ^ (-δ)) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ i b, 2 ≤ b → IsNormal b (G i e) := by
  set κN : ℕ := ⌈ComputableNormal.Kc 1 δ⌉₊ with hκN
  set c₁ : ℕ → ℕ := fun i => 49344 * (1 + (c i + 1) * κN) with hc₁
  set Mf : ℕ → ℕ := fun i => (c₁ i + 1) * 4 ^ (i + 2) with hMf
  have hMp : Primrec Mf := by
    have h1 : Primrec c₁ := Primrec.nat_mul.comp (Primrec.const _) (Primrec.nat_add.comp
      (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.succ.comp hc) (Primrec.const _)))
    exact Primrec.nat_mul.comp (Primrec.succ.comp h1)
      (ComputableNormal.primrec_pow.comp (Primrec.const 4)
        (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
  have hM1 : ∀ i, 1 ≤ Mf i := fun i => Nat.mul_pos (Nat.succ_pos _) (by positivity)
  -- per-map level mass
  have hlev : ∀ i n, 8 ≤ n →
      coins.real {ω | 0 < levelBad (Ψ i) n (pre ω (depthL n))} ≤ (c₁ i : ℝ) / (n : ℝ) ^ 2 := by
    intro i n hn
    have hC : (0 : ℝ) < (c i : ℝ) + 1 := by positivity
    have hdec' : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G i ω) ∂coins‖ ≤ ((c i : ℝ) + 1) * |ξ| ^ (-δ) :=
      fun ξ hξ => (hdec i ξ hξ).trans (by
        have := Real.rpow_nonneg (abs_nonneg ξ) (-δ); nlinarith)
    have h := level_bound_b (Ψ i) (A i) (hΨ i) (hA0 i) (G i) (hGm i) (hAG i) hC hδ hdec' hn
    refine h.trans ?_
    gcongr
    have hK : ComputableNormal.Kc ((c i : ℝ) + 1) δ = ((c i : ℝ) + 1) * ComputableNormal.Kc 1 δ := by
      unfold ComputableNormal.Kc; ring
    have hK0 : 0 ≤ ComputableNormal.Kc 1 δ := ComputableNormal.Kc_nonneg one_pos hδ
    have hKN : ComputableNormal.Kc 1 δ ≤ κN := Nat.le_ceil _
    have hx : 0 ≤ ComputableNormal.Kc ((c i : ℝ) + 1) δ := by rw [hK]; positivity
    have hs : Real.sqrt (1 + ComputableNormal.Kc ((c i : ℝ) + 1) δ) ≤
        1 + ComputableNormal.Kc ((c i : ℝ) + 1) δ :=
      by rw [Real.sqrt_le_left (by positivity)]; nlinarith
    rw [hc₁]; push_cast
    have : ComputableNormal.Kc ((c i : ℝ) + 1) δ ≤ ((c i : ℝ) + 1) * κN := by
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

end NormalNumbers.FamilyDerandomize
