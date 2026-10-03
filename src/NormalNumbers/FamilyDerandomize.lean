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

end NormalNumbers.FamilyDerandomize
