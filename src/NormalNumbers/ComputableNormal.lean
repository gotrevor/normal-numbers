/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Derandomize
import NormalNumbers.VisitDeviation
import NormalNumbers.Sandwich
import NormalNumbers.Wall

/-!
# Polynomial decay + computable digits ⇒ a computable coin sequence with normal image

Generic assembly of the row-3 derandomization (`exists_computable_normal_of_digits`).  Inputs:
a random real `G ω ≥ 0` on fair coins with polynomial Fourier decay, whose binary floors
`⌊G ω · 2^m⌋` are a primitive-recursive function `Φ m` of the first `m` coins.

Test `j` (level `n = j + n₀`, `N = n^10`): some dyadic block `[v/2^ℓ, (v+1)/2^ℓ)` with
`1 ≤ ℓ`, `2^ℓ ≤ n` has `|V/N − 2^{-ℓ}| > 3/(4n)`, decided exactly from the first
`N + n` coins.  `visit_deviation` with `ρ = t = 1/(4n)` bounds each block by `c₁ n^{-3}`,
so level `n` by `2c₁/n²`; `exists_primrec_avoid` derandomizes; avoidance gives dyadic
frequencies along `n^10`, then along all `N` by monotone interpolation, then normality via
`equidistributed_of_badic` and Wall.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.ComputableNormal

open Derandomize DecayAeNormal VisitDeviation

variable (Φ : ℕ → List Bool → ℕ)

/-- Exact visit count of block `(ℓ, v)` among the first `N` orbit points, read from `p`. -/
def Vc (ℓ v N : ℕ) (p : List Bool) : ℕ :=
  ((List.range N).map fun k => if Φ (k + ℓ) (p.take (k + ℓ)) % 2 ^ ℓ = v then 1 else 0).sum

/-- `4n·|V 2^ℓ − N| > 3 N 2^ℓ`, i.e. `|V/N − 2^{-ℓ}| > 3/(4n)`. -/
def fails (n ℓ v : ℕ) (p : List Bool) : Prop :=
  3 * n ^ 10 * 2 ^ ℓ < 4 * n * (Vc Φ ℓ v (n ^ 10) p * 2 ^ ℓ - n ^ 10 + (n ^ 10 - Vc Φ ℓ v (n ^ 10) p * 2 ^ ℓ))

instance (n ℓ v : ℕ) (p : List Bool) : Decidable (fails Φ n ℓ v p) := by
  unfold fails; infer_instance

/-- Number of failing blocks at level `n`. -/
def levelBad (n : ℕ) (p : List Bool) : ℕ :=
  ((List.range (n + 1)).map fun ℓ => if 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n then
    ((List.range (2 ^ ℓ)).map fun v => if fails Φ n ℓ v p then 1 else 0).sum else 0).sum

/-- The bad test of index `j`. -/
def badT (n₀ : ℕ) (j : ℕ) (p : List Bool) : Bool := decide (0 < levelBad Φ (j + n₀) p)

/-- Its depth. -/
def depth (n₀ j : ℕ) : ℕ := (j + n₀) ^ 10 + (j + n₀)

theorem primrec_pow : Primrec₂ fun a b : ℕ => a ^ b := by
  have : Primrec₂ fun (a : ℕ) (n : ℕ) => n.rec (motive := fun _ => ℕ) 1 fun _ ih => ih * a :=
    Primrec.nat_rec (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  refine this.of_eq fun a n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only at ih ⊢; rw [ih, pow_succ]

theorem primrec_Vc (hΦ : Primrec₂ Φ) :
    Primrec fun x : (ℕ × ℕ × ℕ) × List Bool => Vc Φ x.1.1 x.1.2.1 x.1.2.2 x.2 := by
  have hf : Primrec fun x : (ℕ × ℕ × ℕ) × List Bool => List.range x.1.2.2 :=
    Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hl : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ => y.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hv : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ => y.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hp : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ => y.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ => y.2 := Primrec.snd
  have hkl : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ => y.2 + y.1.1.1 :=
    Primrec.nat_add.comp hk hl
  have hval : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ =>
      Φ (y.2 + y.1.1.1) (y.1.2.take (y.2 + y.1.1.1)) % 2 ^ y.1.1.1 :=
    Primrec.nat_mod.comp (hΦ.comp hkl (Primrec.list_take.comp hkl hp))
      (primrec_pow.comp (Primrec.const 2) hl)
  have hg : Primrec fun y : ((ℕ × ℕ × ℕ) × List Bool) × ℕ =>
      if Φ (y.2 + y.1.1.1) (y.1.2.take (y.2 + y.1.1.1)) % 2 ^ y.1.1.1 = y.1.1.2.1 then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hval hv) (Primrec.const 1) (Primrec.const 0)
  exact (primrec_sum_map hf hg.to₂).of_eq fun x => rfl

theorem primrec_fails (hΦ : Primrec₂ Φ) :
    PrimrecPred fun x : (ℕ × ℕ × ℕ) × List Bool => fails Φ x.1.1 x.1.2.1 x.1.2.2 x.2 := by
  have hn : Primrec fun x : (ℕ × ℕ × ℕ) × List Bool => x.1.1 := Primrec.fst.comp Primrec.fst
  have hl : Primrec fun x : (ℕ × ℕ × ℕ) × List Bool => x.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hN : Primrec fun x : (ℕ × ℕ × ℕ) × List Bool => x.1.1 ^ 10 :=
    primrec_pow.comp hn (Primrec.const 10)
  have hP : Primrec fun x : (ℕ × ℕ × ℕ) × List Bool => 2 ^ x.1.2.1 :=
    primrec_pow.comp (Primrec.const 2) hl
  have hV : Primrec fun x : (ℕ × ℕ × ℕ) × List Bool =>
      Vc Φ x.1.2.1 x.1.2.2 (x.1.1 ^ 10) x.2 :=
    (primrec_Vc Φ hΦ).comp (Primrec.pair (Primrec.pair hl (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hN)) Primrec.snd)
  have hVP := Primrec.nat_mul.comp hV hP
  have lhs := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 3) hN) hP
  have rhs := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) hn)
    (Primrec.nat_add.comp (Primrec.nat_sub.comp hVP hN) (Primrec.nat_sub.comp hN hVP))
  exact (Primrec.nat_lt.comp lhs rhs).of_eq fun x => by unfold fails; rfl

attribute [local irreducible] fails in
theorem primrec_levelBad (hΦ : Primrec₂ Φ) :
    Primrec₂ (levelBad Φ) := by
  have hf : Primrec fun x : ℕ × List Bool => List.range (x.1 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have hn : Primrec fun y : (ℕ × List Bool) × ℕ => y.1.1 := Primrec.fst.comp Primrec.fst
  have hl : Primrec fun y : (ℕ × List Bool) × ℕ => y.2 := Primrec.snd
  have hP : Primrec fun y : (ℕ × List Bool) × ℕ => 2 ^ y.2 :=
    primrec_pow.comp (Primrec.const 2) hl
  -- inner sum over v
  have hin : Primrec fun y : (ℕ × List Bool) × ℕ =>
      ((List.range (2 ^ y.2)).map fun v => if fails Φ y.1.1 y.2 v y.1.2 then 1 else 0).sum := by
    have hpair : Primrec fun z : ((ℕ × List Bool) × ℕ) × ℕ =>
        ((z.1.1.1, z.1.2, z.2), z.1.1.2) :=
      Primrec.pair (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hpr : PrimrecPred fun z : ((ℕ × List Bool) × ℕ) × ℕ =>
        fails Φ z.1.1.1 z.1.2 z.2 z.1.1.2 :=
      ((primrec_fails Φ hΦ).comp hpair).of_eq fun z => Iff.rfl
    have hfv : Primrec fun z : ((ℕ × List Bool) × ℕ) × ℕ =>
        if fails Φ z.1.1.1 z.1.2 z.2 z.1.1.2 then 1 else 0 :=
      Primrec.ite hpr (Primrec.const 1) (Primrec.const 0)
    exact primrec_sum_map (Primrec.list_range.comp hP) hfv.to₂
  have hcond : PrimrecPred fun y : (ℕ × List Bool) × ℕ => 1 ≤ y.2 ∧ 2 ^ y.2 ≤ y.1.1 :=
    PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) hl) (Primrec.nat_le.comp hP hn)
  have hg : Primrec fun y : (ℕ × List Bool) × ℕ => if 1 ≤ y.2 ∧ 2 ^ y.2 ≤ y.1.1 then
      ((List.range (2 ^ y.2)).map fun v => if fails Φ y.1.1 y.2 v y.1.2 then 1 else 0).sum
      else 0 := Primrec.ite hcond hin (Primrec.const 0)
  have := primrec_sum_map hf hg.to₂
  exact this.to₂

theorem primrec_badT (hΦ : Primrec₂ Φ) (n₀ : ℕ) : Primrec₂ (badT Φ n₀) := by
  have h : Primrec fun x : ℕ × List Bool => levelBad Φ (x.1 + n₀) x.2 :=
    (primrec_levelBad Φ hΦ).comp (Primrec.nat_add.comp Primrec.fst (Primrec.const n₀)) Primrec.snd
  exact (Primrec.nat_lt.comp (Primrec.const 0) h).decide.to₂

theorem primrec_depth (n₀ : ℕ) : Primrec (depth n₀) := by
  have h : Primrec fun j : ℕ => j + n₀ := Primrec.nat_add.comp Primrec.id (Primrec.const n₀)
  exact Primrec.nat_add.comp (primrec_pow.comp h (Primrec.const 10)) h

/-- **Orbit block membership is a floor residue.** -/
theorem orbit_mem_iff (x : ℝ) (hx : 0 ≤ x) (k ℓ v : ℕ) :
    orbit 2 x k ∈ Set.Ico ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) ↔
      ⌊x * 2 ^ (k + ℓ)⌋₊ % 2 ^ ℓ = v := by
  set y := x * (2 : ℝ) ^ k with hydef
  have hy0 : 0 ≤ y := by positivity
  have horb : orbit 2 x k = Int.fract y := by simp [orbit, hydef]
  set f := Int.fract y
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hyf : y = (⌊y⌋₊ : ℝ) + f := by
    simp only [f, Int.fract]
    rw [← Int.natCast_floor_eq_floor hy0]; push_cast; ring
  have hP : (0 : ℝ) < 2 ^ ℓ := by positivity
  set b := ⌊f * 2 ^ ℓ⌋₊
  have hb : b < 2 ^ ℓ := by
    have : f * 2 ^ ℓ < (2 ^ ℓ : ℕ) := by push_cast; nlinarith
    exact (Nat.floor_lt (by positivity)).2 this
  have hfloor : ⌊x * 2 ^ (k + ℓ)⌋₊ = ⌊y⌋₊ * 2 ^ ℓ + b := by
    have : x * 2 ^ (k + ℓ) = f * 2 ^ ℓ + ((⌊y⌋₊ * 2 ^ ℓ : ℕ) : ℝ) := by
      rw [pow_add, ← mul_assoc, ← hydef]
      conv_lhs => rw [hyf]
      push_cast; ring
    rw [this, Nat.floor_add_natCast (by positivity)]
    ring
  rw [hfloor, Nat.mul_add_mod_of_lt hb, horb]
  rw [Set.mem_Ico, div_le_iff₀ hP, lt_div_iff₀ hP, eq_comm]
  simp only [b]
  rw [eq_comm, Nat.floor_eq_iff (by positivity)]

theorem take_pre (ω : ℕ → Bool) {m D : ℕ} (h : m ≤ D) : (pre ω D).take m = pre ω m := by
  unfold pre
  rw [← List.map_take, List.take_range, min_eq_left h]

/-- **The exact count is the visit count.** -/
theorem Vc_eq (G : (ℕ → Bool) → ℝ) (hG0 : ∀ ω, 0 ≤ G ω)
    (hfl : ∀ ω m, ⌊G ω * 2 ^ m⌋₊ = Φ m (pre ω m)) (ω : ℕ → Bool) (ℓ v N D : ℕ)
    (hD : N + ℓ ≤ D) :
    Vc Φ ℓ v N (pre ω D) =
      visitCount (orbit 2 (G ω)) ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) N := by
  classical
  unfold Vc visitCount
  rw [Finset.card_filter, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [take_pre ω (by omega), ← hfl]
    have := orbit_mem_iff (G ω) (hG0 ω) k ℓ v
    by_cases h : ⌊G ω * 2 ^ (k + ℓ)⌋₊ % 2 ^ ℓ = v
    · rw [if_pos h, if_pos (this.2 h)]
    · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

theorem cast_absdiff (a b : ℕ) : ((a - b + (b - a) : ℕ) : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (by
      have : (a : ℝ) ≤ b := by exact_mod_cast h
      linarith)]
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by
      have : (b : ℝ) ≤ a := by exact_mod_cast h
      linarith)]

theorem fails_imp {n ℓ v : ℕ} {p : List Bool} (hn : 1 ≤ n) (h : fails Φ n ℓ v p) :
    3 / (4 * (n : ℝ)) < |(Vc Φ ℓ v (n ^ 10) p : ℝ) / (n ^ 10 : ℕ) - 1 / 2 ^ ℓ| := by
  unfold fails at h
  have h' : ((3 * n ^ 10 * 2 ^ ℓ : ℕ) : ℝ) < ((4 * n * (Vc Φ ℓ v (n ^ 10) p * 2 ^ ℓ - n ^ 10 +
      (n ^ 10 - Vc Φ ℓ v (n ^ 10) p * 2 ^ ℓ)) : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_mul (4 * n), cast_absdiff] at h'
  push_cast at h'
  rw [Nat.cast_pow]
  set V : ℝ := (Vc Φ ℓ v (n ^ 10) p : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) ^ 10 := by positivity
  have hP : (0 : ℝ) < 2 ^ ℓ := by positivity
  have eq : V / (n : ℝ) ^ 10 - 1 / 2 ^ ℓ = (V * 2 ^ ℓ - n ^ 10) / ((n : ℝ) ^ 10 * 2 ^ ℓ) := by
    field_simp
  rw [eq, abs_div, abs_of_pos (show (0:ℝ) < (n : ℝ) ^ 10 * 2 ^ ℓ by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith


instance : IsProbabilityMeasure coins := by unfold coins; infer_instance

/-- The decay constant appearing in `visit_deviation`. -/
noncomputable def Kc (C δ : ℝ) : ℝ := C * 2 ^ δ * ((1 - (2 : ℝ) ^ (-δ / 2))⁻¹) ^ 2

theorem Kc_nonneg {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) : 0 ≤ Kc C δ := by
  unfold Kc; positivity

theorem block_bound (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂coins‖ ≤ C * |ξ| ^ (-δ))
    (hfl : ∀ ω m, ⌊G ω * 2 ^ m⌋₊ = Φ m (pre ω m)) (c₁ : ℝ)
    (hc₁ : 64 / 3 * Real.sqrt (1 + Kc C δ) ≤ c₁) {n ℓ v : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓn : 2 ^ ℓ ≤ n) (hv : v < 2 ^ ℓ) :
    coins.real {ω | fails Φ n ℓ v (pre ω (n ^ 10 + n))} ≤ c₁ / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hP : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hℓle : ℓ ≤ n := (Nat.lt_two_pow_self).le.trans hℓn
  have hvR : (v : ℝ) + 1 ≤ 2 ^ ℓ := by exact_mod_cast hv
  have hP2 : (2 : ℝ) ≤ 2 ^ ℓ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have hsub : {ω | fails Φ n ℓ v (pre ω (n ^ 10 + n))} ⊆
      {ω | 2 * (1 / (4 * (n : ℝ))) + 1 / (4 * (n : ℝ)) <
        |(visitCount (orbit 2 (G ω)) ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) (n ^ 10) : ℝ) /
          ((n ^ 10 : ℕ) : ℝ) - ((v + 1 : ℝ) / 2 ^ ℓ - (v : ℝ) / 2 ^ ℓ)|} := by
    intro ω hω
    have := fails_imp Φ hn hω
    rw [Vc_eq Φ G hG0 hfl ω ℓ v (n ^ 10) _ (by omega)] at this
    simp only [Set.mem_ofPred_eq]
    have e1 : (v + 1 : ℝ) / 2 ^ ℓ - (v : ℝ) / 2 ^ ℓ = 1 / 2 ^ ℓ := by ring
    have e2 : 2 * (1 / (4 * (n : ℝ))) + 1 / (4 * (n : ℝ)) = 3 / (4 * n) := by ring
    rw [e1, e2]; exact this
  refine (measureReal_mono hsub).trans ?_
  have hN1 : 1 ≤ n ^ 10 := Nat.one_le_pow _ _ hn
  refine (visit_deviation coins G hGm hC hδ hdec ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) (1 / (4 * (n : ℝ))) (1 / (4 * (n : ℝ)))
    (by positivity) (by gcongr; linarith) (by rw [div_le_one hP]; exact hvR)
    (by rw [← sub_div, show (v + 1 : ℝ) - v = 1 by ring, div_le_div_iff₀ hP (by norm_num)]; linarith)
    (by positivity) (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    (by positivity) (n ^ 10) hN1).trans ?_
  have hK := Kc_nonneg hC hδ
  change 2 * (2 / (3 * (1 / (4 * (n : ℝ)))) / (1 / (4 * (n : ℝ))) *
    Real.sqrt ((((n ^ 10 : ℕ) : ℝ) + Kc C δ) / ((n ^ 10 : ℕ) : ℝ) ^ 2)) ≤ c₁ / (n : ℝ) ^ 3
  push_cast
  have hsq : Real.sqrt (((n : ℝ) ^ 10 + Kc C δ) / ((n : ℝ) ^ 10) ^ 2) ≤
      Real.sqrt (1 + Kc C δ) / (n : ℝ) ^ 5 := by
    rw [show Real.sqrt (1 + Kc C δ) / (n : ℝ) ^ 5 = Real.sqrt ((1 + Kc C δ) / ((n : ℝ) ^ 5) ^ 2) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have h10 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ hnR
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((n : ℝ) ^ 10) ^ 2 = (n : ℝ) ^ 10 * ((n : ℝ) ^ 5) ^ 2 := by ring
    rw [this]
    have h5 : (0 : ℝ) < ((n : ℝ) ^ 5) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h10 hK]
  have e : 2 * (2 / (3 * (1 / (4 * (n : ℝ)))) / (1 / (4 * (n : ℝ)))) = 64 / 3 * (n : ℝ) ^ 2 := by
    field_simp; ring
  rw [← mul_assoc, e]
  calc 64 / 3 * (n : ℝ) ^ 2 * Real.sqrt (((n : ℝ) ^ 10 + Kc C δ) / ((n : ℝ) ^ 10) ^ 2)
      ≤ 64 / 3 * (n : ℝ) ^ 2 * (Real.sqrt (1 + Kc C δ) / (n : ℝ) ^ 5) := by gcongr
    _ = 64 / 3 * Real.sqrt (1 + Kc C δ) / (n : ℝ) ^ 3 := by field_simp
    _ ≤ c₁ / (n : ℝ) ^ 3 := by gcongr


theorem geom_two (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem sum_blocks_le (n : ℕ) :
    ∑ ℓ ∈ (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n), 2 ^ ℓ ≤ 2 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsub : (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n) ⊆
      Finset.range (Nat.log 2 n + 1) := by
    intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_range] at hℓ ⊢
    have := Nat.le_log_of_pow_le (by norm_num) hℓ.2.2
    omega
  refine (Finset.sum_le_sum_of_subset hsub).trans ?_
  have h1 := geom_two (Nat.log 2 n + 1)
  have h2 := Nat.pow_log_le_self 2 hn.ne'
  rw [pow_succ] at h1
  omega

theorem levelBad_pos {n : ℕ} {p : List Bool} (h : 0 < levelBad Φ n p) :
    ∃ ℓ ∈ (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n),
      ∃ v ∈ Finset.range (2 ^ ℓ), fails Φ n ℓ v p := by
  by_contra hne
  push Not at hne
  apply h.ne'
  unfold levelBad
  refine List.sum_eq_zero fun x hx => ?_
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨ℓ, hℓ, rfl⟩ := hx
  split_ifs with hc
  · refine List.sum_eq_zero fun y hy => ?_
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    rw [if_neg (hne ℓ (by simp [hℓ, hc]) v (by simpa using hv))]
  · rfl

theorem level_bound (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂coins‖ ≤ C * |ξ| ^ (-δ))
    (hfl : ∀ ω m, ⌊G ω * 2 ^ m⌋₊ = Φ m (pre ω m)) (c₁ : ℝ)
    (hc₁ : 64 / 3 * Real.sqrt (1 + Kc C δ) ≤ c₁) {n : ℕ} (hn : 1 ≤ n) :
    coins.real {ω | 0 < levelBad Φ n (pre ω (n ^ 10 + n))} ≤ 2 * c₁ / (n : ℝ) ^ 2 := by
  set S := (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n)
  have hsub : {ω | 0 < levelBad Φ n (pre ω (n ^ 10 + n))} ⊆
      ⋃ ℓ ∈ S, ⋃ v ∈ Finset.range (2 ^ ℓ), {ω | fails Φ n ℓ v (pre ω (n ^ 10 + n))} := by
    intro ω hω
    obtain ⟨ℓ, hℓ, v, hv, hf⟩ := levelBad_pos Φ hω
    simp only [Set.mem_iUnion]
    exact ⟨ℓ, hℓ, v, hv, hf⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc₁0 : 0 ≤ c₁ := le_trans (by positivity) hc₁
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ ℓ ∈ S, coins.real (⋃ v ∈ Finset.range (2 ^ ℓ), {ω | fails Φ n ℓ v (pre ω (n ^ 10 + n))})
      ≤ ∑ ℓ ∈ S, ((2 ^ ℓ : ℕ) : ℝ) * (c₁ / (n : ℝ) ^ 3) := by
        refine Finset.sum_le_sum fun ℓ hℓ => (measureReal_biUnion_finset_le _ _).trans ?_
        simp only [S, Finset.mem_filter, Finset.mem_range] at hℓ
        calc ∑ v ∈ Finset.range (2 ^ ℓ), coins.real {ω | fails Φ n ℓ v (pre ω (n ^ 10 + n))}
            ≤ ∑ v ∈ Finset.range (2 ^ ℓ), c₁ / (n : ℝ) ^ 3 :=
              Finset.sum_le_sum fun v hv => block_bound Φ G hGm hG0 hC hδ hdec hfl c₁ hc₁ hn
                hℓ.2.1 hℓ.2.2 (Finset.mem_range.1 hv)
          _ = _ := by simp
    _ = ((∑ ℓ ∈ S, 2 ^ ℓ : ℕ) : ℝ) * (c₁ / (n : ℝ) ^ 3) := by rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ((2 * n : ℕ) : ℝ) * (c₁ / (n : ℝ) ^ 3) := by
        gcongr; exact_mod_cast sum_blocks_le n
    _ = 2 * c₁ / (n : ℝ) ^ 2 := by push_cast; field_simp

theorem tele_sum (a m M : ℕ) (hm : 2 ≤ a + m) :
    ∑ j ∈ Finset.range M, (if a ≤ j then (1 : ℝ) / ((j : ℝ) + m) ^ 2 else 0) ≤
      1 / ((a : ℝ) + m - 1) - 1 / ((max a M : ℕ) + (m : ℝ) - 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hm' : (2 : ℝ) ≤ a + m := by exact_mod_cast hm
    by_cases h : a ≤ M
    · rw [if_pos h]
      have e1 : max a M = M := max_eq_right h
      have e2 : max a (M + 1) = M + 1 := max_eq_right (by omega)
      rw [e1] at ih; rw [e2]; push_cast
      have hM : (a : ℝ) ≤ M := by exact_mod_cast h
      have hp : (1 : ℝ) ≤ (M : ℝ) + m - 1 := by linarith
      have key : 1 / ((M : ℝ) + m) ^ 2 ≤ 1 / ((M : ℝ) + m - 1) - 1 / ((M : ℝ) + 1 + m - 1) := by
        rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      linarith
    · rw [if_neg h]
      have e1 : max a M = a := max_eq_left (by omega)
      have e2 : max a (M + 1) = a := max_eq_left (by omega)
      rw [e1] at ih; rw [e2]; linarith

theorem tsum_tail_le (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (B : ℝ) (hB : 0 ≤ B) (a m : ℕ)
    (hm : 2 ≤ a + m) (hle : ∀ j, a ≤ j → f j ≤ B / ((j : ℝ) + m) ^ 2) :
    Summable (fun j => if a ≤ j then f j else 0) ∧
      ∑' j, (if a ≤ j then f j else 0) ≤ B / ((a : ℝ) + m - 1) := by
  have hm' : (2 : ℝ) ≤ a + m := by exact_mod_cast hm
  have hnn : ∀ j, 0 ≤ (if a ≤ j then f j else 0) := fun j => by split_ifs <;> simp [hf]
  have hs : ∀ M, ∑ j ∈ Finset.range M, (if a ≤ j then f j else 0) ≤ B / ((a : ℝ) + m - 1) := by
    intro M
    calc ∑ j ∈ Finset.range M, (if a ≤ j then f j else 0)
        ≤ ∑ j ∈ Finset.range M, B * (if a ≤ j then (1 : ℝ) / ((j : ℝ) + m) ^ 2 else 0) := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs with h
          · rw [mul_one_div]; exact hle j h
          · simp
      _ = B * ∑ j ∈ Finset.range M, (if a ≤ j then (1 : ℝ) / ((j : ℝ) + m) ^ 2 else 0) := by
          rw [Finset.mul_sum]
      _ ≤ B * (1 / ((a : ℝ) + m - 1)) := by
          gcongr
          refine (tele_sum a m M hm).trans ?_
          have : (0 : ℝ) ≤ 1 / ((max a M : ℕ) + (m : ℝ) - 1) := by
            have : (a : ℝ) ≤ (max a M : ℕ) := by exact_mod_cast le_max_left a M
            apply div_nonneg zero_le_one; linarith
          linarith
      _ = B / ((a : ℝ) + m - 1) := by ring
  exact ⟨summable_of_sum_range_le hnn hs, Real.tsum_le_of_sum_range_le hnn hs⟩

theorem dens_badT (n₀ j : ℕ) :
    dens (badT Φ n₀) (depth n₀) j [] =
      coins.real {ω | 0 < levelBad Φ (j + n₀) (pre ω (depth n₀ j))} := by
  unfold dens
  simp only [List.length_nil, Nat.sub_zero]
  rw [← coins_pre]
  rw [measureReal_def]
  congr 2
  ext ω
  simp [badAt, badT, List.take_of_length_le (le_of_eq (length_pre ω _))]


theorem visitCount_mono_n (u : ℕ → ℝ) (a c : ℝ) : Monotone (visitCount u a c) := by
  intro m n hmn
  unfold visitCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hmn))

theorem pow10_ratio (a : ℝ) (ha : 1 < a) :
    ∀ᶠ n : ℕ in atTop, (((n + 1) ^ 10 : ℕ) : ℝ) ≤ a * ((n ^ 10 : ℕ) : ℝ) := by
  have h : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ 10) atTop (𝓝 ((1 + 0) ^ 10)) :=
    (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).pow 10
  rw [add_zero, one_pow] at h
  filter_upwards [h.eventually (gt_mem_nhds ha), eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  push_cast
  have : ((n : ℝ) + 1) ^ 10 = (1 + 1 / (n : ℝ)) ^ 10 * (n : ℝ) ^ 10 := by
    rw [← mul_pow]; congr 1; field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right hn.le (by positivity)

theorem normal_of_good (x : ℝ) (n₀ : ℕ)
    (hgood : ∀ n, n₀ ≤ n → 1 ≤ n → ∀ ℓ, 1 ≤ ℓ → 2 ^ ℓ ≤ n → ∀ v : ℕ, v < 2 ^ ℓ →
      |(visitCount (orbit 2 x) ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) (n ^ 10) : ℝ) /
        ((n ^ 10 : ℕ) : ℝ) - 1 / 2 ^ ℓ| ≤ 3 / (4 * (n : ℝ))) :
    IsNormal 2 x := by
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl]
  refine equidistributed_of_badic 2 le_rfl _ fun ℓ hℓ v hv => ?_
  simp only [Nat.cast_ofNat]
  refine tendsto_div_of_monotone_of_exists_subseq_tendsto_div _ _
    (fun m n h => by exact_mod_cast visitCount_mono_n _ _ _ h) fun a ha =>
      ⟨fun n => n ^ 10, pow10_ratio a ha, ?_, ?_⟩
  · exact tendsto_id.comp (tendsto_pow_atTop (by norm_num))
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => 3 / (4 * (n : ℝ))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (3 / 4 : ℝ))).mul tendsto_one_div_atTop_nhds_zero_nat
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      ring
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop (max n₀ (max 1 (2 ^ ℓ)))] with n hn
    simp only [Real.norm_eq_abs, abs_abs]
    exact hgood n (le_of_max_le_left hn) (le_of_max_le_left (le_of_max_le_right hn)) ℓ hℓ
      (le_of_max_le_right (le_of_max_le_right hn)) v hv


theorem not_fails_imp {n ℓ v : ℕ} {p : List Bool} (hn : 1 ≤ n) (h : ¬ fails Φ n ℓ v p) :
    |(Vc Φ ℓ v (n ^ 10) p : ℝ) / (n ^ 10 : ℕ) - 1 / 2 ^ ℓ| ≤ 3 / (4 * (n : ℝ)) := by
  unfold fails at h
  push Not at h
  have h' : ((4 * n * (Vc Φ ℓ v (n ^ 10) p * 2 ^ ℓ - n ^ 10 +
      (n ^ 10 - Vc Φ ℓ v (n ^ 10) p * 2 ^ ℓ)) : ℕ) : ℝ) ≤ ((3 * n ^ 10 * 2 ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_mul (4 * n), cast_absdiff] at h'
  push_cast at h'
  rw [Nat.cast_pow]
  set V : ℝ := (Vc Φ ℓ v (n ^ 10) p : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) ^ 10 := by positivity
  have hP : (0 : ℝ) < 2 ^ ℓ := by positivity
  have eq : V / (n : ℝ) ^ 10 - 1 / 2 ^ ℓ = (V * 2 ^ ℓ - n ^ 10) / ((n : ℝ) ^ 10 * 2 ^ ℓ) := by
    field_simp
  rw [eq, abs_div, abs_of_pos (show (0:ℝ) < (n : ℝ) ^ 10 * 2 ^ ℓ by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem levelBad_pos_of_fails {n ℓ v : ℕ} {p : List Bool} (hℓ : 1 ≤ ℓ) (hℓn : 2 ^ ℓ ≤ n)
    (hv : v < 2 ^ ℓ) (h : fails Φ n ℓ v p) : 0 < levelBad Φ n p := by
  have hℓle : ℓ ≤ n := (Nat.lt_two_pow_self).le.trans hℓn
  unfold levelBad
  refine lt_of_lt_of_le ?_ (List.le_sum_of_mem (List.mem_map.2 ⟨ℓ, List.mem_range.2 (by omega), rfl⟩))
  rw [if_pos ⟨hℓ, hℓn⟩]
  refine lt_of_lt_of_le ?_ (List.le_sum_of_mem (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩))
  rw [if_pos h]; exact Nat.one_pos


/-- **Generic computable normality.** -/
theorem exists_computable_normal_of_digits (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂coins‖ ≤ C * |ξ| ^ (-δ))
    (hΦ : Primrec₂ Φ) (hfl : ∀ ω m, ⌊G ω * 2 ^ m⌋₊ = Φ m (pre ω m)) :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (G e) := by
  set c₁ : ℕ := ⌈64 / 3 * Real.sqrt (1 + Kc C δ)⌉₊ + 1 with hc₁def
  have hc₁ : 64 / 3 * Real.sqrt (1 + Kc C δ) ≤ (c₁ : ℝ) := by
    rw [hc₁def]; push_cast; linarith [Nat.le_ceil (64 / 3 * Real.sqrt (1 + Kc C δ))]
  have hc₁1 : 1 ≤ c₁ := by omega
  have hc₁R : (1 : ℝ) ≤ c₁ := by exact_mod_cast hc₁1
  set n₀ : ℕ := 8 * c₁ + 2 with hn₀
  set J : ℕ → ℕ := fun k => 2 * c₁ * 8 ^ (k + 1) with hJdef
  have hJ : Primrec J :=
    Primrec.nat_mul.comp (Primrec.const _) (primrec_pow.comp (Primrec.const 8) Primrec.succ)
  have hdj : ∀ j, dens (badT Φ n₀) (depth n₀) j [] ≤ 2 * (c₁ : ℝ) / ((j : ℝ) + n₀) ^ 2 := by
    intro j
    rw [dens_badT]
    have := level_bound Φ G hGm hG0 hC hδ hdec hfl c₁ hc₁ (n := j + n₀) (by omega)
    simpa [depth] using this
  have hnn : ∀ j, 0 ≤ dens (badT Φ n₀) (depth n₀) j [] := fun j => dens_nonneg j []
  have hB : (0 : ℝ) ≤ 2 * c₁ := by positivity
  obtain ⟨hs0, ht0⟩ := tsum_tail_le _ hnn (2 * c₁) hB 0 n₀ (by omega)
    (fun j _ => hdj j)
  simp only [zero_le, if_true, Nat.cast_zero, zero_add] at hs0 ht0
  have htot : ∑' j, dens (badT Φ n₀) (depth n₀) j [] ≤ 1 / 4 := by
    refine ht0.trans ?_
    rw [div_le_div_iff₀ (by rw [hn₀]; push_cast; linarith) (by norm_num), hn₀]
    push_cast; linarith
  have htail : ∀ k, ∑' j, (if J k < j then dens (badT Φ n₀) (depth n₀) j [] else 0) ≤
      (1 / 8 : ℝ) ^ (k + 1) := by
    intro k
    obtain ⟨_, ht⟩ := tsum_tail_le _ hnn (2 * c₁) hB (J k + 1) n₀ (by omega)
      (fun j _ => hdj j)
    have e : (fun j => if J k < j then dens (badT Φ n₀) (depth n₀) j [] else 0) =
        fun j => if J k + 1 ≤ j then dens (badT Φ n₀) (depth n₀) j [] else 0 := by
      funext j; simp only [Nat.lt_iff_add_one_le]
    rw [e]
    refine ht.trans ?_
    have h8 : (0 : ℝ) < 8 ^ (k + 1) := by positivity
    have hJR : ((J k : ℕ) : ℝ) = 2 * c₁ * 8 ^ (k + 1) := by simp [hJdef]
    have hn0R : (0 : ℝ) ≤ n₀ := by positivity
    have hden : (0 : ℝ) < ((J k + 1 : ℕ) : ℝ) + n₀ - 1 := by
      push_cast; rw [hJR]; nlinarith
    rw [div_pow, one_pow, div_le_div_iff₀ hden h8]
    push_cast; rw [hJR]
    have : (0 : ℝ) ≤ n₀ := by positivity
    nlinarith
  obtain ⟨e, hce, hav⟩ := exists_primrec_avoid (badT Φ n₀) (primrec_badT Φ hΦ n₀) (depth n₀)
    (primrec_depth n₀) J hJ hs0 htot htail
  refine ⟨e, hce, normal_of_good (G e) n₀ fun n hn hn1 ℓ hℓ hℓn v hv => ?_⟩
  have hbad0 := hav (n - n₀)
  unfold badT depth at hbad0
  rw [show n - n₀ + n₀ = n by omega] at hbad0
  have hbad : levelBad Φ n (pre e (n ^ 10 + n)) = 0 := by
    have := of_decide_eq_false hbad0; omega
  have hnf : ¬ fails Φ n ℓ v (pre e (n ^ 10 + n)) := fun hf =>
    (levelBad_pos_of_fails Φ hℓ hℓn hv hf).ne' hbad
  have hℓle : ℓ ≤ n := (Nat.lt_two_pow_self).le.trans hℓn
  have := not_fails_imp Φ hn1 hnf
  rwa [Vc_eq Φ G hG0 hfl e ℓ v (n ^ 10) _ (by omega)] at this

end NormalNumbers.ComputableNormal
