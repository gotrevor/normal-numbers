/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Derandomize
import NormalNumbers.VisitDeviation
import NormalNumbers.Sandwich

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

/-- **Generic computable normality.** -/
theorem exists_computable_normal_of_digits (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖∫ ω, ee (ξ * G ω) ∂coins‖ ≤ C * |ξ| ^ (-δ))
    (hΦ : Primrec₂ Φ) (hfl : ∀ ω m, ⌊G ω * 2 ^ m⌋₊ = Φ m (pre ω m)) :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (G e) := by
  sorry

end NormalNumbers.ComputableNormal
