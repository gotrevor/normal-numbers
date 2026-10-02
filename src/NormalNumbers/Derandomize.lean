/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Derandomization by conditional expectations

A countable family of *clopen* bad events `B_j = {ω : bad j (ω|d_j) = true}` on fair coins, each
decided by the first `d_j` coins, with total mass `≤ 1/4` and a **computable** tail modulus `J`
(`Σ_{j > J k} μ(B_j) ≤ 8^{-(k+1)}`), is avoided by a **computable** coin sequence
(`exists_primrec_avoid`).

Algorithm (method of conditional expectations, finitized): having fixed `p = e|k`, set
`e k := b` minimizing `Σ_{j ≤ J k} μ(B_j | p b)`, a dyadic rational computed by exact counting.
The full potential `Φ(p) = Σ_j μ(B_j | p)` then rises by at most the tail
`Σ_{j > J k} μ(B_j | p b) ≤ 2^{k+1} 8^{-(k+1)} = 4^{-(k+1)}` per step, so `Φ < 1/4 + 1/3 < 1`
forever; once `k ≥ d_j`, `μ(B_j | e|k) ∈ {0,1}`, hence `= 0`.

This is the Becher–Figueira / Becher–Lew Deveali derandomization with the tails made explicit.
-/

namespace NormalNumbers.Derandomize

/-- All bit strings of length `m`. -/
def allStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allStrings m).flatMap fun s => [false :: s, true :: s]

/-- Number of length-`m` completions `s` of `p` with `P (p ++ s)`. -/
def cnt (P : List Bool → Bool) (m : ℕ) (p : List Bool) : ℕ :=
  ((allStrings m).map fun s => if P (p ++ s) then 1 else 0).sum

/-- Test `j` reads only the first `d j` bits. -/
def badAt (bad : ℕ → List Bool → Bool) (d : ℕ → ℕ) (j : ℕ) (p : List Bool) : Bool :=
  bad j (p.take (d j))

/-- Conditional mass of `B_j` given the prefix `p`. -/
noncomputable def dens (bad : ℕ → List Bool → Bool) (d : ℕ → ℕ) (j : ℕ) (p : List Bool) : ℝ :=
  (cnt (badAt bad d j) (d j - p.length) p : ℝ) / 2 ^ (d j - p.length)

/-- First `n` coins. -/
def pre (e : ℕ → Bool) (n : ℕ) : List Bool := (List.range n).map e

/-- Fair coins. -/
noncomputable def coins : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- **Mass of a prefix event** equals the exact count. -/
theorem coins_pre (P : List Bool → Bool) (n : ℕ) :
    (coins {ω | P (pre ω n) = true}).toReal = (cnt P n [] : ℝ) / 2 ^ n := by
  sorry

end NormalNumbers.Derandomize

namespace NormalNumbers.Derandomize

theorem primrec_pow2 : Primrec fun n : ℕ => 2 ^ n := by
  have : Primrec (fun n : ℕ => n.rec (motive := fun _ => ℕ) 1 fun _ ih => 2 * ih) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂
  refine this.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only at ih ⊢; rw [ih, pow_succ, mul_comm]

theorem primrec_allStrings : Primrec allStrings := by
  have : Primrec (fun n : ℕ => n.rec (motive := fun _ => List (List Bool)) [[]]
      fun _ l => l.flatMap fun s => [false :: s, true :: s]) := by
    have hs : Primrec (fun x : (ℕ × List (List Bool)) × List Bool => x.2) := Primrec.snd
    have h1 : Primrec (fun x : (ℕ × List (List Bool)) × List Bool => false :: x.2) :=
      Primrec.list_cons.comp (Primrec.const false) hs
    have h2 : Primrec (fun x : (ℕ × List (List Bool)) × List Bool => true :: x.2) :=
      Primrec.list_cons.comp (Primrec.const true) hs
    have h3 : Primrec (fun x : (ℕ × List (List Bool)) × List Bool => [true :: x.2]) :=
      Primrec.list_cons.comp h2 (Primrec.const ([] : List (List Bool)))
    have h4 : Primrec₂ (fun (_ : ℕ × List (List Bool)) (s : List Bool) =>
        [false :: s, true :: s]) := (Primrec.list_cons.comp h1 h3).to₂
    have h5 : Primrec (fun x : ℕ × List (List Bool) =>
        x.2.flatMap fun s => [false :: s, true :: s]) :=
      Primrec.list_flatMap Primrec.snd h4
    exact Primrec.nat_rec₁ [[]] h5.to₂
  refine this.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [allStrings] at ih ⊢; rw [ih]


theorem primrec_sum_map {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {g : α → β → ℕ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => ((f a).map (g a)).sum := by
  have : Primrec fun a => ((f a).map (g a)).foldr (fun b s => b + s) 0 :=
    Primrec.list_foldr (Primrec.list_map hf hg) (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  refine this.of_eq fun a => ?_
  induction (f a).map (g a) with
  | nil => rfl
  | cons x l ih => simp [ih]

variable (bad : ℕ → List Bool → Bool) (d : ℕ → ℕ) (J : ℕ → ℕ)

/-- Exact count for test `j` at prefix `q`. -/
def cntJ (j : ℕ) (q : List Bool) : ℕ := cnt (badAt bad d j) (d j - q.length) q

/-- Common exponent at stage `k`. -/
def bigS (k : ℕ) : ℕ := ((List.range (J k + 1)).map d).sum

/-- `2^{bigS k}` times the truncated potential `Σ_{j ≤ J k} dens j q`. -/
def W (k : ℕ) (q : List Bool) : ℕ :=
  ((List.range (J k + 1)).map fun j => cntJ bad d j q * 2 ^ (bigS d J k - (d j - q.length))).sum

/-- The greedy bit. -/
def choose (k : ℕ) (p : List Bool) : Bool :=
  decide (W bad d J k (p ++ [true]) < W bad d J k (p ++ [false]))

/-- The greedy prefixes. -/
def preA : ℕ → List Bool
  | 0 => []
  | k + 1 => preA k ++ [choose bad d J k (preA k)]

/-- The derandomized coin sequence. -/
def algo (k : ℕ) : Bool := choose bad d J k (preA bad d J k)

section Primrec

variable {bad d J}

theorem primrec_cnt (hbad : Primrec₂ bad) (hd : Primrec d) :
    Primrec fun x : ℕ × ℕ × List Bool => cnt (badAt bad d x.1) x.2.1 x.2.2 := by
  have hf : Primrec fun x : ℕ × ℕ × List Bool => allStrings x.2.1 :=
    primrec_allStrings.comp (Primrec.fst.comp Primrec.snd)
  have hc : Primrec fun y : (ℕ × ℕ × List Bool) × List Bool =>
      bad y.1.1 ((y.1.2.2 ++ y.2).take (d y.1.1)) := by
    refine hbad.comp (Primrec.fst.comp Primrec.fst) ?_
    exact Primrec.list_take.comp (hd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hg : Primrec₂ fun (x : ℕ × ℕ × List Bool) (s : List Bool) =>
      (bif bad x.1 ((x.2.2 ++ s).take (d x.1)) then 1 else 0 : ℕ) :=
    (Primrec.cond hc (Primrec.const 1) (Primrec.const 0)).to₂
  refine (primrec_sum_map hf hg).of_eq fun x => ?_
  unfold cnt badAt
  congr 1
  refine List.map_congr_left fun s _ => ?_
  cases bad x.1 ((x.2.2 ++ s).take (d x.1)) <;> rfl

theorem primrec_cntJ (hbad : Primrec₂ bad) (hd : Primrec d) :
    Primrec₂ (cntJ bad d) := by
  have := (primrec_cnt hbad hd).comp (Primrec.pair Primrec.fst (Primrec.pair
    (Primrec.nat_sub.comp (hd.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))
    Primrec.snd))
  exact this.to₂

theorem primrec_bigS (hd : Primrec d) (hJ : Primrec J) : Primrec (bigS d J) := by
  have hf : Primrec fun k : ℕ => List.range (J k + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hJ)
  exact primrec_sum_map hf (hd.comp Primrec.snd).to₂

theorem primrec_W (hbad : Primrec₂ bad) (hd : Primrec d) (hJ : Primrec J) :
    Primrec₂ (W bad d J) := by
  have hf : Primrec fun x : ℕ × List Bool => List.range (J x.1 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (hJ.comp Primrec.fst))
  have hg : Primrec₂ fun (x : ℕ × List Bool) (j : ℕ) =>
      cntJ bad d j x.2 * 2 ^ (bigS d J x.1 - (d j - x.2.length)) := by
    have hq : Primrec fun y : (ℕ × List Bool) × ℕ => y.1.2 := Primrec.snd.comp Primrec.fst
    have hk : Primrec fun y : (ℕ × List Bool) × ℕ => y.1.1 := Primrec.fst.comp Primrec.fst
    have hj : Primrec fun y : (ℕ × List Bool) × ℕ => y.2 := Primrec.snd
    have hy : Primrec fun y : (ℕ × List Bool) × ℕ =>
        cntJ bad d y.2 y.1.2 * 2 ^ (bigS d J y.1.1 - (d y.2 - y.1.2.length)) := by
      refine Primrec.nat_mul.comp ((primrec_cntJ hbad hd).comp hj hq) (primrec_pow2.comp ?_)
      exact Primrec.nat_sub.comp ((primrec_bigS hd hJ).comp hk)
        (Primrec.nat_sub.comp (hd.comp hj) (Primrec.list_length.comp hq))
    exact hy.to₂
  exact (primrec_sum_map hf hg).to₂

theorem primrec_choose (hbad : Primrec₂ bad) (hd : Primrec d) (hJ : Primrec J) :
    Primrec₂ (choose bad d J) := by
  have hW := primrec_W hbad hd hJ
  have h1 : Primrec fun x : ℕ × List Bool => W bad d J x.1 (x.2 ++ [true]) :=
    hW.comp Primrec.fst (Primrec.list_concat.comp Primrec.snd (Primrec.const true))
  have h2 : Primrec fun x : ℕ × List Bool => W bad d J x.1 (x.2 ++ [false]) :=
    hW.comp Primrec.fst (Primrec.list_concat.comp Primrec.snd (Primrec.const false))
  exact (Primrec.nat_lt.comp h1 h2).decide.to₂

theorem primrec_preA (hbad : Primrec₂ bad) (hd : Primrec d) (hJ : Primrec J) :
    Primrec (preA bad d J) := by
  have hg : Primrec₂ fun (k : ℕ) (l : List Bool) => l ++ [choose bad d J k l] :=
    (Primrec.list_concat.comp Primrec.snd
      ((primrec_choose hbad hd hJ).comp Primrec.fst Primrec.snd)).to₂
  refine (Primrec.nat_rec₁ [] hg).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [preA] at ih ⊢; rw [← ih]

theorem computable_algo (hbad : Primrec₂ bad) (hd : Primrec d) (hJ : Primrec J) :
    Computable (algo bad d J) :=
  ((primrec_choose hbad hd hJ).comp Primrec.id (primrec_preA hbad hd hJ)).to_comp

end Primrec

/-- **Computable avoidance.** -/
theorem exists_primrec_avoid (bad : ℕ → List Bool → Bool) (hbad : Primrec₂ bad)
    (d : ℕ → ℕ) (hd : Primrec d) (J : ℕ → ℕ) (hJ : Primrec J)
    (hsum : Summable fun j => dens bad d j [])
    (htot : ∑' j, dens bad d j [] ≤ 1 / 4)
    (htail : ∀ k, ∑' j, (if J k < j then dens bad d j [] else 0) ≤ (1 / 8 : ℝ) ^ (k + 1)) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ j, bad j (pre e (d j)) = false := by
  sorry

end NormalNumbers.Derandomize
