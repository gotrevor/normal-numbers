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
theorem mem_allStrings (n : ℕ) (s : List Bool) : s ∈ allStrings n ↔ s.length = n := by
  induction n generalizing s with
  | zero => simp [allStrings, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [allStrings, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨t, ht, rfl | rfl⟩ <;> simp [(ih t).1 ht]
    · intro hs
      cases s with
      | nil => simp at hs
      | cons b t =>
        refine ⟨t, (ih t).2 (by simpa using hs), ?_⟩
        cases b <;> simp

theorem nodup_allStrings (n : ℕ) : (allStrings n).Nodup := by
  induction n with
  | zero => simp [allStrings]
  | succ n ih =>
    simp only [allStrings]
    rw [List.nodup_flatMap]
    refine ⟨fun s _ => by simp, ?_⟩
    refine ih.pairwise_of_forall_ne fun a _ b _ hab => ?_
    simp only [Function.onFun, List.disjoint_cons_left, List.disjoint_cons_right,
      List.mem_cons, List.not_mem_nil, or_false, List.disjoint_nil_left]
    simp [Ne.symm hab]

theorem length_pre (e : ℕ → Bool) (n : ℕ) : (pre e n).length = n := by simp [pre]

theorem pre_eq_iff {n : ℕ} (ω : ℕ → Bool) (s : List Bool) (hs : s.length = (n : ℕ)) :
    pre ω n = s ↔ ω ∈ Set.pi (Finset.range n : Set ℕ) fun i => {s.getD i false} := by
  constructor
  · rintro rfl i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    simp [pre, hi]
  · intro h
    refine List.ext_getElem (by rw [length_pre, hs]) fun i h1 h2 => ?_
    have := h i (by simpa [length_pre] using h1)
    simp only [Set.mem_singleton_iff] at this
    rw [List.getD_eq_getElem _ _ h2] at this
    simp [pre, this]

theorem coins_cyl (s : List Bool) :
    coins {ω | pre ω s.length = s} = (1 / 2 : ENNReal) ^ s.length := by
  have : {ω | pre ω s.length = s} =
      Set.pi (Finset.range s.length : Set ℕ) fun i => {s.getD i false} := by
    ext ω; exact pre_eq_iff ω s rfl
  rw [this, coins]
  have h := MeasureTheory.Measure.infinitePi_pi
    (μ := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) (s := Finset.range s.length)
    (t := fun i => {s.getD i false}) (fun _ _ => MeasurableSet.of_discrete)
  rw [h]
  simp [PMF.uniformOfFintype_apply]

theorem coins_pre (P : List Bool → Bool) (n : ℕ) :
    (coins {ω | P (pre ω n) = true}).toReal = (cnt P n [] : ℝ) / 2 ^ n := by
  classical
  set T := (allStrings n).toFinset
  have hcover : {ω | P (pre ω n) = true} =
      ⋃ s ∈ T, {ω | pre ω n = s ∧ P s = true} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, T, List.mem_toFinset,
      mem_allStrings]
    constructor
    · intro h; exact ⟨pre ω n, length_pre ω n, rfl, h⟩
    · rintro ⟨s, _, rfl, h⟩; exact h
  have hmeas : ∀ s ∈ T, MeasurableSet {ω : ℕ → Bool | pre ω n = s ∧ P s = true} := by
    intro s _
    by_cases hP : P s = true
    · simp only [hP, and_true]
      by_cases hl : s.length = n
      · rw [show {ω : ℕ → Bool | pre ω n = s} = Set.pi (Finset.range n : Set ℕ)
          (fun i => {s.getD i false}) by ext ω; exact pre_eq_iff ω s hl]
        exact MeasurableSet.pi (Set.to_countable _) fun _ _ => MeasurableSet.of_discrete
      · convert MeasurableSet.empty
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; exact hl (h ▸ length_pre ω n)
    · simp [hP]
  have hdisj : (T : Set (List Bool)).PairwiseDisjoint
      fun s => {ω : ℕ → Bool | pre ω n = s ∧ P s = true} := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 fun ω ha hb => hab ?_
    exact ha.1.symm.trans hb.1
  rw [hcover, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have hterm : ∀ s ∈ T, coins {ω | pre ω n = s ∧ P s = true} =
      if P s = true then (1 / 2 : ENNReal) ^ n else 0 := by
    intro s hs
    have hl : s.length = n := (mem_allStrings n s).1 (List.mem_toFinset.1 hs)
    split_ifs with hP
    · simp only [hP, and_true]; rw [← hl]; exact coins_cyl s
    · simp [hP]
  rw [Finset.sum_congr rfl hterm, ENNReal.toReal_sum (fun s _ => by split_ifs <;> simp)]
  unfold cnt
  rw [← List.sum_toFinset _ (nodup_allStrings n)]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [List.nil_append]
  split_ifs <;> simp

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

section Correct

variable {bad d J}

theorem cnt_zero (P : List Bool → Bool) (q : List Bool) :
    cnt P 0 q = if P q then 1 else 0 := by
  simp [cnt, allStrings]

theorem cnt_succ (P : List Bool → Bool) (m : ℕ) (p : List Bool) :
    cnt P (m + 1) p = cnt P m (p ++ [false]) + cnt P m (p ++ [true]) := by
  unfold cnt
  simp only [allStrings]
  rw [← List.sum_map_add]
  induction allStrings m with
  | nil => simp
  | cons s L ih => simp [List.flatMap_cons, ih]; ring

theorem dens_nonneg (j : ℕ) (q : List Bool) : 0 ≤ dens bad d j q := by
  unfold dens; positivity

theorem dens_avg (j : ℕ) (p : List Bool) :
    dens bad d j p = (dens bad d j (p ++ [false]) + dens bad d j (p ++ [true])) / 2 := by
  unfold dens
  simp only [List.length_append, List.length_singleton]
  rcases Nat.lt_or_ge p.length (d j) with h | h
  · obtain ⟨m, hm⟩ : ∃ m, d j - p.length = m + 1 := ⟨d j - p.length - 1, by omega⟩
    have hm' : d j - (p.length + 1) = m := by omega
    rw [hm, hm', cnt_succ]
    push_cast
    rw [pow_succ]
    field_simp
  · have h0 : d j - p.length = 0 := by omega
    have h1 : d j - (p.length + 1) = 0 := by omega
    rw [h0, h1, cnt_zero, cnt_zero, cnt_zero]
    simp only [badAt, List.take_append_of_le_length h]
    ring_nf
    exact rfl

theorem dens_snoc_le (j : ℕ) (p : List Bool) (b : Bool) :
    dens bad d j (p ++ [b]) ≤ 2 * dens bad d j p := by
  rw [dens_avg (bad := bad) (d := d) j p]
  have h0 := dens_nonneg (bad := bad) (d := d) j (p ++ [false])
  have h1 := dens_nonneg (bad := bad) (d := d) j (p ++ [true])
  cases b <;> linarith

theorem dens_le_pow (j : ℕ) (q : List Bool) :
    dens bad d j q ≤ 2 ^ q.length * dens bad d j [] := by
  induction q using List.reverseRecOn with
  | nil => simp
  | append_singleton p b ih =>
    rw [List.length_append, List.length_singleton, pow_succ]
    calc dens bad d j (p ++ [b]) ≤ 2 * dens bad d j p := dens_snoc_le j p b
      _ ≤ 2 * (2 ^ p.length * dens bad d j []) := by linarith
      _ = _ := by ring

theorem dens_of_le (j : ℕ) (p : List Bool) (h : d j ≤ p.length) :
    dens bad d j p = if bad j (p.take (d j)) then 1 else 0 := by
  unfold dens
  rw [show d j - p.length = 0 by omega, cnt_zero]
  simp only [badAt, pow_zero, div_one]
  split_ifs <;> simp [*]

theorem le_bigS (k j : ℕ) (hj : j < J k + 1) : d j ≤ bigS d J k := by
  unfold bigS
  exact List.le_sum_of_mem (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

/-- Truncated potential. -/
noncomputable def F (k : ℕ) (q : List Bool) : ℝ :=
  ∑ j ∈ Finset.range (J k + 1), dens bad d j q

theorem W_eq (k : ℕ) (q : List Bool) :
    (W bad d J k q : ℝ) = 2 ^ bigS d J k * F (bad := bad) (d := d) (J := J) k q := by
  unfold W F
  rw [← List.sum_toFinset _ List.nodup_range]
  · push_cast
    rw [Finset.mul_sum, List.toFinset_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hle : d j - q.length ≤ bigS d J k :=
      (Nat.sub_le _ _).trans (le_bigS k j (Finset.mem_range.1 hj))
    unfold dens cntJ
    rw [pow_sub₀ _ two_ne_zero hle]
    field_simp

theorem F_choose_le (k : ℕ) (p : List Bool) :
    F (bad := bad) (d := d) (J := J) k (p ++ [choose bad d J k p]) ≤ F (bad := bad) (d := d) (J := J) k p := by
  have havg : F (bad := bad) (d := d) (J := J) k p =
      (F (bad := bad) (d := d) (J := J) k (p ++ [false]) +
        F (bad := bad) (d := d) (J := J) k (p ++ [true])) / 2 := by
    unfold F
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => dens_avg j p
  have hpos : (0 : ℝ) < 2 ^ bigS d J k := by positivity
  rw [havg]
  unfold choose
  by_cases hc : W bad d J k (p ++ [true]) < W bad d J k (p ++ [false])
  · simp only [hc, decide_true]
    have : (W bad d J k (p ++ [true]) : ℝ) < W bad d J k (p ++ [false]) := by exact_mod_cast hc
    rw [W_eq, W_eq] at this
    have := lt_of_mul_lt_mul_left this hpos.le
    linarith
  · simp only [hc, decide_false]
    have : (W bad d J k (p ++ [false]) : ℝ) ≤ W bad d J k (p ++ [true]) := by
      exact_mod_cast not_lt.1 hc
    rw [W_eq, W_eq] at this
    have := le_of_mul_le_mul_left this hpos
    linarith

theorem length_preA (k : ℕ) : (preA bad d J k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [preA, ih]

theorem pre_algo (n : ℕ) : pre (algo bad d J) n = preA bad d J n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pre, List.range_succ, List.map_append, List.map_singleton] at ih ⊢
    rw [ih]; rfl

end Correct

/-- **Computable avoidance.** -/
theorem exists_primrec_avoid (bad : ℕ → List Bool → Bool) (hbad : Primrec₂ bad)
    (d : ℕ → ℕ) (hd : Primrec d) (J : ℕ → ℕ) (hJ : Primrec J)
    (hsum : Summable fun j => dens bad d j [])
    (htot : ∑' j, dens bad d j [] ≤ 1 / 4)
    (htail : ∀ k, ∑' j, (if J k < j then dens bad d j [] else 0) ≤ (1 / 8 : ℝ) ^ (k + 1)) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ j, bad j (pre e (d j)) = false := by
  refine ⟨algo bad d J, computable_algo hbad hd hJ, ?_⟩
  set Φ : List Bool → ℝ := fun q => ∑' j, dens bad d j q with hΦdef
  have hsq : ∀ q, Summable fun j => dens bad d j q := fun q =>
    (hsum.mul_left (2 ^ q.length)).of_nonneg_of_le (fun j => dens_nonneg j q)
      (fun j => dens_le_pow j q)
  have hT : ∀ k q, Summable fun j => if J k < j then dens bad d j q else 0 := fun k q =>
    (hsq q).of_nonneg_of_le (fun j => by split_ifs <;> simp [dens_nonneg])
      (fun j => by split_ifs <;> simp [dens_nonneg])
  have hTnn : ∀ k q, 0 ≤ ∑' j, (if J k < j then dens bad d j q else 0) := fun k q =>
    tsum_nonneg fun j => by split_ifs <;> simp [dens_nonneg]
  have hsplit : ∀ k q, Φ q = F (bad := bad) (d := d) (J := J) k q +
      ∑' j, (if J k < j then dens bad d j q else 0) := by
    intro k q
    have hA : Summable fun j => if j < J k + 1 then dens bad d j q else 0 :=
      (hsq q).of_nonneg_of_le (fun j => by split_ifs <;> simp [dens_nonneg])
        (fun j => by split_ifs <;> simp [dens_nonneg])
    have hpt : (fun j => dens bad d j q) = fun j =>
        (if j < J k + 1 then dens bad d j q else 0) + (if J k < j then dens bad d j q else 0) := by
      funext j; split_ifs <;> first | omega | simp
    simp only [hΦdef]
    rw [hpt, hA.tsum_add (hT k q)]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (J k + 1)) (fun j hj => by
      rw [if_neg (by simpa using hj)])]
    unfold F
    exact Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.1 hj)
  have htailq : ∀ k q, q.length = k + 1 →
      ∑' j, (if J k < j then dens bad d j q else 0) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
    intro k q hq
    calc ∑' j, (if J k < j then dens bad d j q else 0)
        ≤ ∑' j, (2 : ℝ) ^ (k + 1) * (if J k < j then dens bad d j [] else 0) := by
          refine (hT k q).tsum_le_tsum (fun j => ?_) ((hT k []).mul_left _)
          split_ifs
          · rw [← hq]; exact dens_le_pow j q
          · simp
      _ = 2 ^ (k + 1) * ∑' j, (if J k < j then dens bad d j [] else 0) := tsum_mul_left
      _ ≤ 2 ^ (k + 1) * (1 / 8) ^ (k + 1) := by gcongr; exact htail k
      _ = (1 / 4) ^ (k + 1) := by rw [← mul_pow]; norm_num
  have hstep : ∀ k, Φ (preA bad d J (k + 1)) ≤ Φ (preA bad d J k) + (1 / 4 : ℝ) ^ (k + 1) := by
    intro k
    rw [hsplit k (preA bad d J (k + 1))]
    have h1 := htailq k (preA bad d J (k + 1)) (length_preA (k + 1))
    have h2 : F (bad := bad) (d := d) (J := J) k (preA bad d J (k + 1)) ≤
        F (bad := bad) (d := d) (J := J) k (preA bad d J k) := F_choose_le k _
    have h3 := hsplit k (preA bad d J k)
    have h4 := hTnn k (preA bad d J k)
    linarith
  have hbound : ∀ k, Φ (preA bad d J k) ≤ 1 / 4 + (1 - (1 / 4 : ℝ) ^ k) / 3 := by
    intro k
    induction k with
    | zero => simp only [preA, pow_zero, sub_self, zero_div, add_zero]; exact htot
    | succ k ih =>
      have := hstep k
      rw [pow_succ] at this ⊢
      linarith
  intro j
  rw [pre_algo]
  have hlen := length_preA (bad := bad) (d := d) (J := J) (d j)
  have hd1 := dens_of_le (bad := bad) (d := d) j (preA bad d J (d j)) hlen.ge
  rw [List.take_of_length_le hlen.le] at hd1
  have hle : dens bad d j (preA bad d J (d j)) ≤ Φ (preA bad d J (d j)) :=
    (hsq _).le_tsum j (fun i _ => dens_nonneg i _)
  have hb := hbound (d j)
  have hp : (0 : ℝ) ≤ (1 / 4) ^ (d j) := by positivity
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [if_pos hc] at hd1
  linarith

end NormalNumbers.Derandomize
