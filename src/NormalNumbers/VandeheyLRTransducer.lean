/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyRaney
import NormalNumbers.VandeheyAssembly

/-!
# The concrete transducer: Raney states emitting `L/R` letters

`VandeheyAssembly.mobiusUniformFreq_of_transducer` reduces Vandehey 2017 Theorem 1.1 to a
finite-state transducer with named properties.  This file builds the transducer for `x ↦ D·x`
out of `VandeheyRaney.isRD_ingest` and proves its algebraic core.

## Why `L/R` letters and not CF digits

The obvious design — emit CF digits — does not fit a FINITE state set.  `isRD_ingest_cfString`
emits `A_{d₀} B_{d₁} ⋯ B_{d_m}`, and since `B_d · A_e = B_{d+e}`, the *last* emitted digit is
still provisional: the next step's `d₀` adds to it.  A transducer would have to carry that
pending digit in its state, and the pending digit is unbounded.

Emitting `L/R` letters removes the problem: an `L/R` letter, once emitted, is final.  The CF
digits of the image are then the *runs* of the `L/R` word, and "the last run may still grow"
becomes a one-letter look-ahead — a boundary condition, not an unbounded state.  The two
reindexings this costs (input digits → `L/R` letters → output CF digits) are both instances of
`VandeheyRescale.tendsto_div_of_tendsto_comp_of_monotone`, which is already in the kernel.

## What is here

* `RState D` — the Raney states, a `Fintype` by `finite_isRD`.
* `lrStep` — one transducer step, chosen from `isRD_ingest`; `lrDelta` and `lrOut` are its parts.
* `lrRun_eq` — **the algebraic core**: after reading the first `n` CF digits of `x`,
  `M₀ · B_{a₁} ⋯ B_{a_n} = lrProd (emitted word) · M_n`.  So the emitted `L/R` word and the
  reached state together account for the entire input, exactly.
-/

namespace NormalNumbers.VandeheyLR

open Mat2 VandeheyAut

/-- The Raney states of determinant `±D`: the transducer's (finite) state set. -/
abbrev RState (D : ℕ) := {M : Mat2 // IsRD D M}

instance (D : ℕ) : Finite (RState D) := finite_isRD D

noncomputable instance (D : ℕ) : Fintype (RState D) := Fintype.ofFinite _

/-- The start state `diag(D, 1)`, i.e. the map `x ↦ D·x`. -/
def startState {D : ℕ} (hD : 0 < D) : RState D := ⟨⟨(D : ℤ), 0, 0, 1⟩, isRD_diag hD⟩

/-! ## One step -/

/-- One transducer step: ingest a CF digit, emit an `L/R` word, move to a new Raney state.
Chosen from `isRD_ingest`, which is where Raney's balanced-decomposition descent lives. -/
noncomputable def lrStep {D : ℕ} (hD : 0 < D) (M : RState D) (j : ℕ) :
    List Bool × RState D :=
  let h := isRD_ingest hD M.2 j
  (h.choose, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩)

/-- The emitted `L/R` word. -/
noncomputable def lrOut {D : ℕ} (hD : 0 < D) (M : RState D) (j : ℕ) : List Bool :=
  (lrStep hD M j).1

/-- The transition function. -/
noncomputable def lrDelta {D : ℕ} (hD : 0 < D) (M : RState D) (j : ℕ) : RState D :=
  (lrStep hD M j).2

/-- **The step identity.**  This is `isRD_ingest` with the choices named. -/
lemma lrStep_spec {D : ℕ} (hD : 0 < D) (M : RState D) (j : ℕ) :
    M.val * B j = lrProd (lrOut hD M j) * (lrDelta hD M j).val :=
  (isRD_ingest hD M.2 j).choose_spec.choose_spec.2

/-! ## Products over words -/

lemma bProd_append (u w : List ℕ) : bProd (u ++ w) = bProd u * bProd w := by
  induction u with
  | nil => simp
  | cons a u ih => rw [List.cons_append, bProd_cons, bProd_cons, ih, mul_assoc']

lemma lrProd_append (u w : List Bool) : lrProd (u ++ w) = lrProd u * lrProd w := by
  induction u with
  | nil => simp [lrProd]
  | cons b u ih => rw [List.cons_append, lrProd_cons, lrProd_cons, ih, mul_assoc']

/-! ## The run identity -/

variable {D : ℕ}

/-- The `L/R` word emitted while reading the first `n` CF digits of `x`. -/
noncomputable def lrWord (hD : 0 < D) (s₀ : RState D) (x : ℝ) (n : ℕ) : List Bool :=
  (List.range n).flatMap
    (fun i => lrOut hD (stateAt (lrDelta hD) s₀ x i) (cfDigit x i))

lemma lrWord_succ (hD : 0 < D) (s₀ : RState D) (x : ℝ) (n : ℕ) :
    lrWord hD s₀ x (n + 1)
      = lrWord hD s₀ x n ++ lrOut hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n) := by
  simp [lrWord, List.range_succ]

lemma cfWord_succ'' (x : ℝ) (n : ℕ) : cfWord x (n + 1) = cfWord x n ++ [cfDigit x n] := by
  rw [cfWord_add]
  simp [cfWindow]

/-- **The algebraic core of the transducer.**  Reading the first `n` CF digits of `x` from the
start state factors, exactly, as the emitted `L/R` word times the reached Raney state:

  `M₀ · B_{a₁} ⋯ B_{a_n} = lrProd (lrWord n) · M_n`.

Every later obligation of `mobiusUniformFreq_of_transducer` — that the emitted stream is the CF
expansion of `D·x`, that its length grows linearly, that trigger multiplicities are bounded — is
a statement about this identity together with the `Fintype` bound on the states. -/
theorem lrRun_eq (hD : 0 < D) (s₀ : RState D) (x : ℝ) (n : ℕ) :
    s₀.val * bProd (cfWord x n)
      = lrProd (lrWord hD s₀ x n) * (stateAt (lrDelta hD) s₀ x n).val := by
  induction n with
  | zero => simp [lrWord, cfWord, stateAt]
  | succ n ih =>
    rw [cfWord_succ'', bProd_append, ← mul_assoc', ih, lrWord_succ, lrProd_append,
      mul_assoc', mul_assoc']
    congr 1
    have hstate : stateAt (lrDelta hD) s₀ x (n + 1)
        = lrDelta hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n) := by
      rw [stateAt, stateAt, cfWord_succ'', runState_append]
      simp [runState]
    rw [hstate]
    have hb : bProd [cfDigit x n] = B (cfDigit x n) := by simp [bProd]
    rw [hb]
    exact lrStep_spec hD (stateAt (lrDelta hD) s₀ x n) (cfDigit x n)

/-! ## The semantic invariant

`lrRun_eq` is an identity of matrices; this section turns it into an identity of REALS, which is
what the `hout` obligation of `mobiusUniformFreq_of_transducer` is about.  Combined with
`Mat2.act_cfMat` (`x = B_{a₁} ⋯ B_{aₙ} · Tⁿx`), it says: after `n` input digits the image `D·x`
is the emitted `L/R` word applied to a point of the state cone. -/

/-- A nonnegative pair, not both zero, gives a positive linear form at a positive argument. -/
lemma pos_lin {p q : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hne : ¬(p = 0 ∧ q = 0)) {u : ℝ}
    (hu : 0 < u) : 0 < (p : ℝ) * u + (q : ℝ) := by
  have hp' : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rcases eq_or_lt_of_le hq' with h | h
  · have hq0 : q = 0 := by exact_mod_cast h.symm
    have hp0 : p ≠ 0 := fun h0 => hne ⟨h0, hq0⟩
    have : (0 : ℝ) < (p : ℝ) := lt_of_le_of_ne hp' (by exact_mod_cast (Ne.symm hp0))
    have := mul_pos this hu
    linarith
  · nlinarith

lemma den_pos_of_nonneg {M : Mat2} (hN : Nonneg M) (hdet : M.det ≠ 0) {u : ℝ} (hu : 0 < u) :
    0 < M.den u := by
  obtain ⟨-, -, hc, hd⟩ := hN
  refine pos_lin hc hd (fun h => hdet ?_) hu
  simp [det, h.1, h.2]

lemma num_pos_of_nonneg {M : Mat2} (hN : Nonneg M) (hdet : M.det ≠ 0) {u : ℝ} (hu : 0 < u) :
    0 < (M.a : ℝ) * u + (M.b : ℝ) := by
  obtain ⟨ha, hb, -, -⟩ := hN
  refine pos_lin ha hb (fun h => hdet ?_) hu
  simp [det, h.1, h.2]

lemma act_pos_of_nonneg {M : Mat2} (hN : Nonneg M) (hdet : M.det ≠ 0) {u : ℝ} (hu : 0 < u) :
    0 < M.act u :=
  div_pos (num_pos_of_nonneg hN hdet hu) (den_pos_of_nonneg hN hdet hu)

lemma nonneg_lrProd (w : List Bool) : Nonneg (lrProd w) := by
  induction w with
  | nil => exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  | cons b w ih =>
    rw [lrProd_cons]
    exact Mat2.Nonneg.mul (by cases b <;> exact ⟨by simp [lrL, lrR], by simp [lrL, lrR],
      by simp [lrL, lrR], by simp [lrL, lrR]⟩) ih

lemma isRD_nonneg {M : Mat2} (hM : IsRD D M) : Nonneg M := hM.2.1

lemma isRD_det_ne (hD : 0 < D) {M : Mat2} (hM : IsRD D M) : M.det ≠ 0 := by
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  rcases hM.1 with h | h <;> rw [h] <;> omega

/-- The CF matrix of the first `n` digits is the `B`-product of the input word. -/
lemma cfMat_eq_bProd (x : ℝ) (n : ℕ) : cfMat x n = bProd (cfWord x n) := by
  induction n with
  | zero => simp [cfWord]
  | succ n ih =>
    rw [cfMat_succ, ih, cfWord_succ'', bProd_append]
    simp [bProd]

/-- **The semantic invariant.**  After `n` input digits, the image is the emitted `L/R` word
applied to the state cone point `M_n · Tⁿx`.  So the `L/R` stream really is being read off the
image from the left, one letter at a time, with the state carrying the un-emitted remainder. -/
theorem act_startState_eq (hD : 0 < D) {x : ℝ} (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (startState hD).val.act x
      = (lrProd (lrWord hD (startState hD) x n)).act
          ((stateAt (lrDelta hD) (startState hD) x n).val.act (gaussMap^[n] x)) := by
  obtain ⟨hirrn, hmemn⟩ := irrational_orbit x hirr hx n
  set Mn : Mat2 := (stateAt (lrDelta hD) (startState hD) x n).val with hMn
  have hMnRD : IsRD D Mn := (stateAt (lrDelta hD) (startState hD) x n).2
  have hu : (0 : ℝ) < gaussMap^[n] x := hmemn.1
  have hdenMn : Mn.den (gaussMap^[n] x) ≠ 0 :=
    ne_of_gt (den_pos_of_nonneg (isRD_nonneg hMnRD) (isRD_det_ne hD hMnRD) hu)
  have hactMn : 0 < Mn.act (gaussMap^[n] x) :=
    act_pos_of_nonneg (isRD_nonneg hMnRD) (isRD_det_ne hD hMnRD) hu
  have hdenLR : (lrProd (lrWord hD (startState hD) x n)).den (Mn.act (gaussMap^[n] x)) ≠ 0 := by
    refine ne_of_gt (den_pos_of_nonneg (nonneg_lrProd _) ?_ hactMn)
    rw [det_lrProd]; norm_num
  -- the input side
  have hcf : (cfMat x n).act (gaussMap^[n] x) = x := act_cfMat hirr hx n
  have hdencf : (cfMat x n).den (gaussMap^[n] x) ≠ 0 :=
    ne_of_gt (cfMat_den_pos hirr hx n hu.le)
  have hdenStart : (startState hD).val.den ((cfMat x n).act (gaussMap^[n] x)) ≠ 0 := by
    rw [hcf, startState, den]
    simp
  calc (startState hD).val.act x
      = (startState hD).val.act ((cfMat x n).act (gaussMap^[n] x)) := by rw [hcf]
    _ = ((startState hD).val * cfMat x n).act (gaussMap^[n] x) :=
        (Mat2.act_mul _ _ _ hdencf hdenStart).symm
    _ = (lrProd (lrWord hD (startState hD) x n) * Mn).act (gaussMap^[n] x) := by
        rw [cfMat_eq_bProd, lrRun_eq hD (startState hD) x n]
    _ = (lrProd (lrWord hD (startState hD) x n)).act (Mn.act (gaussMap^[n] x)) :=
        Mat2.act_mul _ _ _ hdenMn hdenLR


/-! ## The `L/R` expansion of a real, and the prefix property

`R · u = u + 1` and `L · u = u/(u+1)`, so `R` maps `(0,∞)` onto `(1,∞)` and `L` maps it onto
`(0,1)`.  The two images are disjoint, which is exactly what makes the `L/R` expansion of a
positive real unique — and makes a factorization `z = lrProd w · u` with `u > 0` *determine* that
`w` is the expansion's prefix.  No irrationality is needed: the boundary value `z = 1` is never
produced from a positive `u`. -/

/-- One step of the `L/R` expansion: undo `L` below `1`, undo `R` above. -/
noncomputable def lrTail (z : ℝ) : ℝ := if z < 1 then z / (1 - z) else z - 1

/-- The letter of the `L/R` expansion at the current point (`true = L`). -/
noncomputable def lrLetter (z : ℝ) : Bool := decide (z < 1)

/-- The `n`-th letter of the `L/R` expansion of `z`. -/
noncomputable def lrExpand (z : ℝ) (n : ℕ) : Bool := lrLetter (lrTail^[n] z)

/-- The first `n` letters of the `L/R` expansion of `z`. -/
noncomputable def lrExpandWord (z : ℝ) (n : ℕ) : List Bool := (List.range n).map (lrExpand z)

lemma lrExpandWord_succ (z : ℝ) (n : ℕ) :
    lrExpandWord z (n + 1) = lrLetter z :: lrExpandWord (lrTail z) n := by
  rw [lrExpandWord, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

lemma act_lrL (u : ℝ) (hu : 0 < u) : lrL.act u = u / (u + 1) := by
  rw [lrL, act, den]
  norm_num

lemma act_lrR (u : ℝ) : lrR.act u = u + 1 := by
  rw [lrR, act, den]
  norm_num

/-- **The prefix property.**  If `z = lrProd w · u` with `u > 0`, then `w` IS the first `|w|`
letters of the `L/R` expansion of `z`, and `u` is what remains.  This is the uniqueness of the
Stern-Brocot path, and it is what turns the transducer's semantic invariant into the statement
that its output stream is the expansion of the image. -/
theorem lrExpandWord_of_act : ∀ (w : List Bool) {u : ℝ}, 0 < u →
    lrExpandWord ((lrProd w).act u) w.length = w ∧
      lrTail^[w.length] ((lrProd w).act u) = u := by
  intro w
  induction w with
  | nil => intro u _; simp [lrExpandWord, lrProd]
  | cons b w ih =>
    intro u hu
    have hdetw : (lrProd w).det ≠ 0 := by rw [det_lrProd]; norm_num
    have hz' : 0 < (lrProd w).act u := act_pos_of_nonneg (nonneg_lrProd w) hdetw hu
    set z' : ℝ := (lrProd w).act u with hz'def
    have hdenw : (lrProd w).den u ≠ 0 :=
      ne_of_gt (den_pos_of_nonneg (nonneg_lrProd w) hdetw hu)
    obtain ⟨ihw, ihu⟩ := ih hu
    have hstep : (lrProd (b :: w)).act u = (if b = true then lrL else lrR).act z' := by
      rw [lrProd_cons]
      refine Mat2.act_mul _ _ _ hdenw ?_
      cases b
      · simp only [Bool.false_eq_true, if_false, lrR, den]
        norm_num
      · simp only [if_true, lrL, den]
        push_cast
        positivity
    cases b
    · -- `R`: the point lands above 1
      have hz : (lrProd (false :: w)).act u = z' + 1 := by
        rw [hstep]; simp only [Bool.false_eq_true, if_false]; exact act_lrR z'
      have hnlt : ¬ (z' + 1 < 1) := by linarith
      constructor
      · rw [hz, List.length_cons, lrExpandWord_succ, lrLetter, decide_eq_false hnlt,
          lrTail, if_neg hnlt, add_sub_cancel_right, ihw]
      · rw [hz, List.length_cons, Function.iterate_succ_apply, lrTail, if_neg hnlt,
          add_sub_cancel_right, ihu]
    · -- `L`: the point lands below 1
      have hz : (lrProd (true :: w)).act u = z' / (z' + 1) := by
        rw [hstep]; simp only [if_true]; exact act_lrL z' hz'
      have hlt : z' / (z' + 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      have hne : z' + 1 ≠ 0 := by linarith
      have htail : lrTail (z' / (z' + 1)) = z' := by
        rw [lrTail, if_pos hlt]
        field_simp
        ring
      constructor
      · rw [hz, List.length_cons, lrExpandWord_succ, lrLetter, decide_eq_true hlt, htail, ihw]
      · rw [hz, List.length_cons, Function.iterate_succ_apply, htail, ihu]

/-- **The transducer's output IS the `L/R` expansion of the image.**  Combining the semantic
invariant with the prefix property: at every `n`, the word emitted so far is exactly the
expansion's prefix of its own length. -/
theorem lrWord_eq_lrExpandWord (hD : 0 < D) {x : ℝ} (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    lrExpandWord ((startState hD).val.act x) (lrWord hD (startState hD) x n).length
      = lrWord hD (startState hD) x n := by
  obtain ⟨-, hmemn⟩ := irrational_orbit x hirr hx n
  set Mn : Mat2 := (stateAt (lrDelta hD) (startState hD) x n).val with hMn
  have hMnRD : IsRD D Mn := (stateAt (lrDelta hD) (startState hD) x n).2
  have hactMn : 0 < Mn.act (gaussMap^[n] x) :=
    act_pos_of_nonneg (isRD_nonneg hMnRD) (isRD_det_ne hD hMnRD) hmemn.1
  rw [act_startState_eq hD hirr hx n]
  exact (lrExpandWord_of_act _ hactMn).1


end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms lrStep_spec
#print axioms lrRun_eq
#print axioms act_startState_eq
#print axioms lrExpandWord_of_act
#print axioms lrWord_eq_lrExpandWord
end
