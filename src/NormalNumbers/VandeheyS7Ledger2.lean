/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-LD2: the greedy ledger — the output's height is paid for by the input's

S7-GW priced the two moves of the greedy transducer (`width_emit_ge`, `width_comp_readMap_ge`).
This module runs the ledger over a whole run and cashes it in.

* `width_emitAcc_ge` / `width_flushState_ge_prod` — the flush's gain is the PRODUCT of the squares
  of the digits it emits: `(∏_{b ∈ flushWord t} b²) · width t ≤ width (flushState t)`.
* `width_grunState_ge` — the run's recursion, telescoped:

      width Φ' · ∏_{j < |gOut Φ x p|} b_j²  ≤  width (grunState Φ x p) · ∏_{n<p} cost_n ,

  where `Φ' = grunState Φ x 0`, `b_j` are the output digits and
  `cost_n = a_n(a_n+1)(r_n + 2 + 1/r_n)` is S7-GW's read price.
* `outProd_le` — since `width ≤ 1`, the same inequality without the state:

      ∏_{j} b_j²  ≤  (∏_{n<p} cost_n) / width (grunState Φ x 0) .

**The output stream cannot outgrow the input stream.**  This is the quantitative form of "a
transducer creates no information", and it is the ledger the clock analysis runs on: an output word
of large height forces an input word of at least comparable height, with the distortion factor
`r + 2 + 1/r` as the only leak.

The converse direction — that the output KEEPS UP, i.e. the width does not drift to zero — is the
remaining scalar obligation.  The lap-91 probe measures it as true for the greedy run in the strong
Cesàro sense (`mean slack ≈ 2.0` over 20000 reads of a rational map, against a `√n` walk for the
throttled run), and locates the mechanism: `slack ≈ 2 log(next output digit)` (correlation `0.65`),
i.e. a narrow reduced state is one whose image sits near a cylinder boundary, which is exactly what
makes the NEXT output digit large.

## Guard rule

**Content locator.**  `width_emitAcc_ge` is an induction on the emission attempts using
`width_emit_ge`; the run telescoping is an induction using `width_grunState_succ_ge`.

**Degenerate cases.**  A flush that emits nothing has product `1` and the bound is
`width t ≤ width t`.  Digits equal to `1` contribute a factor `1`: they are free in both
directions, which is why the ledger controls heights and not digit counts.
-/
import NormalNumbers.VandeheyS7GreedyWidth
import NormalNumbers.VandeheyS7GreedyCorrect

namespace NormalNumbers.VandeheyS7

open Set Finset NormalNumbers

namespace MapState

/-- The product of the squares of a word's digits — the height the word carries. -/
noncomputable def wordProd (u : List ℕ) : ℝ := (u.map fun b => ((b : ℕ) : ℝ) ^ 2).prod

@[simp] lemma wordProd_nil : wordProd [] = 1 := by simp [wordProd]

lemma wordProd_append (u v : List ℕ) : wordProd (u ++ v) = wordProd u * wordProd v := by
  simp [wordProd, List.map_append]

lemma wordProd_pos {u : List ℕ} (hu : ∀ a ∈ u, 1 ≤ a) : 0 < wordProd u := by
  induction u with
  | nil => simp
  | cons a u ih =>
      have ha : 1 ≤ a := hu a (by simp)
      have haR : (0:ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast ha
      have := ih fun e he => hu e (by simp [he])
      simp only [wordProd, List.map_cons, List.prod_cons] at *
      positivity

lemma one_le_wordProd {u : List ℕ} (hu : ∀ a ∈ u, 1 ≤ a) : 1 ≤ wordProd u := by
  induction u with
  | nil => simp
  | cons a u ih =>
      have ha : 1 ≤ a := hu a (by simp)
      have haR : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
      have hrest := ih fun e he => hu e (by simp [he])
      simp only [wordProd, List.map_cons, List.prod_cons] at *
      nlinarith

/-! ## The flush's gain -/

/-- **The emission ledger.**  `n` emission attempts multiply the width by at least the product of
the squares of the digits emitted. -/
theorem width_emitAcc_ge (t : MapState) (n : ℕ) :
    wordProd (emitAcc t n) * t.width ≤ (stepFst^[n] t).width := by
  induction n with
  | zero => simp [emitAcc]
  | succ k ih =>
      rw [Function.iterate_succ_apply', emitAcc, wordProd_append]
      by_cases h : Emittable (stepFst^[k] t)
      · obtain ⟨b, hemit, hword⟩ := step_emitStep h
        have hgain := width_emit_ge hemit
        have hb : (1:ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hemit.1
        have hprod : wordProd (step (stepFst^[k] t)).2 = ((b : ℕ) : ℝ) ^ 2 := by
          rw [hword]; simp [wordProd]
        have hpos : 0 < wordProd (emitAcc t k) := wordProd_pos (emitAcc_pos t k)
        have hw0 : (0:ℝ) < t.width := width_pos t
        rw [hprod, mul_comm (wordProd (emitAcc t k)) (((b : ℕ) : ℝ) ^ 2), mul_assoc]
        calc ((b : ℕ) : ℝ) ^ 2 * (wordProd (emitAcc t k) * t.width)
            ≤ ((b : ℕ) : ℝ) ^ 2 * (stepFst^[k] t).width := by
              refine mul_le_mul_of_nonneg_left ih (by positivity)
          _ ≤ (stepFst (stepFst^[k] t)).width := by
              simpa [stepFst] using hgain
      · have hword : (step (stepFst^[k] t)).2 = [] := by
          rw [step_of_not_emittable h]
        rw [hword, wordProd_nil, mul_one, stepFst, step_of_not_emittable h]
        exact ih

/-- The flush's gain, in closed form. -/
theorem width_flushState_ge_prod (t : MapState) :
    wordProd (flushWord t) * t.width ≤ (flushState t).width :=
  width_emitAcc_ge t (flushLen t)

/-! ## The run's ledger -/

/-- The read price of the `n`-th step. -/
noncomputable def readCost (Φ : MapState) (x : ℝ) (n : ℕ) : ℝ :=
  ((inDigit x n : ℕ) : ℝ) * (((inDigit x n : ℕ) : ℝ) + 1)
    * ((grunState Φ x n).denRatio + 2 + 1 / (grunState Φ x n).denRatio)

lemma readCost_pos (Φ : MapState) (x : ℝ) (n : ℕ) : 0 < readCost Φ x n := by
  have h1 : (1:ℝ) ≤ ((inDigit x n : ℕ) : ℝ) := one_le_inDigit_real x n
  have h2 : 0 < (grunState Φ x n).denRatio := denRatio_pos _
  rw [readCost]
  positivity

/-- **The greedy ledger.**  Telescoped over a whole run: the output's height, times the initial
width, is at most the state's width times the accumulated read price. -/
theorem width_grunState_ge (Φ : MapState) (x : ℝ) (p : ℕ) :
    wordProd (gOut Φ x p) * Φ.width
      ≤ (grunState Φ x p).width * ∏ n ∈ range p, readCost Φ x n := by
  induction p with
  | zero =>
      simp only [gOut, range_zero, Finset.prod_empty, mul_one]
      have h := width_flushState_ge_prod Φ
      have hg : grunState Φ x 0 = flushState Φ := rfl
      rw [hg]
      exact h
  | succ k ih =>
      have hstep : (grunState Φ x k).width / readCost Φ x k ≤ (grunState Φ x (k + 1)).width :=
        width_grunState_succ_ge Φ x k
      have hcost : 0 < readCost Φ x k := readCost_pos Φ x k
      have hflush : wordProd (grunWord Φ x k) * ((grunState Φ x k).comp (readAt x k)).width
          ≤ (grunState Φ x (k + 1)).width := width_flushState_ge_prod _
      have hread : (grunState Φ x k).width / readCost Φ x k
          ≤ ((grunState Φ x k).comp (readAt x k)).width := by
        have := width_comp_readMap_ge (grunState Φ x k) (one_le_inDigit_real x k)
        simpa [readCost, readAt] using this
      have hgprod : 0 < wordProd (grunWord Φ x k) := wordProd_pos (grunWord_pos Φ x k)
      -- combine the read and the flush
      have hcomb : wordProd (grunWord Φ x k) * ((grunState Φ x k).width / readCost Φ x k)
          ≤ (grunState Φ x (k + 1)).width :=
        le_trans (mul_le_mul_of_nonneg_left hread hgprod.le) hflush
      rw [gOut, wordProd_append, Finset.prod_range_succ]
      have hw0 : (0:ℝ) < Φ.width := width_pos _
      have hpos : 0 < wordProd (gOut Φ x k) := wordProd_pos (gOut_pos Φ x k)
      have hmul : wordProd (gOut Φ x k) * wordProd (grunWord Φ x k) * Φ.width
          ≤ wordProd (grunWord Φ x k) * ((grunState Φ x k).width
              * ∏ n ∈ range k, readCost Φ x n) := by
        have := mul_le_mul_of_nonneg_left ih hgprod.le
        nlinarith
      refine le_trans hmul ?_
      have hstate : wordProd (grunWord Φ x k) * (grunState Φ x k).width
          ≤ (grunState Φ x (k + 1)).width * readCost Φ x k := by
        rw [mul_div_assoc', div_le_iff₀ hcost] at hcomb
        linarith
      have hprodpos : (0:ℝ) < ∏ n ∈ range k, readCost Φ x n :=
        Finset.prod_pos fun n _ => readCost_pos Φ x n
      nlinarith

/-- **The output cannot outgrow the input.**  With `width ≤ 1` the state drops out. -/
theorem outProd_le (Φ : MapState) (x : ℝ) (p : ℕ) :
    wordProd (gOut Φ x p) * Φ.width ≤ ∏ n ∈ range p, readCost Φ x n := by
  refine le_trans (width_grunState_ge Φ x p) ?_
  have hw : (grunState Φ x p).width ≤ 1 := width_le_one _
  have hprodpos : (0:ℝ) < ∏ n ∈ range p, readCost Φ x n :=
    Finset.prod_pos fun n _ => readCost_pos Φ x n
  nlinarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.width_emitAcc_ge
#print axioms NormalNumbers.VandeheyS7.MapState.width_flushState_ge_prod
#print axioms NormalNumbers.VandeheyS7.MapState.width_grunState_ge
#print axioms NormalNumbers.VandeheyS7.MapState.outProd_le

end Audit
