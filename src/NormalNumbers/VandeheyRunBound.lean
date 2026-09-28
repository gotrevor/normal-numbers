/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyLRTransducer

/-!
# Vandehey Lemma 2.2, in run form: a block emits at most `2D` alternations

The `L/R` transducer of `VandeheyLRTransducer` emits, for one ingested CF digit `j`, a word
`lrOut M j` whose LENGTH is genuinely unbounded (a large `j` emits a long run).  What Vandehey's
Lemma 2.2 bounds is the number of emitted CF digits, i.e. the number of **runs** of that word —
equivalently the number of **alternations** `numAlt`, adjacent positions carrying different
letters.  That is the bound the trigger layer needs, because a genuine CF trigger word's `L/R`
pattern contains both letters, so an occurrence can only start near an alternation.

## The proof

The hinge is `VandeheyLRTransducer.lrStep_col`: the first column of `M · B j` is `M`'s second
column, *independently of `j`*, so the step identity `M · B j = lrProd w · M'` gives the `j`-free
**vector** identity

  `(M.b, M.d) = lrProd w ·ᵛ (M'.a, M'.c)`.

Now read `lrProd w` right-to-left on a nonnegative column: `L` sends `(p,q) ↦ (p, p+q)` and `R`
sends `(p,q) ↦ (p+q, q)`.  Each letter therefore *adds* one coordinate to the other, and the
coordinate sum is nondecreasing.  A letter can fail to increase the sum only when the coordinate
it adds is `0` — and a `0` coordinate can only persist under one of the two letters, so the whole
remaining word is constant and carries **no alternation at all**.  Hence

  `numAlt w ≤ p + q`  where `(p,q)` is the column `lrProd w` acts on,

which for the ingest identity reads `numAlt (lrOut M j) ≤ M.b + M.d ≤ 2D` by `raneyEntry_le`.

This avoids Vandehey's four-case split on vanishing denominators entirely: the degenerate
directions are exactly the cases in which the emitted word is a single run.
-/

namespace NormalNumbers.VandeheyLR

open Mat2

/-! ## Alternations of an `L/R` word -/

/-- The number of adjacent unequal pairs of an `L/R` word.  The number of runs of a nonempty
word is `numAlt + 1`. -/
def numAlt : List Bool → ℕ
  | [] => 0
  | _ :: [] => 0
  | b :: c :: w => (if b = c then 0 else 1) + numAlt (c :: w)

@[simp] lemma numAlt_nil : numAlt [] = 0 := rfl
@[simp] lemma numAlt_singleton (b : Bool) : numAlt [b] = 0 := rfl

lemma numAlt_cons_le (b : Bool) (w : List Bool) : numAlt (b :: w) ≤ numAlt w + 1 := by
  cases w with
  | nil => simp
  | cons c w =>
    rw [numAlt]
    split <;> omega

/-- A constant word has no alternation. -/
lemma numAlt_eq_zero_of_const : ∀ (w : List Bool) (b : Bool), (∀ x ∈ w, x = b) → numAlt w = 0
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | (u :: v :: w), b, h => by
      have hu : u = b := h u (by simp)
      have hv : v = b := h v (by simp)
      rw [numAlt, if_pos (hu.trans hv.symm),
        numAlt_eq_zero_of_const (v :: w) b (fun x hx => h x (by simp [hx]))]

/-! ## The column action -/

/-- A matrix acting on an integer column vector. -/
def colApp (M : Mat2) (v : ℤ × ℤ) : ℤ × ℤ := (M.a * v.1 + M.b * v.2, M.c * v.1 + M.d * v.2)

@[simp] lemma colApp_one (v : ℤ × ℤ) : colApp 1 v = v := by
  simp [colApp]

lemma colApp_mul (M N : Mat2) (v : ℤ × ℤ) : colApp (M * N) v = colApp M (colApp N v) := by
  simp only [colApp, mul_def, mul, Prod.mk.injEq]
  constructor <;> ring

lemma colApp_lrL (v : ℤ × ℤ) : colApp lrL v = (v.1, v.1 + v.2) := by
  simp [colApp, lrL]

lemma colApp_lrR (v : ℤ × ℤ) : colApp lrR v = (v.1 + v.2, v.2) := by
  simp [colApp, lrR]

/-! ## The bound -/

/-- **The engine.**  For a nonnegative, nonzero column `(a,c)`, the word `w` has at most
`p + q` alternations, where `(p,q) = lrProd w ·ᵛ (a,c)`; and a vanishing coordinate of the
result forces `w` to be constant. -/
theorem numAlt_le_colApp : ∀ (w : List Bool) {a c : ℤ}, 0 ≤ a → 0 ≤ c → ¬(a = 0 ∧ c = 0) →
    0 ≤ (colApp (lrProd w) (a, c)).1 ∧ 0 ≤ (colApp (lrProd w) (a, c)).2 ∧
      ¬((colApp (lrProd w) (a, c)).1 = 0 ∧ (colApp (lrProd w) (a, c)).2 = 0) ∧
      (numAlt w : ℤ) ≤ (colApp (lrProd w) (a, c)).1 + (colApp (lrProd w) (a, c)).2 ∧
      ((colApp (lrProd w) (a, c)).1 = 0 → ∀ x ∈ w, x = true) ∧
      ((colApp (lrProd w) (a, c)).2 = 0 → ∀ x ∈ w, x = false) := by
  intro w
  induction w with
  | nil =>
    intro a c ha hc hne
    refine ⟨by simpa using ha, by simpa using hc, by simpa using hne, by simp; omega, ?_, ?_⟩ <;> simp
  | cons b w ih =>
    intro a c ha hc hne
    obtain ⟨hp, hq, hpq, hnum, hzp, hzq⟩ := ih ha hc hne
    set p : ℤ := (colApp (lrProd w) (a, c)).1 with hpdef
    set q : ℤ := (colApp (lrProd w) (a, c)).2 with hqdef
    have hstep : colApp (lrProd (b :: w)) (a, c)
        = colApp (if b then lrL else lrR) (p, q) := by
      rw [lrProd_cons, colApp_mul]
    have halt : numAlt (b :: w) ≤ numAlt w + 1 := numAlt_cons_le b w
    have haltZ : (numAlt (b :: w) : ℤ) ≤ (numAlt w : ℤ) + 1 := by exact_mod_cast halt
    cases b with
    | true =>
      rw [hstep, if_pos rfl, colApp_lrL]
      simp only
      refine ⟨hp, by omega, by omega, ?_, ?_, ?_⟩
      · rcases eq_or_lt_of_le hp with h0 | h1
        · -- degenerate: `p = 0` forces `w` constant, so there is no alternation at all
          have hconst : ∀ x ∈ w, x = true := hzp h0.symm
          have : numAlt (true :: w) = 0 :=
            numAlt_eq_zero_of_const (true :: w) true (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · rfl
              · exact hconst x hx')
          rw [this]
          push_cast
          omega
        · omega
      · intro h0 x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · rfl
        · exact hzp h0 x hx'
      · intro h0
        exact absurd ⟨by omega, by omega⟩ hpq
    | false =>
      rw [hstep, if_neg (by simp), colApp_lrR]
      simp only
      refine ⟨by omega, hq, by omega, ?_, ?_, ?_⟩
      · rcases eq_or_lt_of_le hq with h0 | h1
        · have hconst : ∀ x ∈ w, x = false := hzq h0.symm
          have : numAlt (false :: w) = 0 :=
            numAlt_eq_zero_of_const (false :: w) false (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · rfl
              · exact hconst x hx')
          rw [this]
          push_cast
          omega
        · omega
      · intro h0
        exact absurd ⟨by omega, by omega⟩ hpq
      · intro h0 x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · rfl
        · exact hzq h0 x hx'

variable {D : ℕ}

/-- The first column of a Raney state is nonnegative and nonzero. -/
lemma isRD_fst_col {M : Mat2} (hD : 0 < D) (hM : IsRD D M) :
    0 ≤ M.a ∧ 0 ≤ M.c ∧ ¬(M.a = 0 ∧ M.c = 0) := by
  obtain ⟨ha, -, -, -, hc, -, -, -⟩ := raneyEntry_le hM
  refine ⟨ha, hc, fun h => ?_⟩
  have hdet : M.det = 0 := by simp [det, h.1, h.2]
  have := isRD_det_ne hD hM
  exact this hdet

/-- **Vandehey Lemma 2.2, run form.**  Ingesting one CF digit emits at most `M.b + M.d`
alternations — a bound with NO dependence on the ingested digit `j`. -/
theorem numAlt_lrOut_le (hD : 0 < D) (M : RState D) (j : ℕ) :
    (numAlt (lrOut hD M j) : ℤ) ≤ M.val.b + M.val.d := by
  obtain ⟨h1, h2⟩ := lrStep_col hD M j
  obtain ⟨ha, hc, hne⟩ := isRD_fst_col hD (lrDelta hD M j).2
  have hcol : colApp (lrProd (lrOut hD M j)) ((lrDelta hD M j).val.a, (lrDelta hD M j).val.c)
      = (M.val.b, M.val.d) := by
    simp only [colApp, Prod.mk.injEq]
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨-, -, -, hnum, -, -⟩ := numAlt_le_colApp (lrOut hD M j) ha hc hne
  rw [hcol] at hnum
  exact hnum

/-- **The uniform form**: at most `2D` alternations per ingested digit, for every state and
every digit.  This is the constant Vandehey's Lemma 2.2 provides. -/
theorem numAlt_lrOut_le_two_mul (hD : 0 < D) (M : RState D) (j : ℕ) :
    numAlt (lrOut hD M j) ≤ 2 * D := by
  have h := numAlt_lrOut_le hD M j
  obtain ⟨-, -, -, hb, -, -, -, hd⟩ := raneyEntry_le M.2
  have : (numAlt (lrOut hD M j) : ℤ) ≤ 2 * (D : ℤ) := by omega
  exact_mod_cast this

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms numAlt_le_colApp
#print axioms numAlt_lrOut_le
#print axioms numAlt_lrOut_le_two_mul
end
