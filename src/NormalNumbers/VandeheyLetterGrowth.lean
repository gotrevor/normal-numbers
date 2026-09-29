/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyLRTrigger

/-!
# The lower Lemma 2.2: the Raney transducer emits at least `~|q|/2` letters

Vandehey's Lemma 2.2 bounds the emitted RUNS per ingested digit from ABOVE
(`VandeheyRunBound.numAlt_lrOut_le_two_mul`).  The tail hypothesis `htail` of the output
engine needs the companion bound from BELOW: a genuine input word of length `m` cannot be
digested into fewer than about `m/2` output letters.

## The mechanism

The transducer identity (`lrBlocks_run`, the word-level `lrRun_eq`) reads

  `t · B_{a₁} ⋯ B_{a_m} = lrProd w · t'`,  `w` the emitted letter word, `t'` a Raney state.

Both sides are nonnegative, so compare entry sums (`norm1`).

* **Right, from above.**  Multiplying by `L` or `R` at most doubles the entry sum
  (`norm1_lr_mul_le`), and a Raney state's entries are at most `D` (`raneyEntry_le`), so
  `norm1 (lrProd w · t') ≤ 2 ^ |w| · 4D`.
* **Left, from below.**  On column sums, ingesting a digit `j ≥ 1` acts by
  `(c₁, c₂) ↦ (c₂, c₁ + j·c₂)` (`col_mul_B`) — the Fibonacci recursion.  So
  `c₂ (t · B_{a₁} ⋯ B_{a_m}) ≥ fib (m+1) · c₂ t ≥ fib (m+1)`, the last step because
  `c₂ t = 0` would force `det t = 0`.

Since `fib (2K+1) ≥ 2 ^ K` and `4D ≤ 2 ^ (D+2)`, the two bounds give
`(m-1)/2 ≤ |w| + D + 2`, i.e. `m ≤ 2|w| + 2D + 6`: **`genuine_length_le`**.

## What it buys

`htail` becomes trivial: a nonzero trigger multiplicity `kOut v q t ≠ 0` forces the letters
emitted by the INTERIOR digits of `q` to number fewer than `|v|` (the occurrence starts in the
first block and is completed by the last digit), so `|q|` is bounded in terms of `|v|` and `D`
alone, and the trigger prefix set is EMPTY at every length beyond that bound.  See
`VandeheyLRTail`.
-/

namespace NormalNumbers.VandeheyLR

open Mat2 VandeheyAut VandeheyOut

/-! ## Entry sums and column sums -/

namespace Mat2Norm

/-- The entry sum, a norm on nonnegative matrices. -/
def norm1 (M : Mat2) : ℤ := M.a + M.b + M.c + M.d

/-- The first column's sum. -/
def col1 (M : Mat2) : ℤ := M.a + M.c

/-- The second column's sum. -/
def col2 (M : Mat2) : ℤ := M.b + M.d

lemma col2_le_norm1 {M : Mat2} (h : Nonneg M) : col2 M ≤ norm1 M := by
  obtain ⟨ha, -, hc, -⟩ := h
  simp only [norm1, col2]; linarith

lemma norm1_nonneg {M : Mat2} (h : Nonneg M) : 0 ≤ norm1 M := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  simp only [norm1]; linarith

/-- **Right multiplication by `B j` is the Fibonacci step on column sums.** -/
lemma col_mul_B (M : Mat2) (j : ℕ) :
    col1 (M * B j) = col2 M ∧ col2 (M * B j) = col1 M + (j : ℤ) * col2 M := by
  constructor <;> simp only [col1, col2, mul_def, mul, B] <;> ring

/-- **Left multiplication by `L` or `R` at most doubles the entry sum.** -/
lemma norm1_lr_mul_le {M : Mat2} (h : Nonneg M) (b : Bool) :
    norm1 ((if b then lrL else lrR) * M) ≤ 2 * norm1 M := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  cases b <;> simp only [if_pos, if_neg, mul_def, mul, lrL, lrR, norm1] <;> simp <;> linarith

/-- The entry sum of `lrProd w · N` is at most `2 ^ |w|` times that of `N`. -/
lemma norm1_lrProd_mul_le : ∀ (w : List Bool) {N : Mat2}, Nonneg N →
    norm1 (lrProd w * N) ≤ 2 ^ w.length * norm1 N
  | [], N, hN => by simp [lrProd]
  | (b :: w), N, hN => by
      have hrec := norm1_lrProd_mul_le w hN
      have hnn : Nonneg (lrProd w * N) := Mat2.Nonneg.mul (nonneg_lrProd w) hN
      have hstep := norm1_lr_mul_le hnn b
      rw [lrProd_cons, mul_assoc']
      calc norm1 ((if b then lrL else lrR) * (lrProd w * N))
          ≤ 2 * norm1 (lrProd w * N) := hstep
        _ ≤ 2 * (2 ^ w.length * norm1 N) := by
            have : (0 : ℤ) ≤ 2 := by norm_num
            exact mul_le_mul_of_nonneg_left hrec this
        _ = 2 ^ (b :: w).length * norm1 N := by
            simp [List.length_cons, pow_succ]; ring

end Mat2Norm

open Mat2Norm

/-! ## The Fibonacci lower bound on column sums -/

/-- `2 ^ K ≤ fib (2K+1)`: the Fibonacci numbers double every two steps. -/
lemma two_pow_le_fib : ∀ K : ℕ, 2 ^ K ≤ Nat.fib (2 * K + 1)
  | 0 => by simp
  | (K + 1) => by
      have ih := two_pow_le_fib K
      have hmono : Nat.fib (2 * K + 1) ≤ Nat.fib (2 * K + 2) := Nat.fib_mono (by omega)
      have hsum : Nat.fib (2 * (K + 1) + 1) = Nat.fib (2 * K + 1) + Nat.fib (2 * K + 1 + 1) := by
        have h : 2 * (K + 1) + 1 = (2 * K + 1) + 2 := by ring
        rw [h, Nat.fib_add_two]
      have hmono' : Nat.fib (2 * K + 1) ≤ Nat.fib (2 * K + 1 + 1) := Nat.fib_mono (by omega)
      have h2 : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by ring
      omega

/-- **Fibonacci growth of a `B`-product's second column.**  Ingesting a genuine digit acts by
`(c₁, c₂) ↦ (c₂, c₁ + j·c₂)` with `j ≥ 1`, which dominates the Fibonacci recursion. -/
lemma fib_col_le : ∀ (q : List ℕ), (∀ e ∈ q, 1 ≤ e) → ∀ {M : Mat2}, Nonneg M →
    (Nat.fib q.length : ℤ) * col1 M + (Nat.fib (q.length + 1) : ℤ) * col2 M
      ≤ col2 (M * bProd q)
  | [], _, M, hM => by
      have hc1 : 0 ≤ col1 M := by
        obtain ⟨ha, -, hc, -⟩ := hM; simp only [col1]; linarith
      simp only [bProd_nil, mul_one', List.length_nil, Nat.fib_zero, Nat.fib_one,
        Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add]
      linarith
  | (a :: q), hgen, M, hM => by
      have ha1 : 1 ≤ a := hgen a (by simp)
      have hgen' : ∀ e ∈ q, 1 ≤ e := fun e he => hgen e (by simp [he])
      have hMB : Nonneg (M * B a) := Mat2.Nonneg.mul hM (nonneg_B a)
      have ih := fib_col_le q hgen' hMB
      obtain ⟨hc1eq, hc2eq⟩ := col_mul_B M a
      have hc1 : 0 ≤ col1 M := by
        obtain ⟨ha', -, hc, -⟩ := hM; simp only [col1]; linarith
      have hc2 : 0 ≤ col2 M := by
        obtain ⟨-, hb, -, hd⟩ := hM; simp only [col2]; linarith
      have hassoc : M * bProd (a :: q) = (M * B a) * bProd q := by
        rw [bProd_cons, mul_assoc']
      rw [hassoc]
      refine le_trans ?_ ih
      rw [hc1eq, hc2eq]
      have hacol : col2 M ≤ (a : ℤ) * col2 M := by
        have h1 : (1 : ℤ) * col2 M ≤ (a : ℤ) * col2 M := by
          refine mul_le_mul_of_nonneg_right ?_ hc2
          exact_mod_cast ha1
        linarith
      have hfib : Nat.fib (q.length + 1 + 1) = Nat.fib q.length + Nat.fib (q.length + 1) :=
        Nat.fib_add_two
      have hF1 : (0 : ℤ) ≤ (Nat.fib (q.length + 1) : ℤ) := Int.natCast_nonneg _
      have hexp : (Nat.fib (q.length + 1) : ℤ) * (col1 M + (a : ℤ) * col2 M)
          ≥ (Nat.fib (q.length + 1) : ℤ) * (col1 M + col2 M) := by
        refine mul_le_mul_of_nonneg_left (by linarith) hF1
      simp only [List.length_cons, hfib]
      push_cast
      nlinarith [hexp, Int.natCast_nonneg (Nat.fib q.length)]

/-! ## The letter word of an arbitrary input word -/

variable {D : ℕ}

/-- The `L/R` word emitted by running the input word `q` from state `t` — the word-level
version of `VandeheyLRTransducer.lrWord`. -/
noncomputable def lrBlocks (hD : 0 < D) : RState D → List ℕ → List Bool
  | _, [] => []
  | t, (a :: q) => lrOut hD t a ++ lrBlocks hD (lrDelta hD t a) q

@[simp] lemma lrBlocks_nil (hD : 0 < D) (t : RState D) : lrBlocks hD t [] = [] := rfl

lemma lrBlocks_cons (hD : 0 < D) (t : RState D) (a : ℕ) (q : List ℕ) :
    lrBlocks hD t (a :: q) = lrOut hD t a ++ lrBlocks hD (lrDelta hD t a) q := rfl

/-- The encoded output of `VandeheyTrigger.blocksOf` is `lrBlocks` relabelled, so the two have
the same length. -/
lemma length_blocksOf_eq (hD : 0 < D) : ∀ (t : RState D) (q : List ℕ),
    (blocksOf (lrDelta hD) (lrOutN hD) t q).length = (lrBlocks hD t q).length
  | _, [] => by simp
  | t, (a :: q) => by
      rw [blocksOf_cons, lrBlocks_cons, List.length_append, List.length_append,
        length_blocksOf_eq hD (lrDelta hD t a) q, lrOutN, List.length_map]

/-- **The word-level transducer identity.**  `lrRun_eq` for an arbitrary input word. -/
theorem lrBlocks_run (hD : 0 < D) : ∀ (t : RState D) (q : List ℕ),
    t.val * bProd q = lrProd (lrBlocks hD t q) * (runState (lrDelta hD) t q).val
  | t, [] => by simp
  | t, (a :: q) => by
      calc t.val * bProd (a :: q) = (t.val * B a) * bProd q := by rw [bProd_cons, ← mul_assoc']
        _ = (lrProd (lrOut hD t a) * (lrDelta hD t a).val) * bProd q := by rw [lrStep_spec]
        _ = lrProd (lrOut hD t a) * ((lrDelta hD t a).val * bProd q) := mul_assoc' _ _ _
        _ = lrProd (lrOut hD t a)
              * (lrProd (lrBlocks hD (lrDelta hD t a) q)
                  * (runState (lrDelta hD) (lrDelta hD t a) q).val) := by
              rw [lrBlocks_run hD (lrDelta hD t a) q]
        _ = lrProd (lrBlocks hD t (a :: q)) * (runState (lrDelta hD) t (a :: q)).val := by
              rw [lrBlocks_cons, lrProd_append, runState_cons, mul_assoc']

/-! ## The growth bound -/

/-- A Raney state's second column is nonzero: otherwise its determinant would vanish. -/
lemma one_le_col2 (hD : 0 < D) (t : RState D) : 1 ≤ col2 t.val := by
  obtain ⟨hdet, hnn, -⟩ := t.2
  obtain ⟨ha, hb, hc, hd⟩ := hnn
  by_contra hcon
  have hb0 : t.val.b = 0 := by simp only [col2] at hcon; omega
  have hd0 : t.val.d = 0 := by simp only [col2] at hcon; omega
  have : t.val.det = 0 := by simp [det, hb0, hd0]
  have hD' : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  rcases hdet with h | h <;> rw [this] at h <;> omega

/-- `4D ≤ 2 ^ (D + 2)`. -/
lemma four_mul_le_two_pow (D : ℕ) : 4 * D ≤ 2 ^ (D + 2) := by
  have h : D ≤ 2 ^ D := Nat.le_of_lt_succ (Nat.lt_two_pow_self.trans_le (by omega))
  calc 4 * D ≤ 4 * 2 ^ D := by omega
    _ = 2 ^ (D + 2) := by rw [pow_add]; ring

/-- **The lower Lemma 2.2.**  A genuine input word of length `m`, digested from ANY Raney state,
emits at least `(m - 2D - 6)/2` output letters.  Equivalently `m ≤ 2·(letters) + 2D + 6`. -/
theorem genuine_length_le (hD : 0 < D) (t : RState D) (q : List ℕ)
    (hgen : ∀ e ∈ q, 1 ≤ e) :
    q.length ≤ 2 * (lrBlocks hD t q).length + 2 * D + 6 := by
  classical
  set m : ℕ := q.length with hm
  set w : List Bool := lrBlocks hD t q with hw
  set t' : RState D := runState (lrDelta hD) t q with ht'
  -- the lower bound on the left-hand side
  have hnn : Nonneg t.val := t.2.2.1
  have hlow : (Nat.fib (m + 1) : ℤ) ≤ col2 (t.val * bProd q) := by
    have h := fib_col_le q hgen hnn
    have hc1 : 0 ≤ col1 t.val := by
      obtain ⟨ha, -, hc, -⟩ := hnn; simp only [col1]; linarith
    have hc2 := one_le_col2 hD t
    have hF : (0 : ℤ) ≤ (Nat.fib m : ℤ) := Int.natCast_nonneg _
    have hF1 : (0 : ℤ) ≤ (Nat.fib (m + 1) : ℤ) := Int.natCast_nonneg _
    nlinarith [h, mul_le_mul_of_nonneg_left hc2 hF1, mul_nonneg hF hc1]
  -- the upper bound on the right-hand side
  have hnn' : Nonneg t'.val := t'.2.2.1
  have hub : col2 (t.val * bProd q) ≤ 2 ^ w.length * (4 * D : ℤ) := by
    rw [lrBlocks_run hD t q]
    have h1 : col2 (lrProd w * t'.val) ≤ norm1 (lrProd w * t'.val) :=
      col2_le_norm1 (Mat2.Nonneg.mul (nonneg_lrProd w) hnn')
    have h2 := norm1_lrProd_mul_le w hnn'
    have h3 : norm1 t'.val ≤ (4 * D : ℤ) := by
      obtain ⟨h0a, hab, h0b, hbb, h0c, hcb, h0d, hdb⟩ := raneyEntry_le t'.2
      simp only [norm1]; push_cast; linarith
    have h4 : (0 : ℤ) ≤ 2 ^ w.length := by positivity
    calc col2 (lrProd w * t'.val) ≤ norm1 (lrProd w * t'.val) := h1
      _ ≤ 2 ^ w.length * norm1 t'.val := h2
      _ ≤ 2 ^ w.length * (4 * D : ℤ) := mul_le_mul_of_nonneg_left h3 h4
  -- combine: fib (m+1) ≤ 2 ^ (|w| + D + 2)
  have hcomb : Nat.fib (m + 1) ≤ 2 ^ (w.length + D + 2) := by
    have h : (Nat.fib (m + 1) : ℤ) ≤ 2 ^ w.length * (4 * D : ℤ) := hlow.trans hub
    have h4D : (4 * D : ℤ) ≤ (2 : ℤ) ^ (D + 2) := by
      have := four_mul_le_two_pow D
      exact_mod_cast this
    have h4 : (0 : ℤ) ≤ 2 ^ w.length := by positivity
    have h2 : (Nat.fib (m + 1) : ℤ) ≤ 2 ^ w.length * (2 : ℤ) ^ (D + 2) :=
      h.trans (mul_le_mul_of_nonneg_left h4D h4)
    have hsplit : w.length + D + 2 = w.length + (D + 2) := by ring
    have h3 : (Nat.fib (m + 1) : ℤ) ≤ ((2 ^ (w.length + D + 2) : ℕ) : ℤ) := by
      push_cast
      rw [hsplit, pow_add]
      exact h2
    exact_mod_cast h3
  -- and `2 ^ K ≤ fib (2K+1)` with `2K+1 ≤ m+1` closes it
  by_contra hcon
  set K : ℕ := w.length + D + 3 with hK
  have hKm : 2 * K + 1 ≤ m + 1 := by omega
  have h1 : 2 ^ K ≤ Nat.fib (2 * K + 1) := two_pow_le_fib K
  have h2 : Nat.fib (2 * K + 1) ≤ Nat.fib (m + 1) := Nat.fib_mono hKm
  have h3 : 2 ^ (w.length + D + 2) < 2 ^ K := by
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    omega
  omega

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms Mat2Norm.norm1_lrProd_mul_le
#print axioms two_pow_le_fib
#print axioms fib_col_le
#print axioms lrBlocks_run
#print axioms length_blocksOf_eq
#print axioms genuine_length_le
end
