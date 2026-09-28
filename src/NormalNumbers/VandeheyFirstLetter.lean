/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyTransportB

/-!
# The first emitted letter is the determinant's sign

The one structural fact that makes the emitted RUN count grow linearly:

> **the first letter of a nonempty emitted block is `L` exactly when `det M > 0`.**

Since `det (M · B_j) = − det M` (`det_lrDelta`), the phase alternates at every ingested digit,
so consecutive nonempty blocks START with opposite letters.  Hence over any two consecutive
steps there is at least one alternation: either the first block already alternates internally,
or it is constant, and then its last letter is its first letter — the opposite of the next
block's first letter, so the seam alternates.

    `altOut sᵢ jᵢ + altOut sᵢ₊₁ jᵢ₊₁ ≥ 1`

which is exactly the lower bound `outLenLimit_pos` needs, at window length 2 instead of 1.

The proof of the headline fact is short: `M · B_j = lrProd w · M'` with `M'` nonnegative, so if
`w` starts with `L = [[1,0],[1,1]]` then row 2 of `M · B_j` dominates row 1; reading off the
first column, `M.b ≤ M.d`, which excludes the balance branch `a < c, d < b`.  And a balanced
matrix has `det > 0` exactly on the other branch (`det_pos_iff_branch`).
-/

namespace NormalNumbers

namespace Mat2

/-- **The balance branch IS the determinant's sign.** -/
lemma det_pos_iff_branch {M : Mat2} (h : Balanced M) :
    0 < M.det ↔ (M.c < M.a ∧ M.b < M.d) := by
  obtain ⟨⟨ha, hb, hc, hd⟩, hbr⟩ := h
  constructor
  · intro hpos
    rcases hbr with h1 | h2
    · exact h1
    · exfalso
      rw [det] at hpos
      nlinarith [h2.1, h2.2]
  · intro h1
    rw [det]
    nlinarith [h1.1, h1.2]

end Mat2

namespace VandeheyLR

open Mat2

variable {D : ℕ}

/-- **The first emitted letter is determined by the phase.**  `L` iff the determinant is
positive. -/
theorem head_lrOut_eq_true_iff (hD : 0 < D) (M : RState D) (j : ℕ) {b : Bool}
    {rest : List Bool} (h : lrOut hD M j = b :: rest) :
    b = true ↔ 0 < M.val.det := by
  have hspec := lrStep_spec hD M j
  rw [h] at hspec
  set M' := (lrDelta hD M j).val with hM'
  have hM'nn : Nonneg M' := (lrDelta hD M j).2.2.1
  set X := lrProd rest * M' with hX
  have hXnn : Nonneg X := nonneg_lrProd_mul hM'nn
  have hb : (M.val * B j).a = M.val.b := by simp [mul_def, mul, B]
  have hd : (M.val * B j).c = M.val.d := by simp [mul_def, mul, B]
  have hbal := M.2.2
  cases b with
  | true =>
    have hfac : M.val * B j = lrL * X := by
      rw [hspec, lrProd_cons_true, mul_assoc']
    have h1 : M.val.b = X.a := by rw [← hb, hfac]; simp [mul_def, mul, lrL]
    have h2 : M.val.d = X.a + X.c := by rw [← hd, hfac]; simp [mul_def, mul, lrL]
    have hle : M.val.b ≤ M.val.d := by
      have := hXnn.2.2.1
      omega
    have hbr : M.val.c < M.val.a ∧ M.val.b < M.val.d := by
      rcases hbal.2 with h3 | h3
      · exact h3
      · exact absurd h3.2 (by omega)
    simp only [true_iff]
    exact (Mat2.det_pos_iff_branch hbal).mpr hbr
  | false =>
    have hfac : M.val * B j = lrR * X := by
      rw [hspec, lrProd_cons_false, mul_assoc']
    have h1 : M.val.b = X.a + X.c := by rw [← hb, hfac]; simp [mul_def, mul, lrR]
    have h2 : M.val.d = X.c := by rw [← hd, hfac]; simp [mul_def, mul, lrR]
    have hle : M.val.d ≤ M.val.b := by
      have := hXnn.1
      omega
    have hnbr : ¬ (M.val.c < M.val.a ∧ M.val.b < M.val.d) := by
      rintro ⟨-, h4⟩
      omega
    exact ⟨fun hcon => absurd hcon (by simp),
      fun hpos => absurd ((Mat2.det_pos_iff_branch hbal).mp hpos) hnbr⟩

end VandeheyLR

end NormalNumbers

section
#print axioms NormalNumbers.Mat2.det_pos_iff_branch
#print axioms NormalNumbers.VandeheyLR.head_lrOut_eq_true_iff
end
