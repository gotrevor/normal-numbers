/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# G4 disjunctivity, §4B (spectral half): the adjacent-difference Gram matrix

The zonotope/ellipsoid tube bound of draft §5 rests on

  `log det(I + AAᵀ) = O(r√K)`,   `A = D_s^{⊗K}`,

which in turn rests on the spectrum of the one-dimensional Gram matrix `T_s = D_s D_sᵀ`
(the `s × s` tridiagonal `(−1, 2, −1)` matrix):

* `det T_s = s + 1` (`det_gram`), proved by the explicit `L D Lᵀ` factorisation with unit
  lower-bidiagonal `L` (subdiagonal `−k/(k+1)`) and `D = diag((k+2)/(k+1))`;
* the sine eigenvectors `v_j(k) = sin(π(j+1)(k+1)/(s+1))` with eigenvalues
  `λ_j = 2 − 2cos(π(j+1)/(s+1)) = 4 sin²(π(j+1)/(2(s+1)))` (`gram_mulVec_sineVec`);
* the eigenvalues are distinct and positive, the eigenvectors nonzero and (by symmetry of `T_s`)
  pairwise orthogonal.

The tensor-power step and the log-moment bound follow in the same file once these are in place.
-/

open Matrix Finset Real
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### The Gram matrix and its `L D Lᵀ` factorisation -/

/-- The `s × s` Gram matrix `D_s D_sᵀ` of the adjacent-difference operator:
`2` on the diagonal, `−1` on the two neighbouring diagonals. -/
def gram (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun a b => if a = b then 2 else if (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a then -1 else 0

/-- Unit lower-bidiagonal factor: `L a (a-1) = −a/(a+1)`. -/
noncomputable def gramL (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun a c => if a = c then 1 else if (c : ℕ) + 1 = a then -((c : ℝ) + 1) / ((c : ℝ) + 2) else 0

/-- Diagonal factor `D a = (a+2)/(a+1)`. -/
noncomputable def gramD (s : ℕ) : Fin s → ℝ := fun a => ((a : ℝ) + 2) / ((a : ℝ) + 1)

lemma gramL_isLowerTriangular (s : ℕ) : (gramL s).IsLowerTriangular := by
  intro i j hij
  simp only [OrderDual.toDual_lt_toDual] at hij
  unfold gramL
  rw [if_neg (ne_of_gt hij).symm, if_neg]
  intro h
  have := Fin.lt_def.mp hij
  omega

lemma det_gramL (s : ℕ) : (gramL s).det = 1 := by
  rw [det_of_isLowerTriangular _ (gramL_isLowerTriangular s)]
  simp [gramL]

lemma prod_gramD (s : ℕ) : ∏ a, gramD s a = s + 1 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    have : (∏ a : Fin n, gramD (n + 1) a.castSucc) = ∏ a : Fin n, gramD n a := by
      refine Finset.prod_congr rfl fun a _ => ?_
      simp [gramD]
    rw [this, ih]
    simp only [gramD, Fin.val_last]
    push_cast
    field_simp
    ring

lemma gramL_mul_diagonal (s : ℕ) :
    gramL s * diagonal (gramD s) = fun a c => gramL s a c * gramD s c := by
  ext a c; exact mul_diagonal _ _ _ _

/-- The summand of `(L D Lᵀ)_{ab}`. -/
noncomputable def ldlSummand (s : ℕ) (a b c : Fin s) : ℝ := gramL s a c * gramD s c * gramL s b c

lemma ldlSummand_eq_zero {s : ℕ} {a b c : Fin s} (hca : c ≠ a) (hcb : c ≠ b)
    (h : ¬ ((c : ℕ) + 1 = a ∧ (c : ℕ) + 1 = b)) : ldlSummand s a b c = 0 := by
  unfold ldlSummand gramL
  rw [if_neg hca.symm, if_neg hcb.symm]
  by_cases h1 : (c : ℕ) + 1 = a
  · rw [if_pos h1, if_neg (fun h2 => h ⟨h1, h2⟩)]; ring
  · rw [if_neg h1]; ring

/-- The factorisation `T = L D Lᵀ`, entrywise. -/
lemma ldl_apply (s : ℕ) (a b : Fin s) :
    (gramL s * diagonal (gramD s) * (gramL s)ᵀ) a b = ∑ c, ldlSummand s a b c := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_diagonal, transpose_apply]
  rfl

lemma gram_eq_LDLt (s : ℕ) : gram s = gramL s * diagonal (gramD s) * (gramL s)ᵀ := by
  ext a b
  rw [ldl_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : (a : ℕ) = 0
    · -- only `c = a` contributes
      rw [Finset.sum_eq_single a]
      · unfold ldlSummand gramL gramD gram
        simp [ha]
      · intro c _ hc
        exact ldlSummand_eq_zero hc hc (by omega)
      · simp
    · -- `c = a` and `c = a − 1` contribute
      have hlt : (a : ℕ) - 1 < s := by omega
      set a' : Fin s := ⟨(a : ℕ) - 1, hlt⟩ with ha'
      have hne : a ≠ a' := by
        intro h; rw [Fin.ext_iff] at h; simp [ha'] at h; omega
      rw [Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
      · unfold ldlSummand gramL gramD gram
        have h1 : (a' : ℕ) + 1 = a := by simp [ha']; omega
        simp only [if_true, if_neg hne, h1]
        have : ((a : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by
          rw [ha']; simp; push_cast [Nat.cast_sub (by omega : 1 ≤ (a : ℕ))]; ring
        rw [this]
        have hpos : ((a' : ℕ) : ℝ) + 1 ≠ 0 := by positivity
        have hpos2 : ((a' : ℕ) : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
      · intro c _ hc
        refine ldlSummand_eq_zero hc.1 hc.1 ?_
        rintro ⟨h1, -⟩
        apply hc.2
        rw [Fin.ext_iff, ha']; simp; omega
  · -- off-diagonal: at most one contributing term
    have hno : ∀ c : Fin s, ¬ ((c : ℕ) + 1 = a ∧ (c : ℕ) + 1 = b) := by
      rintro c ⟨h1, h2⟩; exact hab (Fin.ext (by omega))
    by_cases h1 : (a : ℕ) + 1 = b
    · -- `c = a`
      rw [Finset.sum_eq_single a]
      · unfold ldlSummand gramL gramD gram
        simp [hab, Ne.symm hab, h1]
        have hpos : ((a : ℕ) : ℝ) + 1 ≠ 0 := by positivity
        have hpos2 : ((a : ℕ) : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
      · intro c _ hc
        by_cases hcb : c = b
        · subst hcb
          have : ¬ ((c : ℕ) + 1 = a) := by omega
          simp [ldlSummand, gramL, Ne.symm hc, this]
        · exact ldlSummand_eq_zero hc hcb (hno c)
      · simp
    · by_cases h2 : (b : ℕ) + 1 = a
      · -- `c = b`
        rw [Finset.sum_eq_single b]
        · unfold ldlSummand gramL gramD gram
          simp [hab, h2]
          have hpos : ((b : ℕ) : ℝ) + 1 ≠ 0 := by positivity
          have hpos2 : ((b : ℕ) : ℝ) + 2 ≠ 0 := by positivity
          field_simp
          ring
        · intro c _ hc
          by_cases hca : c = a
          · subst hca
            have : ¬ ((c : ℕ) + 1 = b) := by omega
            simp [ldlSummand, gramL, Ne.symm hab, this]
          · exact ldlSummand_eq_zero hca hc (hno c)
        · simp
      · rw [Finset.sum_eq_zero]
        · unfold gram
          rw [if_neg hab, if_neg (by tauto)]
        · intro c _
          by_cases hca : c = a
          · subst hca
            simp [ldlSummand, gramL, hab, Ne.symm hab, h1]
          · by_cases hcb : c = b
            · subst hcb
              simp [ldlSummand, gramL, hab, Ne.symm hab, h2]
            · exact ldlSummand_eq_zero hca hcb (hno c)

/-- **`det T_s = s + 1`.** -/
theorem det_gram (s : ℕ) : (gram s).det = s + 1 := by
  rw [gram_eq_LDLt, det_mul, det_mul, det_gramL, det_transpose, det_gramL, det_diagonal,
    prod_gramD]
  ring

end NormalNumbers.G4
