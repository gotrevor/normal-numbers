/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# G4 disjunctivity, §4B: `det (I + A_G A_Gᵀ) ≤ det (I + A Aᵀ)` for a row restriction `A_G`

The tube bound of draft §5 needs the spectral estimate for the *principal row restrictions*
`A_G` of `A`, not only for `A`.  We reduce it to the full matrix:

* `det_le_det_add_vecMulVec_self` — matrix determinant lemma:
  `det N ≤ det (N + u uᵀ)` for positive-definite `N` (since `uᵀ N⁻¹ u ≥ 0`);
* `det_le_det_add_sum_vecMulVec` — its finite-sum iteration, with positivity preserved;
* `det_one_add_submatrix_mul_transpose_le` — via Weinstein–Aronszajn,
  `det (I + Bᵀ B)` with `Bᵀ B = ∑_{i ∈ G} aᵢ aᵢᵀ ≤ ∑_{all i} aᵢ aᵢᵀ = Aᵀ A`.
-/

open Matrix Finset
open scoped BigOperators

namespace NormalNumbers.G4

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Matrix determinant lemma, inequality form:** `det N ≤ det (N + u uᵀ)` for `N ≻ 0`. -/
theorem det_le_det_add_vecMulVec_self {N : Matrix n n ℝ} (hN : N.PosDef) (u : n → ℝ) :
    N.det ≤ (N + vecMulVec u u).det := by
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  rw [vecMulVec_eq Unit, Matrix.det_add_replicateCol_mul_replicateRow hdet,
    det_unique (1 + replicateRow Unit u * N⁻¹ * replicateCol Unit u),
    Matrix.add_apply, Matrix.one_apply_eq, ← replicateRow_vecMul,
    replicateRow_mul_replicateCol_apply, ← dotProduct_mulVec]
  have hq : 0 ≤ u ⬝ᵥ (N⁻¹ *ᵥ u) := by
    have := hN.inv.posSemidef.dotProduct_mulVec_nonneg u
    simpa using this
  have hpos : 0 < N.det := hN.det_pos
  nlinarith

omit [DecidableEq n] in
theorem posDef_add_vecMulVec_self {N : Matrix n n ℝ} (hN : N.PosDef) (u : n → ℝ) :
    (N + vecMulVec u u).PosDef := by
  have := posSemidef_vecMulVec_self_star u
  rw [star_trivial] at this
  exact hN.add_posSemidef this

/-- Iterating: adding any finite sum of `uᵢ uᵢᵀ` to a positive-definite `N` keeps positivity
and does not decrease the determinant. -/
theorem det_le_det_add_sum_vecMulVec {ι : Type*} {N : Matrix n n ℝ} (hN : N.PosDef)
    (u : ι → n → ℝ) (S : Finset ι) :
    N.det ≤ (N + ∑ i ∈ S, vecMulVec (u i) (u i)).det
      ∧ (N + ∑ i ∈ S, vecMulVec (u i) (u i)).PosDef := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hN]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, add_comm (vecMulVec (u a) (u a)) _, ← add_assoc]
    exact ⟨ih.1.trans (det_le_det_add_vecMulVec_self ih.2 (u a)),
      posDef_add_vecMulVec_self ih.2 (u a)⟩

omit [Fintype n] [DecidableEq n] in
/-- `Aᵀ A = ∑ᵢ aᵢ aᵢᵀ` over the rows `aᵢ = A i`. -/
theorem transpose_mul_self_eq_sum_vecMulVec {m : Type*} [Fintype m] (A : Matrix m n ℝ) :
    Aᵀ * A = ∑ i, vecMulVec (A i) (A i) := by
  ext a b
  simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]

/-- **Row restriction does not increase `det (I + A Aᵀ)`.**  For an injective row selection
`e : ι → m` and `A_G = A.submatrix e id`, `det (1 + A_G A_Gᵀ) ≤ det (1 + A Aᵀ)`. -/
theorem det_one_add_submatrix_mul_transpose_le {m ι : Type*} [Fintype m] [DecidableEq m]
    [Fintype ι] [DecidableEq ι] (A : Matrix m n ℝ) (e : ι → m) (he : Function.Injective e) :
    (1 + A.submatrix e id * (A.submatrix e id)ᵀ).det ≤ (1 + A * Aᵀ).det := by
  rw [det_one_add_mul_comm (A.submatrix e id), det_one_add_mul_comm A,
    transpose_mul_self_eq_sum_vecMulVec, transpose_mul_self_eq_sum_vecMulVec]
  have hB : ∑ i : ι, vecMulVec (A.submatrix e id i) (A.submatrix e id i)
      = ∑ i ∈ Finset.univ.image e, vecMulVec (A i) (A i) := by
    rw [Finset.sum_image (fun x _ y _ h => he h)]
    rfl
  rw [hB, ← Finset.sum_add_sum_compl (Finset.univ.image e) (fun i => vecMulVec (A i) (A i)),
    ← add_assoc]
  exact (det_le_det_add_sum_vecMulVec
    (det_le_det_add_sum_vecMulVec Matrix.PosDef.one (fun i => A i) (Finset.univ.image e)).2
    (fun i => A i) _).1

end NormalNumbers.G4
