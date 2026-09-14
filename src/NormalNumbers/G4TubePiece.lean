/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Tensor
import NormalNumbers.G4DetMonotone
import NormalNumbers.G4Ellipsoid

/-!
# G4 disjunctivity, §4B: volume of one tube piece `η [A_G, I_g] [-1,1]^{H+g}`

Assembles the three B-lemmas:

* `volume_image_le` (ellipsoid bound) for `L = [A_G, I_g]`, whose Gram matrix is
  `L Lᵀ = I + A_G A_Gᵀ`;
* `det_one_add_submatrix_mul_transpose_le` (row restriction);
* `log_det_one_add_tensorGram_le'` (the `O(r√K)` spectral bound at `s = K²`).

Result (`volume_tubePiece_le`): for `A = D_{K²}^{⊗K}` and any injective row selection `e`,

  `vol ([A_G, I_g] '' cube) ≤ exp(½ r (log 2 + 23√K)) · (√(2πe (H+g)/g))^g`,   `r = (K²)^K`.

The factor `η^g` for the scaled cube follows from `addHaar_smul`.
-/

open Matrix MeasureTheory Real
open scoped BigOperators ENNReal

namespace NormalNumbers.G4

section general
variable {g H : Type*} [Fintype g] [Fintype H] [DecidableEq g] [DecidableEq H]

/-- `[A, I]` as a matrix on `H ⊕ g`. -/
def augmented (A : Matrix g H ℝ) : Matrix g (H ⊕ g) ℝ := fromCols A 1

lemma augmented_mul_transpose (A : Matrix g H ℝ) :
    augmented A * (augmented A)ᵀ = 1 + A * Aᵀ := by
  unfold augmented
  rw [transpose_fromCols, fromCols_mul_fromRows, transpose_one, Matrix.mul_one, add_comm]

lemma posDef_one_add_mul_transpose (A : Matrix g H ℝ) : (1 + A * Aᵀ).PosDef := by
  have := posSemidef_self_mul_conjTranspose A
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact Matrix.PosDef.one.add_posSemidef this

/-- The ellipsoid bound for `[A, I]` on the unit sup-cube of `ℝ^{H ⊕ g}`. -/
theorem volume_augmented_image_le (A : Matrix g H ℝ) (hg : 0 < Fintype.card g) :
    (volume ((Matrix.toLin' (augmented A)) '' Metric.closedBall (0 : H ⊕ g → ℝ) 1)).toReal
      ≤ Real.sqrt (1 + A * Aᵀ).det
        * (Real.sqrt (2 * π * Real.exp 1 / Fintype.card g)
            * Real.sqrt (Fintype.card (H ⊕ g))) ^ Fintype.card g := by
  have hM : (augmented A * (augmented A)ᵀ).PosDef := by
    rw [augmented_mul_transpose]; exact posDef_one_add_mul_transpose A
  have hR : (0 : ℝ) < Real.sqrt (Fintype.card (H ⊕ g)) := by
    rw [Real.sqrt_pos, Fintype.card_sum]
    have : 0 < Fintype.card g + 0 := by omega
    exact_mod_cast (Nat.lt_of_lt_of_le this (by omega))
  have := volume_image_le hM hR closedBall_subset_eball hg
  rwa [augmented_mul_transpose] at this

end general

/-! ### Specialisation to `A = D_{K²}^{⊗K}` and a row restriction -/

/-- **One tube piece.**  For `A = D_{K²}^{⊗K}`, `K ≥ 1`, and an injective row selection
`e : Fin g → (Fin K → Fin K²)`, the image of the unit sup-cube under `[A_G, I_g]` has volume at
most `exp(½ r (log 2 + 23√K)) · (√(2πe (H+g)/g))^g`, `r = (K²)^K`, `H = (K²+1)^K`. -/
theorem volume_tubePiece_le {K g : ℕ} (hK : 1 ≤ K) (hg : 0 < g)
    (e : Fin g → (Fin K → Fin (K ^ 2))) (he : Function.Injective e) :
    (volume ((Matrix.toLin' (augmented ((tensorDiff K (K ^ 2)).submatrix e id)))
        '' Metric.closedBall (0 : (Fin K → Fin (K ^ 2 + 1)) ⊕ Fin g → ℝ) 1)).toReal
      ≤ Real.exp (((K : ℝ) ^ 2) ^ K * (Real.log 2 + 23 * Real.sqrt K) / 2)
        * (Real.sqrt (2 * π * Real.exp 1 / g)
            * Real.sqrt (((K : ℝ) ^ 2 + 1) ^ K + g)) ^ g := by
  have h1 := volume_augmented_image_le ((tensorDiff K (K ^ 2)).submatrix e id)
    (by simpa using hg)
  simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_pi, Finset.prod_const,
    Finset.card_univ] at h1
  push_cast at h1
  refine h1.trans ?_
  gcongr
  -- `√det(1 + A_G A_Gᵀ) ≤ √det(1 + A Aᵀ) = exp(½ log det) ≤ exp(½ r(log 2 + 23√K))`
  have hdet := det_one_add_submatrix_mul_transpose_le (tensorDiff K (K ^ 2)) e he
  rw [tensorDiff_mul_transpose] at hdet
  have hpos : 0 < (1 + tensorGram K (K ^ 2)).det := by
    rw [det_one_add_tensorGram]
    exact Finset.prod_pos fun j _ => by linarith [tensorLam_pos (K := K) j]
  have hlog := log_det_one_add_tensorGram_le' hK
  calc Real.sqrt (1 + (tensorDiff K (K ^ 2)).submatrix e id
          * ((tensorDiff K (K ^ 2)).submatrix e id)ᵀ).det
      ≤ Real.sqrt (1 + tensorGram K (K ^ 2)).det := Real.sqrt_le_sqrt hdet
    _ = Real.exp (Real.log (1 + tensorGram K (K ^ 2)).det / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]; ring_nf
    _ ≤ _ := by gcongr

end NormalNumbers.G4
