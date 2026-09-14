/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4TubeVolume
import NormalNumbers.G4Frame

/-!
# G4 disjunctivity, §4B on the concrete frame: the piece cubes of the grid

`gridFrame` has `A = D_s^{⊗K}` reindexed (`Amat`); over `ℝ` this is `tensorDiff K s` reindexed
by `rowEquiv`/`atomEquiv` (`gridFrame_AR`).  For every row set `G`, the piece cube
`[A_G, I_G]·[−1,1]^{H+G}` is bounded by the ellipsoid estimate with
`det(1 + A_G A_Gᵀ) ≤ det(1 + M Mᵀ)` for any reindexing `M` of `A`
(`Frame.volume_pieceCube_le_of_reindex`), hence on the grid by `det(1 + T_s^{⊗K})`
(`gridFrame_volume_pieceCube_le`), the log of which is the spectral input
`log_det_one_add_tensorGram_le'` at `s = K²`.
-/

open MeasureTheory Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

namespace Frame

/-- **Piece-cube bound through a reindexing.**  If `A = M.submatrix e₁ e₂` for bijections
`e₁, e₂`, then `vol([A_G, I_G]·cube) ≤ √det(1 + M Mᵀ) · (√(2πe/|G|) · √(H + |G|))^{|G|}`. -/
theorem volume_pieceCube_le_of_reindex (fr : Frame) {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℝ) (e₁ : Fin fr.r ≃ m) (e₂ : Fin fr.H ≃ n)
    (hAR : fr.AR = M.submatrix e₁ e₂) (G : Finset (Fin fr.r)) (hG : 0 < G.card) :
    (volume (fr.pieceCube G)).toReal
      ≤ Real.sqrt (1 + M * Mᵀ).det
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / G.card)
            * Real.sqrt (fr.H + G.card)) ^ G.card := by
  have hcard : Fintype.card {ν // ν ∈ G} = G.card := Fintype.card_coe G
  have h1 := volume_augmented_image_le (fr.ARsub G) (by rw [hcard]; exact hG)
  unfold pieceCube
  rw [Fintype.card_sum, Fintype.card_fin, hcard] at h1
  refine h1.trans ?_
  push_cast
  gcongr
  -- the Gram matrix of `A_G` is a principal submatrix of `M Mᵀ`
  set f : {ν // ν ∈ G} → m := fun ν => e₁ ν.1 with hf
  have hfinj : Function.Injective f := fun a b h => Subtype.ext (e₁.injective h)
  have hsub : fr.ARsub G = M.submatrix f e₂ := by
    unfold ARsub; rw [hAR, Matrix.submatrix_submatrix]; rfl
  have hgram : fr.ARsub G * (fr.ARsub G)ᵀ = (M * Mᵀ).submatrix f f := by
    rw [hsub, Matrix.transpose_submatrix, Matrix.submatrix_mul M Mᵀ f e₂ f e₂.bijective]
  have hgram' : M.submatrix f id * (M.submatrix f id)ᵀ = (M * Mᵀ).submatrix f f := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul M Mᵀ f id f Function.bijective_id]
  have hdet := det_one_add_submatrix_mul_transpose_le M f hfinj
  rw [hgram'] at hdet
  rw [hgram]
  exact hdet

end Frame

open GridParams

variable (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ)
  (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ)

/-- The real matrix of the concrete frame is the reindexed `tensorDiff`. -/
lemma gridFrame_AR :
    (gridFrame G X hne sm γ hη hε D).AR
      = (tensorDiff G.K G.s).submatrix G.rowEquiv.symm G.atomEquiv.symm := by
  ext ν α
  rw [Frame.AR, Matrix.map_apply]
  show ((G.Amat ν α : ℤ) : ℝ) = tensorDiff G.K G.s (G.rowEquiv.symm ν) (G.atomEquiv.symm α)
  simp only [Amat, kronPow, tensorDiff]
  push_cast
  exact Finset.prod_congr rfl fun i _ => diffZ_cast _ _ _

/-- **Piece-cube bound on the grid.**  With `Lg ≥ log det(1 + T_s^{⊗K})`,
`vol([A_G, I_G]·cube) ≤ exp(Lg/2) · (√(2πe/|G|) · √(H + |G|))^{|G|}`. -/
theorem gridFrame_volume_pieceCube_le (Gs : Finset (Fin (gridFrame G X hne sm γ hη hε D).r))
    (hG : 0 < Gs.card) {Lg : ℝ} (hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg) :
    (volume ((gridFrame G X hne sm γ hη hε D).pieceCube Gs)).toReal
      ≤ Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / Gs.card)
            * Real.sqrt (G.hDim + Gs.card)) ^ Gs.card := by
  have h1 := (gridFrame G X hne sm γ hη hε D).volume_pieceCube_le_of_reindex (tensorDiff G.K G.s)
    G.rowEquiv.symm G.atomEquiv.symm (gridFrame_AR G X hne sm γ hη hε D) Gs hG
  rw [tensorDiff_mul_transpose, gridFrame_H] at h1
  refine h1.trans ?_
  gcongr
  have hpos : 0 < (1 + tensorGram G.K G.s).det := by
    rw [det_one_add_tensorGram]
    exact Finset.prod_pos fun j _ => by linarith [tensorLam_pos (K := G.K) (s := G.s) j]
  calc Real.sqrt (1 + tensorGram G.K G.s).det
      = Real.exp (Real.log (1 + tensorGram G.K G.s).det / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]; ring_nf
    _ ≤ _ := by gcongr

end NormalNumbers.G4
