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

open PrimeLambert

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

/-! ### The base-four cylinder inside an omitted interval, and the cylinder cover -/

/-- Every interval `[a, c) ⊆ [0, 1]` of positive length contains a base-four cylinder
`[w/4^ℓ, (w+1)/4^ℓ)`. -/
lemma exists_cylinder_subset {a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    ∃ ℓ w : ℕ, w < 4 ^ ℓ ∧
      Set.Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ) ⊆ Set.Ico a c := by
  -- choose `ℓ` with `2 / 4^ℓ ≤ c − a`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, 2 / (c - a) ≤ (4 : ℝ) ^ ℓ := by
    obtain ⟨ℓ, hℓ⟩ := pow_unbounded_of_one_lt (2 / (c - a)) (by norm_num : (1 : ℝ) < 4)
    exact ⟨ℓ, hℓ.le⟩
  have hca : 0 < c - a := by linarith
  have h4 : (0 : ℝ) < 4 ^ ℓ := by positivity
  have hgap : 2 / (4 : ℝ) ^ ℓ ≤ c - a := by
    rw [div_le_iff₀ h4]; rw [div_le_iff₀ hca] at hℓ; linarith
  refine ⟨ℓ, ⌈a * 4 ^ ℓ⌉₊, ?_, ?_⟩
  · have h1 : (⌈a * 4 ^ ℓ⌉₊ : ℝ) < a * 4 ^ ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : a * 4 ^ ℓ + 2 ≤ 4 ^ ℓ := by
      have : (c - a) * 4 ^ ℓ ≤ 1 * 4 ^ ℓ := by gcongr; linarith
      rw [div_le_iff₀ h4] at hgap; nlinarith
    exact_mod_cast (show (⌈a * 4 ^ ℓ⌉₊ : ℝ) < 4 ^ ℓ by linarith)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : a * 4 ^ ℓ ≤ ⌈a * 4 ^ ℓ⌉₊ := Nat.le_ceil _
    have h3 : (⌈a * 4 ^ ℓ⌉₊ : ℝ) < a * 4 ^ ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
    constructor
    · rw [div_le_iff₀ h4] at hx1; nlinarith
    · rw [lt_div_iff₀ h4] at hx2
      rw [div_le_iff₀ h4] at hgap
      nlinarith

/-- The cylinder cover of `orbitClosure` in the form `volume_tube_le` consumes: if the orbit
omits `[w/4^ℓ, (w+1)/4^ℓ)`, the closure is covered by at most `(4^ℓ − 1)^M` closed intervals
of length `4^{−ℓM}`. -/
lemma exists_cover_of_omit {ℓ w : ℕ} (hw : w < 4 ^ ℓ)
    (homit : ∀ m, orbit 4 primeLambertFour m ∉
      Set.Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ)) (M : ℕ) :
    ∃ Bs : Finset ℝ, Bs.card ≤ (4 ^ ℓ - 1) ^ M ∧
      orbitClosure ⊆ ⋃ c ∈ Bs, ((↑) : ℝ → UnitAddCircle) ''
        Set.Icc c (c + 1 / ((4 : ℝ) ^ ℓ) ^ M) := by
  refine ⟨(admissible (4 ^ ℓ) M ⟨w, hw⟩).image (cylLeft (4 ^ ℓ) M), ?_, ?_⟩
  · exact Finset.card_image_le.trans (card_admissible _ _ _).le
  · intro x hx
    unfold orbitClosure at hx
    have := orbitClosure_subset_cylinders (bb := 4) (by norm_num) hw
      (by simpa using homit) M hx
    rw [Set.mem_iUnion₂] at this ⊢
    obtain ⟨b, hb, hxb⟩ := this
    refine ⟨cylLeft (4 ^ ℓ) M b, Finset.mem_image_of_mem _ hb, ?_⟩
    unfold cyl at hxb
    push_cast at hxb
    exact hxb

lemma card_goodSets_le (fr : Frame) : fr.goodSets.card ≤ 2 ^ fr.r := by
  unfold Frame.goodSets
  calc _ ≤ ((univ : Finset (Fin fr.r)).powerset).card := Finset.card_filter_le _ _
    _ = 2 ^ fr.r := by rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

/-- **`PropB` on the grid from one real inequality.**  Suppose the orbit omits
`[w/4^ℓ, (w+1)/4^ℓ)`, `4^{−ℓM} ≤ η`, `ε < 1`, `Lg ≥ log det(1 + T_s^{⊗K})`, and for every
`g` with `(1−ε) r ≤ g ≤ r`

    ((4^ℓ−1)^M)^H · η^g · exp(Lg/2) · (√(2πe/g) · √(H+g))^g ≤ δ₁ / 2^r.

Then `PropB δ₁`. -/
theorem gridFrame_propB_of_bound {ℓ w : ℕ} (hw : w < 4 ^ ℓ)
    (homit : ∀ m, orbit 4 primeLambertFour m ∉
      Set.Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ))
    (M : ℕ) (hM : 1 / ((4 : ℝ) ^ ℓ) ^ M ≤ η) (hε1 : ε < 1) (hr : 1 ≤ G.rDim)
    {Lg : ℝ} (hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg)
    {δ₁ : ℝ} (hδ : 0 ≤ δ₁)
    (hbound : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
      (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
        ≤ δ₁ / 2 ^ G.rDim) :
    (gridFrame G X hne sm γ hη hε D).PropB δ₁ := by
  obtain ⟨Bs, hBs, hcov⟩ := exists_cover_of_omit hw homit M
  -- real lifts of θ and γ
  choose θr hθr using fun ν => QuotientAddGroup.mk_surjective ((gridFrame G X hne sm γ hη hε D).θ ν)
  choose γr hγr using fun ν => QuotientAddGroup.mk_surjective ((gridFrame G X hne sm γ hη hε D).γ ν)
  unfold Frame.PropB
  refine ((gridFrame G X hne sm γ hη hε D).volume_tube_le θr γr hθr hγr hM Bs hcov).trans ?_
  have hterm : ∀ Gs ∈ (gridFrame G X hne sm γ hη hε D).goodSets,
      (Bs.card : ℝ) ^ (gridFrame G X hne sm γ hη hε D).H * η ^ Gs.card
        * (volume ((gridFrame G X hne sm γ hη hε D).pieceCube Gs)).toReal ≤ δ₁ / 2 ^ G.rDim := by
    intro Gs hGs
    unfold Frame.goodSets at hGs
    rw [Finset.mem_filter] at hGs
    have hge : (1 - ε) * G.rDim ≤ Gs.card := hGs.2
    have hle : Gs.card ≤ G.rDim := by
      have := Finset.card_le_card (Finset.mem_powerset.1 hGs.1)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have hpos : 0 < Gs.card := by
      have hr' : (1 : ℝ) ≤ G.rDim := by exact_mod_cast hr
      have : (0 : ℝ) < (1 - ε) * G.rDim := mul_pos (by linarith) (by linarith)
      exact_mod_cast (lt_of_lt_of_le this hge)
    have hpc := gridFrame_volume_pieceCube_le G X hne sm γ hη hε D Gs hpos hlog
    refine le_trans ?_ (hbound Gs.card hge hle)
    rw [gridFrame_H]
    have h1 : (Bs.card : ℝ) ^ G.hDim ≤ (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim := by
      have : (Bs.card : ℝ) ≤ (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) := by exact_mod_cast hBs
      exact pow_le_pow_left₀ (by positivity) this _
    calc (Bs.card : ℝ) ^ G.hDim * η ^ Gs.card
          * (volume ((gridFrame G X hne sm γ hη hε D).pieceCube Gs)).toReal
        ≤ (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ Gs.card
          * (Real.exp (Lg / 2) * (Real.sqrt (2 * Real.pi * Real.exp 1 / Gs.card)
              * Real.sqrt (G.hDim + Gs.card)) ^ Gs.card) := by
          gcongr
      _ = _ := by ring
  calc ∑ Gs ∈ (gridFrame G X hne sm γ hη hε D).goodSets,
        (Bs.card : ℝ) ^ (gridFrame G X hne sm γ hη hε D).H * η ^ Gs.card
          * (volume ((gridFrame G X hne sm γ hη hε D).pieceCube Gs)).toReal
      ≤ ∑ _Gs ∈ (gridFrame G X hne sm γ hη hε D).goodSets, δ₁ / 2 ^ G.rDim :=
        Finset.sum_le_sum hterm
    _ = ((gridFrame G X hne sm γ hη hε D).goodSets.card : ℝ) * (δ₁ / 2 ^ G.rDim) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ G.rDim : ℝ) * (δ₁ / 2 ^ G.rDim) := by
        have hc : ((gridFrame G X hne sm γ hη hε D).goodSets.card : ℝ) ≤ 2 ^ G.rDim := by
          exact_mod_cast card_goodSets_le _
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = δ₁ := by field_simp

end NormalNumbers.G4
