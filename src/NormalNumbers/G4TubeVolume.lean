/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Wiring
import NormalNumbers.G4TubePiece
import NormalNumbers.G4TorusProjection
import NormalNumbers.G4Covering
import NormalNumbers.G4FreqSep

/-!
# G4 disjunctivity, §4B assembly: Haar volume of the `εη`-tube around the image

Draft §5 / brief §4B.  For a frame `fr` whose orbit closure is covered by `#Bs` closed
cylinders `[c, c+h]`, `h ≤ η`, the `εη`-tube around `image = A(Cᴴ) + θ − γ` in the **average**
metric `dAv` is covered by the finite union, over coordinate sets `G ⊆ Fin r` with
`|G| ≥ (1−ε) r` and over cylinder choices `b : Fin H → Bs`, of the *pieces*

  `piece G b = {y | y_G ∈ π_G (center_G(b) + η · [A_G, I_G] · [−1,1]^{H+G})}`.

Mechanism (`tube_subset_pieces`): a point `y` of the tube has a nearest image point
`z = A x + θ − γ` (attained by compactness); Markov in `dAv` gives `|{ν : dist(y_ν,z_ν) > η}| ≤ εr`
(`card_filter_dist_gt_le`), so on the complement `G` the coordinate error is `≤ η` and the
cylinder half-widths are `≤ η` — both fit in `η` times the unit sup-cube.  This is exactly where
the brief's "average metric, not the product sup metric" constraint bites: with the sup metric
`G` would be forced to be everything.

Volume (`volume_piece_le`): the restriction `𝕋^r → 𝕋^G` is measure preserving, the torus
projection does not increase volume (`volume_image_torusProj_le`), translation is invariant,
and `addHaar_smul` gives the factor `η^{|G|}`.  Summing (`volume_tube_le`):

  `vol(tube) ≤ ∑_{G, |G| ≥ (1−ε)r} (#Bs)^H · η^{|G|} · vol([A_G, I_G] · cube)`,

with the last factor bounded by `volume_tubePiece_le` once `A` is the tensor matrix (grid
instantiation is a separate module).
-/

open MeasureTheory Finset
open scoped BigOperators Pointwise

namespace NormalNumbers.G4

/-! ### Real lifts and Markov in the average metric -/

/-- Every torus point lifts to a real of absolute value its norm. -/
lemma exists_real_lift (t : UnitAddCircle) : ∃ v : ℝ, (v : UnitAddCircle) = t ∧ |v| = ‖t‖ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
  refine ⟨x - round x, ?_, UnitAddCircle.norm_eq.symm⟩
  rw [AddCircle.coe_sub, coe_int_eq_zero, sub_zero]

/-- **Markov in `dAv`**: if `dAv y z ≤ c η`, at most `c r` coordinates are farther than `η`. -/
lemma card_filter_dist_gt_le {r : ℕ} (y z : Torus r) {η c : ℝ} (hη : 0 < η)
    (hd : dAv y z ≤ c * η) :
    ((univ.filter fun ν => η < dist (y ν) (z ν)).card : ℝ) ≤ c * r := by
  unfold dAv at hd
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_le_iff₀ hr'] at hd
  have hsum : ((univ.filter fun ν => η < dist (y ν) (z ν)).card : ℝ) * η
      ≤ ∑ ν, dist (y ν) (z ν) := by
    calc ((univ.filter fun ν => η < dist (y ν) (z ν)).card : ℝ) * η
        = ∑ _ν ∈ univ.filter fun ν => η < dist (y ν) (z ν), η := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ν ∈ univ.filter fun ν => η < dist (y ν) (z ν), dist (y ν) (z ν) :=
          Finset.sum_le_sum fun ν hν => (Finset.mem_filter.1 hν).2.le
      _ ≤ ∑ ν, dist (y ν) (z ν) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => dist_nonneg
  have : ((univ.filter fun ν => η < dist (y ν) (z ν)).card : ℝ) * η ≤ c * r * η := by
    linarith
  exact le_of_mul_le_mul_right this hη

/-- The good coordinate set has at least `(1 − c) r` elements. -/
lemma le_card_filter_dist_le {r : ℕ} (y z : Torus r) {η c : ℝ} (hη : 0 < η)
    (hd : dAv y z ≤ c * η) :
    (1 - c) * r ≤ ((univ.filter fun ν => dist (y ν) (z ν) ≤ η).card : ℝ) := by
  have h1 := card_filter_dist_gt_le y z hη hd
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin r))) (p := fun ν => dist (y ν) (z ν) ≤ η)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (univ.filter fun ν => ¬ dist (y ν) (z ν) ≤ η)
      = univ.filter fun ν => η < dist (y ν) (z ν) := by
    ext ν; simp [not_le]
  rw [h3] at h2
  have h4 : (((univ.filter fun ν => dist (y ν) (z ν) ≤ η).card : ℕ) : ℝ)
      + ((univ.filter fun ν => η < dist (y ν) (z ν)).card : ℝ) = r := by exact_mod_cast h2
  linarith

/-! ### The image is compact; the nearest image point is attained -/

lemma continuous_dAv_right {r : ℕ} (y : Torus r) : Continuous fun z : Torus r => dAv y z := by
  unfold dAv
  exact (continuous_finsetSum _ fun ν _ => continuous_const.dist (continuous_apply ν)).div_const _

lemma continuous_mulVecT {r H : ℕ} (A : Matrix (Fin r) (Fin H) ℤ) :
    Continuous fun x : Fin H → UnitAddCircle => mulVecT A x := by
  unfold mulVecT
  exact continuous_pi fun ν =>
    continuous_finsetSum _ fun α _ => (continuous_zsmul _).comp (continuous_apply α)

namespace Frame

variable (fr : Frame)

lemma image_eq_image : fr.image
    = (fun x : Fin fr.H → UnitAddCircle => mulVecT fr.A x + fr.θ - fr.γ) ''
        (Set.pi Set.univ fun _ => orbitClosure) := by
  ext y
  simp only [image, Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

lemma image_isCompact : IsCompact fr.image := by
  rw [image_eq_image]
  exact (isClosed_set_pi fun _ _ => isClosed_closure).isCompact.image
    (((continuous_mulVecT fr.A).add continuous_const).sub continuous_const)

/-- The nearest image point exists. -/
lemma exists_dAv_eq_dAvSet (y : Torus fr.r) : ∃ z ∈ fr.image, dAv y z = dAvSet y fr.image := by
  obtain ⟨z, hz, hmin⟩ := fr.image_isCompact.exists_isMinOn fr.image_nonempty
    (continuous_dAv_right y).continuousOn
  refine ⟨z, hz, le_antisymm ?_ (dAvSet_le hz)⟩
  unfold dAvSet
  refine le_csInf (fr.image_nonempty.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  exact hmin hw

/-! ### The pieces -/

/-- The real matrix `A` (entries cast from `ℤ`). -/
noncomputable def AR : Matrix (Fin fr.r) (Fin fr.H) ℝ := fr.A.map (Int.cast : ℤ → ℝ)

/-- The row restriction `A_G`. -/
noncomputable def ARsub (G : Finset (Fin fr.r)) : Matrix {ν // ν ∈ G} (Fin fr.H) ℝ :=
  fr.AR.submatrix (fun ν : {ν // ν ∈ G} => ν.1) id

/-- The image of the unit sup-cube under `[A_G, I_G]`. -/
noncomputable def pieceCube (G : Finset (Fin fr.r)) : Set ({ν // ν ∈ G} → ℝ) :=
  Matrix.toLin' (augmented (fr.ARsub G)) '' Metric.closedBall 0 1

/-- The centre of a piece: `A c + θ − γ` restricted to `G`, with real lifts `θr, γr`. -/
noncomputable def pieceCenter (θr γr : Fin fr.r → ℝ) (G : Finset (Fin fr.r)) (b : Fin fr.H → ℝ) :
    {ν // ν ∈ G} → ℝ :=
  fun ν => ∑ α, fr.AR ν.1 α * b α + θr ν.1 - γr ν.1

/-- The restriction `𝕋^r → 𝕋^G`. -/
def restrictG (G : Finset (Fin fr.r)) (y : Torus fr.r) : {ν // ν ∈ G} → UnitAddCircle :=
  fun ν => y ν.1

/-- One piece of the cover. -/
noncomputable def piece (θr γr : Fin fr.r → ℝ) (G : Finset (Fin fr.r)) (b : Fin fr.H → ℝ) :
    Set (Torus fr.r) :=
  fr.restrictG G ⁻¹'
    (torusProj '' ((fun v => fr.pieceCenter θr γr G b + fr.η • v) '' fr.pieceCube G))

/-- The good coordinate sets. -/
noncomputable def goodSets : Finset (Finset (Fin fr.r)) :=
  (univ : Finset (Fin fr.r)).powerset.filter fun G => (1 - fr.ε) * fr.r ≤ G.card

lemma toLin'_augmented_sum_elim {g H : Type*} [Fintype g] [Fintype H] [DecidableEq g]
    [DecidableEq H] (A : Matrix g H ℝ) (u : H → ℝ) (w : g → ℝ) :
    Matrix.toLin' (augmented A) (Sum.elim u w) = A.mulVec u + w := by
  rw [Matrix.toLin'_apply]; unfold augmented
  ext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromCols, Matrix.one_apply]

lemma coe_zsmul_real (n : ℤ) (x : ℝ) :
    n • (x : UnitAddCircle) = ((n * x : ℝ) : UnitAddCircle) := by
  rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]

/-- **The covering.**  The tube lies in the finite union of the pieces. -/
theorem tube_subset_pieces (θr γr : Fin fr.r → ℝ)
    (hθ : ∀ ν, (θr ν : UnitAddCircle) = fr.θ ν) (hγ : ∀ ν, (γr ν : UnitAddCircle) = fr.γ ν)
    {h : ℝ} (hhη : h ≤ fr.η) (Bs : Finset ℝ)
    (hcov : orbitClosure ⊆ ⋃ c ∈ Bs, ((↑) : ℝ → UnitAddCircle) '' Set.Icc c (c + h)) :
    tube fr.image fr.res ⊆
      ⋃ G ∈ fr.goodSets, ⋃ b ∈ Fintype.piFinset (fun _ : Fin fr.H => Bs),
        fr.piece θr γr G b := by
  intro y hy
  have hη := fr.hη
  obtain ⟨z, hz, hzd⟩ := fr.exists_dAv_eq_dAvSet y
  have hdist : dAv y z ≤ fr.ε * fr.η := by rw [hzd]; exact hy
  obtain ⟨x, hxC, rfl⟩ := hz
  -- cylinder representatives of the atoms
  have hcyl : ∀ α, ∃ c ∈ Bs, ∃ u : ℝ, 0 ≤ u ∧ u ≤ h ∧ x α = ((c + u : ℝ) : UnitAddCircle) := by
    intro α
    have := hcov (hxC α)
    rw [Set.mem_iUnion₂] at this
    obtain ⟨c, hc, w, hw, hwx⟩ := this
    exact ⟨c, hc, w - c, by linarith [hw.1], by linarith [hw.2], by rw [← hwx]; congr 1; ring⟩
  choose c hcB u hu0 huh hxu using hcyl
  -- real lifts of the coordinate errors
  have hlift : ∀ ν, ∃ v : ℝ, (v : UnitAddCircle) = y ν - (mulVecT fr.A x + fr.θ - fr.γ) ν ∧
      |v| = dist (y ν) ((mulVecT fr.A x + fr.θ - fr.γ) ν) := by
    intro ν
    obtain ⟨v, hv1, hv2⟩ := exists_real_lift (y ν - (mulVecT fr.A x + fr.θ - fr.γ) ν)
    exact ⟨v, hv1, by rw [hv2, dist_eq_norm]⟩
  choose v hv hvabs using hlift
  set G : Finset (Fin fr.r) :=
    univ.filter fun ν => dist (y ν) ((mulVecT fr.A x + fr.θ - fr.γ) ν) ≤ fr.η with hG
  have hGgood : G ∈ fr.goodSets := by
    unfold goodSets
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
      le_card_filter_dist_le y _ hη hdist⟩
  refine Set.mem_iUnion₂.2 ⟨G, hGgood, Set.mem_iUnion₂.2 ⟨c, ?_, ?_⟩⟩
  · rw [Fintype.mem_piFinset]; exact hcB
  -- the point of the cube
  let w : Fin fr.H ⊕ {ν // ν ∈ G} → ℝ := Sum.elim (fun α => u α / fr.η) (fun ν => v ν.1 / fr.η)
  have hw : w ∈ Metric.closedBall (0 : Fin fr.H ⊕ {ν // ν ∈ G} → ℝ) 1 := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro (α | ν)
    · simp only [w, Sum.elim_inl, Real.norm_eq_abs]
      rw [abs_div, abs_of_pos hη, abs_of_nonneg (hu0 α), div_le_one hη]
      exact (huh α).trans hhη
    · simp only [w, Sum.elim_inr, Real.norm_eq_abs]
      rw [abs_div, abs_of_pos hη, div_le_one hη, hvabs]
      exact (Finset.mem_filter.1 ν.2).2
  refine ⟨_, ⟨Matrix.toLin' (augmented (fr.ARsub G)) w, ⟨w, hw, rfl⟩, rfl⟩, ?_⟩
  funext ν
  simp only [torusProj, restrictG, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [toLin'_augmented_sum_elim]
  simp only [Pi.add_apply]
  -- unfold the target coordinate
  have hzν : (mulVecT fr.A x + fr.θ - fr.γ) ν.1
      = ((∑ α, fr.AR ν.1 α * (c α + u α) + θr ν.1 - γr ν.1 : ℝ) : UnitAddCircle) := by
    simp only [Pi.add_apply, Pi.sub_apply, mulVecT]
    rw [AddCircle.coe_sub, AddCircle.coe_add, hθ, hγ, QuotientAddGroup.mk_sum]
    congr 1; congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hxu, coe_zsmul_real]
    simp [AR]
  have hy : y ν.1 = (mulVecT fr.A x + fr.θ - fr.γ) ν.1 + (v ν.1 : UnitAddCircle) := by
    rw [hv]; abel
  rw [hy, hzν, ← AddCircle.coe_add]
  congr 1
  simp only [pieceCenter, ARsub, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
  rw [mul_add, Finset.mul_sum]
  have hηne : fr.η ≠ 0 := hη.ne'
  have : ∑ α, fr.AR ν.1 α * (c α + u α) = ∑ α, fr.AR ν.1 α * c α + ∑ α, fr.AR ν.1 α * u α := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun α _ => by ring
  rw [this]
  have h2 : ∑ α, fr.η * (fr.AR ν.1 α * (u α / fr.η)) = ∑ α, fr.AR ν.1 α * u α :=
    Finset.sum_congr rfl fun α _ => by field_simp
  rw [h2]
  field_simp
  ring

/-! ### Volume of one piece -/

lemma restrictG_eq (G : Finset (Fin fr.r)) :
    fr.restrictG G = Prod.fst ∘ (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin fr.r => UnitAddCircle) fun ν => ν ∈ G) := rfl

lemma measurePreserving_restrictG (G : Finset (Fin fr.r)) :
    MeasurePreserving (fr.restrictG G) volume volume := by
  rw [restrictG_eq]
  have h1 := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin fr.r => (volume : Measure UnitAddCircle)) fun ν => ν ∈ G
  have := (measurePreserving_fst (μ := _) (ν := _)).comp h1
  refine ⟨this.measurable, ?_⟩
  rw [volume_pi, volume_pi]
  refine this.map_eq.trans ?_
  congr
  exact Subsingleton.elim _ _

lemma pieceCube_isCompact (G : Finset (Fin fr.r)) : IsCompact (fr.pieceCube G) :=
  (isCompact_closedBall _ _).image (LinearMap.continuous_of_finiteDimensional _)

lemma volume_pieceCube_ne_top (G : Finset (Fin fr.r)) : volume (fr.pieceCube G) ≠ ⊤ :=
  (fr.pieceCube_isCompact G).measure_lt_top.ne

/-- **One piece**: `vol(piece) ≤ η^{|G|} · vol([A_G, I_G] · cube)`. -/
theorem volume_piece_le (θr γr : Fin fr.r → ℝ) (G : Finset (Fin fr.r)) (b : Fin fr.H → ℝ) :
    volume (fr.piece θr γr G b) ≤ ENNReal.ofReal (fr.η ^ G.card) * volume (fr.pieceCube G) := by
  have hη := fr.hη
  set T : Set ({ν // ν ∈ G} → ℝ) :=
    (fun v => fr.pieceCenter θr γr G b + fr.η • v) '' fr.pieceCube G with hT
  have hTc : IsCompact T :=
    (fr.pieceCube_isCompact G).image (by fun_prop)
  have hπ : IsCompact (torusProj '' T) := hTc.image continuous_torusProj
  calc volume (fr.piece θr γr G b)
      = volume (torusProj '' T) :=
        (fr.measurePreserving_restrictG G).measure_preimage hπ.isClosed.measurableSet.nullMeasurableSet
    _ ≤ volume T := volume_image_torusProj_le hTc.isClosed.measurableSet hπ.isClosed.measurableSet
    _ = ENNReal.ofReal (fr.η ^ G.card) * volume (fr.pieceCube G) := by
        rw [hT, show (fun v : {ν // ν ∈ G} → ℝ => fr.pieceCenter θr γr G b + fr.η • v)
            = (fun v => fr.pieceCenter θr γr G b + v) ∘ (fun v => fr.η • v) from rfl,
          Set.image_comp, Set.image_smul, Set.image_add_left, measure_preimage_add,
          Measure.addHaar_smul, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, abs_pow,
          abs_of_pos hη]

/-! ### The tube volume -/

/-- **The §4B assembly.**  If the orbit closure is covered by `#Bs` closed cylinders `[c, c+h]`
with `h ≤ η`, then

  `vol(tube) ≤ ∑_{G ⊆ Fin r, |G| ≥ (1−ε) r} (#Bs)^H · η^{|G|} · vol([A_G, I_G] · [−1,1]^{H+G})`. -/
theorem volume_tube_le (θr γr : Fin fr.r → ℝ)
    (hθ : ∀ ν, (θr ν : UnitAddCircle) = fr.θ ν) (hγ : ∀ ν, (γr ν : UnitAddCircle) = fr.γ ν)
    {h : ℝ} (hhη : h ≤ fr.η) (Bs : Finset ℝ)
    (hcov : orbitClosure ⊆ ⋃ c ∈ Bs, ((↑) : ℝ → UnitAddCircle) '' Set.Icc c (c + h)) :
    (volume (tube fr.image fr.res)).toReal ≤
      ∑ G ∈ fr.goodSets, (Bs.card : ℝ) ^ fr.H * fr.η ^ G.card * (volume (fr.pieceCube G)).toReal := by
  have hη := fr.hη
  have hcard : (Fintype.piFinset fun _ : Fin fr.H => Bs).card = Bs.card ^ fr.H := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hE : volume (tube fr.image fr.res) ≤
      ∑ G ∈ fr.goodSets, ENNReal.ofReal ((Bs.card : ℝ) ^ fr.H * fr.η ^ G.card)
        * volume (fr.pieceCube G) := by
    calc volume (tube fr.image fr.res)
        ≤ volume (⋃ G ∈ fr.goodSets, ⋃ b ∈ Fintype.piFinset (fun _ : Fin fr.H => Bs),
            fr.piece θr γr G b) := measure_mono (fr.tube_subset_pieces θr γr hθ hγ hhη Bs hcov)
      _ ≤ ∑ G ∈ fr.goodSets, volume (⋃ b ∈ Fintype.piFinset (fun _ : Fin fr.H => Bs),
            fr.piece θr γr G b) := measure_biUnion_finset_le _ _
      _ ≤ ∑ G ∈ fr.goodSets, ∑ b ∈ Fintype.piFinset (fun _ : Fin fr.H => Bs),
            volume (fr.piece θr γr G b) :=
          Finset.sum_le_sum fun G _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ G ∈ fr.goodSets, ∑ _b ∈ Fintype.piFinset (fun _ : Fin fr.H => Bs),
            ENNReal.ofReal (fr.η ^ G.card) * volume (fr.pieceCube G) :=
          Finset.sum_le_sum fun G _ => Finset.sum_le_sum fun b _ => fr.volume_piece_le θr γr G b
      _ = _ := by
          refine Finset.sum_congr rfl fun G _ => ?_
          rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul (by positivity),
            ← Nat.cast_pow, ENNReal.ofReal_natCast]
  have hne : ∀ G ∈ fr.goodSets, ENNReal.ofReal ((Bs.card : ℝ) ^ fr.H * fr.η ^ G.card)
      * volume (fr.pieceCube G) ≠ ⊤ :=
    fun G _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fr.volume_pieceCube_ne_top G)
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne) hE).trans (le_of_eq ?_)
  rw [ENNReal.toReal_sum hne]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end Frame

end NormalNumbers.G4
