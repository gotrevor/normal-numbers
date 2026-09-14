/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4TubeVolume
import NormalNumbers.G4EntropyFrame

/-!
# Entropy expedition §3B: the **joint**-box cover bound (G)

`G4TubeVolume.Frame.volume_tube_le` covers the tube around the image of the *whole* orbit
closure.  Its cylinder choices range independently over each of the `H` atoms, so it pays a
factor `(#Bs)^H` — the number of points of a **product** set.  An entropy argument cannot
afford that: the whole point is that the sampled joint vector lives in a collection `ℬ` of
joint boxes far smaller than the product of its coordinate projections, and replacing `ℬ` by
that product erases the entropy saving.

So the covering is redone here over an arbitrary finite collection `𝓑` of **joint** box
centres `b : Fin H → ℝ`:

* `boxUnion 𝓑 h`  — the union over `b ∈ 𝓑` of the closed joint boxes `∏_α [b α, b α + h]`
  (closed, hence endpoint-safe, and compact);
* `imageOfSet X`  — `{A x + θ − γ : x ∈ X}`, so `E_K(ℬ) = imageOfSet (boxUnion 𝓑 h)`;
* **`tube_subset_pieces_joint`** — the tube around it is covered by
  `⋃_{G good} ⋃_{b ∈ 𝓑} piece θr γr G b`: the *same* pieces as before, but indexed by `𝓑`
  itself rather than by `Bs^H`;
* **`volume_tube_le_joint` — (G)** —
  `vol(tube (E 𝓑) res) ≤ ∑_{G, |G| ≥ (1−ε)r} |𝓑| · η^{|G|} · vol([A_G, I_G]·cube)`.

The mechanism is unchanged (Markov in the average metric picks the good coordinate set `G`;
the determinant/ellipsoid bound handles `vol(pieceCube G)`), and `volume_tube_le_of_joint`
recovers the old `(#Bs)^H` statement as the instance `𝓑 = Bs^H`, so nothing is lost.

**What this buys.**  Combined with `Frame.capture_le`, a collection `ℬ` of `N` joint boxes now
costs `N` rather than `(#Bs)^H` — the cover factor is *linear in the number of joint boxes*.
That is precisely the shape the information-set lemma feeds: `N ≤ 2^{(1−δ/2) m H}` against a
mass `≥ δ/(2−δ)`.
-/

open MeasureTheory Finset
open scoped BigOperators Pointwise

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

/-- Tubes are monotone in the set. -/
lemma tube_mono {r : ℕ} {E E' : Set (Torus r)} (hne : E.Nonempty) (hsub : E ⊆ E') (ρ : ℝ) :
    tube E ρ ⊆ tube E' ρ := by
  intro y hy
  have : dAvSet y E' ≤ dAvSet y E :=
    csInf_le_csInf (dAvSet_bddBelow y E') (hne.image _) (Set.image_mono hsub)
  exact le_trans this hy

/-- The nearest point of a nonempty compact set is attained (the `Frame.image`-specific
`exists_dAv_eq_dAvSet` for an arbitrary compact set). -/
lemma exists_dAv_eq_dAvSet_of_isCompact {r : ℕ} {E : Set (Torus r)} (hc : IsCompact E)
    (hne : E.Nonempty) (y : Torus r) : ∃ z ∈ E, dAv y z = dAvSet y E := by
  obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn hne (continuous_dAv_right y).continuousOn
  refine ⟨z, hz, le_antisymm ?_ (dAvSet_le hz)⟩
  unfold dAvSet
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  exact hmin hw

variable (fr : NormalNumbers.G4.Frame)

/-- The closed joint box of centre `b` and side `h`, in `(ℝ/ℤ)^H`. -/
def jointBox (b : Fin fr.H → ℝ) (h : ℝ) : Set (Fin fr.H → UnitAddCircle) :=
  Set.pi Set.univ fun α => ((↑) : ℝ → UnitAddCircle) '' Set.Icc (b α) (b α + h)

/-- The union of the joint boxes of a finite collection of centres. -/
def boxUnion (𝓑 : Finset (Fin fr.H → ℝ)) (h : ℝ) : Set (Fin fr.H → UnitAddCircle) :=
  ⋃ b ∈ 𝓑, jointBox fr b h

/-- `E = A·X + θ − γ` for an arbitrary set `X` of atom vectors. -/
def imageOfSet (X : Set (Fin fr.H → UnitAddCircle)) : Set (Torus fr.r) :=
  (fun x => mulVecT fr.A x + fr.θ - fr.γ) '' X

lemma jointBox_isCompact (b : Fin fr.H → ℝ) (h : ℝ) : IsCompact (jointBox fr b h) :=
  isCompact_univ_pi fun α => isCompact_Icc.image continuous_quotient_mk'

lemma boxUnion_isCompact (𝓑 : Finset (Fin fr.H → ℝ)) (h : ℝ) :
    IsCompact (boxUnion fr 𝓑 h) := by
  refine 𝓑.isCompact_biUnion fun b _ => jointBox_isCompact fr b h

lemma imageOfSet_isCompact {X : Set (Fin fr.H → UnitAddCircle)} (hX : IsCompact X) :
    IsCompact (imageOfSet fr X) :=
  hX.image (((continuous_mulVecT fr.A).add continuous_const).sub continuous_const)

lemma imageOfSet_nonempty {X : Set (Fin fr.H → UnitAddCircle)} (hX : X.Nonempty) :
    (imageOfSet fr X).Nonempty := hX.image _

lemma mem_imageOfSet {X : Set (Fin fr.H → UnitAddCircle)} {x : Fin fr.H → UnitAddCircle}
    (hx : x ∈ X) : mulVecT fr.A x + fr.θ - fr.γ ∈ imageOfSet fr X :=
  ⟨x, hx, rfl⟩

/-- **The joint covering.**  The tube around `A·(⋃_{b ∈ 𝓑} box b) + θ − γ` is covered by the
pieces indexed by `𝓑` itself — one piece per *joint* box, not one per product choice. -/
theorem tube_subset_pieces_joint (θr γr : Fin fr.r → ℝ)
    (hθ : ∀ ν, (θr ν : UnitAddCircle) = fr.θ ν) (hγ : ∀ ν, (γr ν : UnitAddCircle) = fr.γ ν)
    {h : ℝ} (hh0 : 0 ≤ h) (hhη : h ≤ fr.η) (𝓑 : Finset (Fin fr.H → ℝ)) (h𝓑 : 𝓑.Nonempty) :
    tube (imageOfSet fr (boxUnion fr 𝓑 h)) fr.res ⊆
      ⋃ G ∈ fr.goodSets, ⋃ b ∈ 𝓑, fr.piece θr γr G b := by
  intro y hy
  have hη := fr.hη
  have hcpt := imageOfSet_isCompact fr (boxUnion_isCompact fr 𝓑 h)
  have hne : (imageOfSet fr (boxUnion fr 𝓑 h)).Nonempty := by
    obtain ⟨b, hb⟩ := h𝓑
    refine imageOfSet_nonempty fr ⟨fun α => ((b α : ℝ) : UnitAddCircle), ?_⟩
    refine Set.mem_biUnion hb ?_
    intro α _
    exact ⟨b α, ⟨le_rfl, by linarith⟩, rfl⟩
  obtain ⟨z, hz, hzd⟩ := exists_dAv_eq_dAvSet_of_isCompact hcpt hne y
  have hdist : dAv y z ≤ fr.ε * fr.η := by rw [hzd]; exact hy
  obtain ⟨x, hxU, rfl⟩ := hz
  -- one joint box contains the whole atom vector
  rw [boxUnion, Set.mem_iUnion₂] at hxU
  obtain ⟨c, hcB, hxbox⟩ := hxU
  have hcyl : ∀ α, ∃ u : ℝ, 0 ≤ u ∧ u ≤ h ∧ x α = ((c α + u : ℝ) : UnitAddCircle) := by
    intro α
    obtain ⟨w, hw, hwx⟩ := hxbox α (Set.mem_univ α)
    exact ⟨w - c α, by linarith [hw.1], by linarith [hw.2], by rw [← hwx]; congr 1; ring⟩
  choose u hu0 huh hxu using hcyl
  have hlift : ∀ ν, ∃ v : ℝ, (v : UnitAddCircle) = y ν - (mulVecT fr.A x + fr.θ - fr.γ) ν ∧
      |v| = dist (y ν) ((mulVecT fr.A x + fr.θ - fr.γ) ν) := by
    intro ν
    obtain ⟨v, hv1, hv2⟩ := exists_real_lift (y ν - (mulVecT fr.A x + fr.θ - fr.γ) ν)
    exact ⟨v, hv1, by rw [hv2, dist_eq_norm]⟩
  choose v hv hvabs using hlift
  set G : Finset (Fin fr.r) :=
    univ.filter fun ν => dist (y ν) ((mulVecT fr.A x + fr.θ - fr.γ) ν) ≤ fr.η with hG
  have hGgood : G ∈ fr.goodSets := by
    unfold NormalNumbers.G4.Frame.goodSets
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
      le_card_filter_dist_le y _ hη hdist⟩
  refine Set.mem_iUnion₂.2 ⟨G, hGgood, Set.mem_iUnion₂.2 ⟨c, hcB, ?_⟩⟩
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
  simp only [torusProj, NormalNumbers.G4.Frame.restrictG, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [NormalNumbers.G4.Frame.toLin'_augmented_sum_elim]
  simp only [Pi.add_apply]
  have hzν : (mulVecT fr.A x + fr.θ - fr.γ) ν.1
      = ((∑ α, fr.AR ν.1 α * (c α + u α) + θr ν.1 - γr ν.1 : ℝ) : UnitAddCircle) := by
    simp only [Pi.add_apply, Pi.sub_apply, mulVecT]
    rw [AddCircle.coe_sub, AddCircle.coe_add, hθ, hγ, QuotientAddGroup.mk_sum]
    congr 1; congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hxu, NormalNumbers.G4.Frame.coe_zsmul_real]
    simp [NormalNumbers.G4.Frame.AR]
  have hy2 : y ν.1 = (mulVecT fr.A x + fr.θ - fr.γ) ν.1 + (v ν.1 : UnitAddCircle) := by
    rw [hv]; abel
  rw [hy2, hzν, ← AddCircle.coe_add]
  congr 1
  simp only [NormalNumbers.G4.Frame.pieceCenter, NormalNumbers.G4.Frame.ARsub, Matrix.mulVec,
    dotProduct, Matrix.submatrix_apply, id]
  rw [mul_add, Finset.mul_sum]
  have hηne : fr.η ≠ 0 := hη.ne'
  have hsplit : ∑ α, fr.AR ν.1 α * (c α + u α)
      = ∑ α, fr.AR ν.1 α * c α + ∑ α, fr.AR ν.1 α * u α := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun α _ => by ring
  rw [hsplit]
  have h2 : ∑ α, fr.η * (fr.AR ν.1 α * (u α / fr.η)) = ∑ α, fr.AR ν.1 α * u α :=
    Finset.sum_congr rfl fun α _ => by field_simp
  rw [h2]
  field_simp
  ring

/-- **(G): the joint-box cover bound.**  The cover factor is `|𝓑|`, the number of *joint*
boxes — linear, not the `(#Bs)^H` of a product cover. -/
theorem volume_tube_le_joint (θr γr : Fin fr.r → ℝ)
    (hθ : ∀ ν, (θr ν : UnitAddCircle) = fr.θ ν) (hγ : ∀ ν, (γr ν : UnitAddCircle) = fr.γ ν)
    {h : ℝ} (hh0 : 0 ≤ h) (hhη : h ≤ fr.η) (𝓑 : Finset (Fin fr.H → ℝ)) (h𝓑 : 𝓑.Nonempty) :
    (volume (tube (imageOfSet fr (boxUnion fr 𝓑 h)) fr.res)).toReal ≤
      ∑ G ∈ fr.goodSets, (𝓑.card : ℝ) * fr.η ^ G.card
        * (volume (fr.pieceCube G)).toReal := by
  have hη := fr.hη
  have hE : volume (tube (imageOfSet fr (boxUnion fr 𝓑 h)) fr.res) ≤
      ∑ G ∈ fr.goodSets, ENNReal.ofReal ((𝓑.card : ℝ) * fr.η ^ G.card)
        * volume (fr.pieceCube G) := by
    calc volume (tube (imageOfSet fr (boxUnion fr 𝓑 h)) fr.res)
        ≤ volume (⋃ G ∈ fr.goodSets, ⋃ b ∈ 𝓑, fr.piece θr γr G b) :=
          measure_mono (tube_subset_pieces_joint fr θr γr hθ hγ hh0 hhη 𝓑 h𝓑)
      _ ≤ ∑ G ∈ fr.goodSets, volume (⋃ b ∈ 𝓑, fr.piece θr γr G b) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ G ∈ fr.goodSets, ∑ b ∈ 𝓑, volume (fr.piece θr γr G b) :=
          Finset.sum_le_sum fun G _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ G ∈ fr.goodSets, ∑ _b ∈ 𝓑,
            ENNReal.ofReal (fr.η ^ G.card) * volume (fr.pieceCube G) :=
          Finset.sum_le_sum fun G _ => Finset.sum_le_sum fun b _ => fr.volume_piece_le θr γr G b
      _ = _ := by
          refine Finset.sum_congr rfl fun G _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
  have hne : ∀ G ∈ fr.goodSets, ENNReal.ofReal ((𝓑.card : ℝ) * fr.η ^ G.card)
      * volume (fr.pieceCube G) ≠ ⊤ :=
    fun G _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fr.volume_pieceCube_ne_top G)
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne) hE).trans (le_of_eq ?_)
  rw [ENNReal.toReal_sum hne]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- The product cover is the special case `𝓑 = Bs^H`, so the old
`G4TubeVolume.Frame.volume_tube_le` statement is recovered as an instance — nothing the
product cover proved is lost by moving to joint boxes. -/
theorem volume_tube_le_of_joint (θr γr : Fin fr.r → ℝ)
    (hθ : ∀ ν, (θr ν : UnitAddCircle) = fr.θ ν) (hγ : ∀ ν, (γr ν : UnitAddCircle) = fr.γ ν)
    {h : ℝ} (hh0 : 0 ≤ h) (hhη : h ≤ fr.η) (Bs : Finset ℝ)
    (hcov : orbitClosureOf fr.bse fr.x ⊆
      ⋃ c ∈ Bs, ((↑) : ℝ → UnitAddCircle) '' Set.Icc c (c + h)) :
    (volume (tube fr.image fr.res)).toReal ≤
      ∑ G ∈ fr.goodSets, (Bs.card : ℝ) ^ fr.H * fr.η ^ G.card
        * (volume (fr.pieceCube G)).toReal := by
  classical
  set 𝓑 : Finset (Fin fr.H → ℝ) := Fintype.piFinset fun _ : Fin fr.H => Bs with h𝓑def
  -- `Bs` is nonempty because the orbit closure is
  obtain ⟨p, hp⟩ := orbitClosureOf_nonempty fr.bse fr.x
  obtain ⟨c₀, hc₀, -⟩ := Set.mem_iUnion₂.1 (hcov hp)
  have hBs : Bs.Nonempty := ⟨c₀, hc₀⟩
  have h𝓑 : 𝓑.Nonempty := by
    refine ⟨fun _ => c₀, ?_⟩
    rw [h𝓑def, Fintype.mem_piFinset]
    exact fun _ => hc₀
  -- the image of the orbit closure sits inside the image of the joint-box union
  have hsub : fr.image ⊆ imageOfSet fr (boxUnion fr 𝓑 h) := by
    rintro y ⟨x, hxC, rfl⟩
    have hchoice : ∀ α, ∃ c ∈ Bs, x α ∈ ((↑) : ℝ → UnitAddCircle) '' Set.Icc c (c + h) := by
      intro α
      obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.1 (hcov (hxC α))
      exact ⟨c, hc, hx⟩
    choose c hcB hcx using hchoice
    refine mem_imageOfSet fr ?_
    have hcmem : c ∈ 𝓑 := by rw [h𝓑def, Fintype.mem_piFinset]; exact hcB
    exact Set.mem_biUnion hcmem (fun α _ => hcx α)
  have hmono := tube_mono fr.image_nonempty hsub fr.res
  have hcard : (𝓑.card : ℝ) = (Bs.card : ℝ) ^ fr.H := by
    rw [h𝓑def, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  have hbound := volume_tube_le_joint fr θr γr hθ hγ hh0 hhη 𝓑 h𝓑
  rw [hcard] at hbound
  refine le_trans ?_ hbound
  refine ENNReal.toReal_mono ?_ (measure_mono hmono)
  exact (measure_lt_top _ _).ne

end NormalNumbers.G4Entropy
