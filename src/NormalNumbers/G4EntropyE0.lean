/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyTransport

/-!
# Entropy expedition §4: assembling **E0** from (C), (G), §3A and the information-set lemma

The three structural pieces now compose into one theorem.  Suppose, for contradiction, that the
joint quantized sample of `G₄` at scale `K` has entropy deficit

  `H₂(Z^{G4}_K) ≤ (1 − δ) M`,   `M = m_K H_K`,   `0 < δ < 1`.

Then (`FinLaw.prob_infoSet_ge`, `card_infoSet_le`) there is a collection `ℬ` of at most
`2^{(1−δ/2)M}` joint values carrying sample density at least `δ/(2−δ)`.  Its centres `𝓑` select
a set of joint boxes; by §3A (`gridFrame_Ffull_mem_boxUnion`) every sample point of the
corresponding sub-sample `Good` transports into `E = imageOfSet (boxUnion 𝓑 2^{-m})`; by (C)
(`Frame.capture_le`) its density is at most `vol(tube E res) + δ₂ + 2κ + Λδ₃`; and by (G)
(`volume_tube_le_joint`) that volume is at most `|𝓑| ∑_G η^{|G|} vol(pieceCube G)`.

Hence **`entropy_gt_of_budget`**: whenever the schedule satisfies the single numeric inequality

  `2^{(1−δ/2)M} · (∑_{G good} η^{|G|} vol(pieceCube G)) + δ₂ + 2κ + Λδ₃ < δ/(2−δ)`,

the entropy deficit is impossible: `(1 − δ) M < H₂(Z^{G4}_K)`.

That is E0 reduced to a *schedule inequality* — no remaining structural obligation.  Its two
sides are exactly the objects the existing §5 modules estimate: the left is the tube/determinant
budget (`G4GridTube`, `G4Ellipsoid`, `G4Tensor`, `G4ScheduleBudget`) with the entropy factor
`2^{(1−δ/2)m_K H_K}` in place of the old `(#Bs)^{H}`, together with `PropD` (`G4Remainder`,
`G4FarTail`), `PropC` (`G4SmallPrimeVector`) and the Jackson degree.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4
open NormalNumbers.PrimeLambert

/-- The centre map on joint quantized values. -/
noncomputable def centreOf (G : NormalNumbers.G4.GridParams) (m : ℕ)
    (v : G.Atom → Fin (2 ^ m)) : Fin G.hDim → ℝ :=
  fun α => ((v (G.atomEquiv.symm α) : ℕ) : ℝ) / 2 ^ m

lemma centreOf_ZVec (G : NormalNumbers.G4.GridParams) (m : ℕ) (x : ℝ) (n : ℕ) :
    centreOf G m (ZVec G m x n) = sampleCentre G m x n := rfl

/-- **E0, as a schedule inequality.**  Under the stated budget the joint sample entropy cannot
fall short of `M` by the factor `1 − δ`. -/
theorem entropy_gt_of_budget
    (G : NormalNumbers.G4.GridParams) (X : ℕ) (hX : G.b₀ < X) (hbb : (2 : ℕ) ≤ 4)
    (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (Dg m : ℕ)
    (θr γr : Fin G.rDim → ℝ)
    (hθ : ∀ ν, (θr ν : UnitAddCircle)
      = (gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).θ ν)
    (hγ : ∀ ν, (γr ν : UnitAddCircle)
      = (gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).γ ν)
    (hmη : (2 : ℝ)⁻¹ ^ m ≤ η)
    {δ M δ₂ δ₃ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM : 0 < M)
    (hD : (gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).PropD δ₂)
    (hC : (gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).PropC δ₃)
    (hδ₃ : 0 ≤ δ₃)
    (hbudget :
      (2 : ℝ) ^ ((1 - δ / 2) * M)
          * (∑ G' ∈ (gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).goodSets,
              η ^ G'.card
                * (volume ((gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).pieceCube
                    G')).toReal)
        + δ₂ + 2 * (1 / ((gridFrame 4 hbb G X (apSample_nonempty G hX) sm γ hη hε Dg).res
            * Real.sqrt (Dg + 1)))
        + (((2 * Dg + 1) ^ G.rDim : ℕ) : ℝ) * δ₃
        < δ / (2 - δ)) :
    (1 - δ) * M < (jointLaw G hX m (primeLambertAtBase 4)).H₂ := by
  classical
  set hne := apSample_nonempty G hX with hnedef
  set fr := gridFrame 4 hbb G X hne sm γ hη hε Dg with hfr
  set L := jointLaw G hX m (primeLambertAtBase 4) with hL
  by_contra hcon
  push Not at hcon
  -- the information set
  set θth : ℝ := (1 - δ / 2) * M with hθth
  set B := L.infoSet θth with hB
  have hmass : δ / (2 - δ) ≤ L.prob B := L.prob_infoSet_ge hδ0 hδ1 hM hcon
  have hcardB : ((B.card : ℝ)) ≤ (2 : ℝ) ^ θth := L.card_infoSet_le θth
  -- the corresponding sub-sample
  set P := apSample X G.P₀ G.b₀ with hP
  set Good : Finset ℕ := P.filter (fun n => ZVec G m (primeLambertAtBase 4) n ∈ B) with hGood
  have hGoodsub : Good ⊆ P := Finset.filter_subset _ _
  have hdens : (Good.card : ℝ) / P.card = L.prob B := by
    rw [hL, jointLaw, prob_empirical]
  -- the joint boxes
  set 𝓑 : Finset (Fin G.hDim → ℝ) := B.image (centreOf G m) with h𝓑
  have hcard𝓑 : ((𝓑.card : ℝ)) ≤ (2 : ℝ) ^ θth :=
    le_trans (by exact_mod_cast Finset.card_image_le) hcardB
  have h𝓑ne : 𝓑.Nonempty := by
    rw [h𝓑, Finset.image_nonempty, ← Finset.card_pos]
    by_contra hzero
    push_neg at hzero
    have : B.card = 0 := by omega
    have hp0 : L.prob B = 0 := by
      rw [FinLaw.prob, Finset.card_eq_zero.1 this, Finset.sum_empty]
    have : (0 : ℝ) < δ / (2 - δ) := div_pos hδ0 (by linarith)
    linarith [hmass, hp0]
  -- §3A: every good sample point transports into the box image
  set E := imageOfSet fr (boxUnion fr 𝓑 ((2 : ℝ)⁻¹ ^ m)) with hE
  have hEne : E.Nonempty := by
    obtain ⟨b, hb⟩ := h𝓑ne
    refine imageOfSet_nonempty fr ⟨fun α => ((b α : ℝ) : UnitAddCircle), ?_⟩
    refine Set.mem_biUnion hb ?_
    intro α _
    refine ⟨b α, ⟨le_rfl, ?_⟩, rfl⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
    linarith
  have hcap : ∀ n ∈ Good, fr.Ffull n ∈ E := by
    intro n hn
    rw [hGood, Finset.mem_filter] at hn
    refine gridFrame_Ffull_mem_boxUnion G X hbb hne sm γ hη hε Dg m 𝓑 hn.1 ?_
    rw [← centreOf_ZVec]
    exact Finset.mem_image_of_mem _ hn.2
  -- (C)
  have hC' := Frame.capture_le fr hEne Good hGoodsub hcap hD hC hδ₃
  -- (G)
  have hG := volume_tube_le_joint fr θr γr hθ hγ (by positivity) hmη 𝓑 h𝓑ne
  rw [← hE] at hG
  have hsumle : ∑ G' ∈ fr.goodSets, (𝓑.card : ℝ) * η ^ G'.card
        * (volume (fr.pieceCube G')).toReal
      ≤ (2 : ℝ) ^ θth * ∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun G' _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hcard𝓑 (by positivity)
  have hPfr : fr.P = P := rfl
  have hnat : ((2 * fr.D + 1) ^ fr.r : ℕ) = (2 * Dg + 1) ^ G.rDim := rfl
  have hDR : (fr.D : ℝ) = (Dg : ℝ) := rfl
  rw [hPfr, hdens, hnat, hDR] at hC'
  have hηfr : fr.η = η := rfl
  rw [hηfr] at hG
  linarith [hmass, hC', hG.trans hsumle, hbudget]

end NormalNumbers.G4Entropy
