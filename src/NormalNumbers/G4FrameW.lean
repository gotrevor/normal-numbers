/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Frame
import NormalNumbers.G4TransportW
import NormalNumbers.G4GridTube

/-!
# The concrete frame for a general additive weight, and `PropA`

`G4Frame.gridFrame` hard-codes the weight `ω` and the constant `primeLambertAtBase bb`.  This
module repeats the same construction over a `TWeight` `W` (`G4TransportW`), giving

  `gridFrameW W bb hbb G X hne sm γ hη hε D : Frame`

with `w = W.wN`, `x = W.lambert bb`, and the transport translate `θ` built from `W.corrB` at the
frozen residue `c = 0`.  Two facts:

* `gridFrameW_omega` — with `W = TWeight.omega` this is *definitionally* the old `gridFrame`, so
  nothing downstream of `gridFrame` has to move;
* `gridFrameW_propA` — `PropA` for the general frame, by `Frame.propA_of_progressionW`.

For campaign A the instance is `W = TWeight.subset S` and `x = subsetLambert S bb`
(`gridFrameW_subset_x`).  Note the small-prime vector field `S` of the frame is *already*
parametrized by the finset `sm` of active primes, and `ω_S` restricted to a finset of primes is
`omegaOn (sm.filter S)`: the `S`-restriction of the local layer costs no new machinery, only a
different `sm`.
-/

open MeasureTheory Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **The concrete frame with a general weight.** -/
noncomputable def gridFrameW (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) : Frame where
  bse := bb
  hbse := hbb
  w := fun m => (W.wN m : ℝ)
  x := W.lambert bb
  K := G.K
  J := G.K + G.N
  r := G.rDim
  H := G.hDim
  A := G.Amat
  d := fun α => G.d (G.atomEquiv.symm α)
  t := fun α => G.t (G.atomEquiv.symm α)
  ht := fun α => G.t_lt_d _
  P := apSample X G.P₀ G.b₀
  hP := hne
  θ := fun ν => ((∑ α : Fin G.hDim, (G.Amat ν α : ℝ) *
    ((W.wN (G.d (G.atomEquiv.symm α)) : ℝ) / ((bb : ℝ) - 1)
      - W.corrB bb (G.d (G.atomEquiv.symm α)) 0) : ℝ) :
      UnitAddCircle)
  γ := γ
  S := fun n ν => ((Sval bb sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν) : ℝ) :
    UnitAddCircle)
  η := η
  hη := hη
  ε := ε
  hε := hε
  D := D

/-- With the weight `ω`, the general frame *is* `gridFrame`. -/
theorem gridFrameW_omega (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    gridFrameW TWeight.omega bb hbb G X hne sm γ hη hε D
      = gridFrame bb hbb G X hne sm γ hη hε D := rfl

@[simp] lemma gridFrameW_r (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ) (hne)
    (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).r = G.rDim := rfl

@[simp] lemma gridFrameW_H (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ) (hne)
    (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).H = G.hDim := rfl

/-- For the prime-subset weight the constant under test is `c_S(bb) = ∑_n ω_S(n)/bbⁿ`. -/
lemma gridFrameW_subset_x (S : ℕ → Prop) [DecidablePred S] (bb : ℕ) (hbb : 2 ≤ bb)
    (G : GridParams) (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW (TWeight.subset S) bb hbb G X hne sm γ hη hε D).x = subsetLambert S bb :=
  TWeight.lambert_subset S

/-- **`PropA` for the general-weight frame.**  Same proof as `gridFrame_propA`: the progression
`n ≡ b₀ (P₀)` freezes every multiplier residue at `0`, and the frame's `θ` is the transport
translate of `c = 0` by construction. -/
theorem gridFrameW_propA (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).PropA := by
  set fr := gridFrameW W bb hbb G X hne sm γ hη hε D with hfr
  refine fr.propA_of_progressionW W rfl rfl 0 (fun α => (G.d_pos _).ne') rfl ?_
  intro n hn
  choose k hk1 hk2 using fun α : Fin fr.H => G.exists_mult_mul hn (G.atomEquiv.symm α)
  refine ⟨k, hk1, ?_⟩
  intro α p hp
  have hpd : p ∣ G.d (G.atomEquiv.symm α) := (Nat.mem_primeFactors.1 hp).2.1
  have : p ∣ k α := hpd.trans (hk2 α)
  simpa [Nat.ModEq] using (Nat.mod_eq_zero_of_dvd this)

/-! ### `PropC` and `PropB` for the general-weight frame -/

/-- **`PropC` for the general-weight frame.**  `PropC` sees only `P`, `S` and `D`, and those
three fields of `gridFrameW` are the fields of `gridFrame`, so the §4C bound is the same one. -/
theorem gridFrameW_propC_gen (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) {D : ℕ}
    (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, ¬ p ∣ G.P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    (hN : 1 + Nat.clog bb (2 ^ G.K * D) ≤ G.N)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).PropC
      (smallPrimeBound sm (Fintype.card G.Idx) R M (apSample X G.P₀ G.b₀).card lam' lam
        (freqSeed bb G.K)) :=
  gridFrame_propC_gen bb hbb G X hne sm γ hη hε hs hsP hR1 hR hN hM hlam' hlam

/-- The cylinder cover for an arbitrary constant `x`: `G4GridTube.exists_cover_of_omit` never
used anything about `primeLambertAtBase`. -/
lemma exists_cover_of_omit_gen (bb : ℕ) (hbb : 2 ≤ bb) {x : ℝ} {ℓ w : ℕ} (hw : w < bb ^ ℓ)
    (homit : ∀ m, orbit bb x m ∉
      Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) (M : ℕ) :
    ∃ Bs : Finset ℝ, Bs.card ≤ (bb ^ ℓ - 1) ^ M ∧
      orbitClosureOf bb x ⊆ ⋃ c ∈ Bs, ((↑) : ℝ → UnitAddCircle) ''
        Set.Icc c (c + 1 / ((bb : ℝ) ^ ℓ) ^ M) := by
  refine ⟨(admissible (bb ^ ℓ) M ⟨w, hw⟩).image (cylLeft (bb ^ ℓ) M), ?_, ?_⟩
  · exact Finset.card_image_le.trans (card_admissible _ _ _).le
  · intro y hy
    unfold orbitClosureOf at hy
    have := orbitClosure_subset_cylinders (bb := bb) (by omega) hw homit M hy
    rw [Set.mem_iUnion₂] at this ⊢
    obtain ⟨c, hc, hyc⟩ := this
    refine ⟨cylLeft (bb ^ ℓ) M c, Finset.mem_image_of_mem _ hc, ?_⟩
    unfold cyl at hyc
    push_cast at hyc
    exact hyc

/-- **`PropB` for the general-weight frame**, from the same real inequality: the only input
about the constant is that its orbit omits a base-`bb` block. -/
theorem gridFrameW_propB_of_bound (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ)
    {ℓ w : ℕ} (hw : w < bb ^ ℓ)
    (homit : ∀ m, orbit bb (W.lambert bb) m ∉
      Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ))
    (M : ℕ) (hM : 1 / ((bb : ℝ) ^ ℓ) ^ M ≤ η) (hε1 : ε < 1) (hr : 1 ≤ G.rDim)
    {Lg : ℝ} (hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg)
    {δ₁ : ℝ} (hδ : 0 ≤ δ₁)
    (hbound : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
      (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
        ≤ δ₁ / 2 ^ G.rDim) :
    (gridFrameW W bb hbb G X hne sm γ hη hε D).PropB δ₁ := by
  classical
  set fr := gridFrameW W bb hbb G X hne sm γ hη hε D with hfr
  obtain ⟨Bs, hBs, hcov⟩ := exists_cover_of_omit_gen bb hbb hw homit M
  choose θr hθr using fun ν => QuotientAddGroup.mk_surjective (fr.θ ν)
  choose γr hγr using fun ν => QuotientAddGroup.mk_surjective (fr.γ ν)
  unfold Frame.PropB
  refine (fr.volume_tube_le θr γr hθr hγr hM Bs hcov).trans ?_
  have hterm : ∀ Gs ∈ fr.goodSets,
      (Bs.card : ℝ) ^ fr.H * η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal
        ≤ δ₁ / 2 ^ G.rDim := by
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
    have hpc : (volume (fr.pieceCube Gs)).toReal ≤ Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / Gs.card) * Real.sqrt (G.hDim + Gs.card))
          ^ Gs.card :=
      gridFrame_volume_pieceCube_le bb hbb G X hne sm γ hη hε D Gs hpos hlog
    refine le_trans ?_ (hbound Gs.card hge hle)
    have h1 : (Bs.card : ℝ) ^ G.hDim ≤ (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim := by
      have : (Bs.card : ℝ) ≤ (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) := by exact_mod_cast hBs
      exact pow_le_pow_left₀ (by positivity) this _
    show (Bs.card : ℝ) ^ G.hDim * η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal ≤ _
    calc (Bs.card : ℝ) ^ G.hDim * η ^ Gs.card * (volume (fr.pieceCube Gs)).toReal
        ≤ (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ Gs.card
          * (Real.exp (Lg / 2)
            * (Real.sqrt (2 * Real.pi * Real.exp 1 / Gs.card) * Real.sqrt (G.hDim + Gs.card))
              ^ Gs.card) := by
          have hη0 : (0 : ℝ) ≤ η ^ Gs.card := by positivity
          have hv : (0 : ℝ) ≤ (volume (fr.pieceCube Gs)).toReal := ENNReal.toReal_nonneg
          gcongr
      _ = _ := by ring
  calc ∑ Gs ∈ fr.goodSets, (Bs.card : ℝ) ^ fr.H * η ^ Gs.card
        * (volume (fr.pieceCube Gs)).toReal
      ≤ ∑ _Gs ∈ fr.goodSets, δ₁ / 2 ^ G.rDim := Finset.sum_le_sum hterm
    _ = (fr.goodSets.card : ℝ) * (δ₁ / 2 ^ G.rDim) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ G.rDim * (δ₁ / 2 ^ G.rDim) := by
        have hc : (fr.goodSets.card : ℝ) ≤ (2 : ℝ) ^ G.rDim := by
          have h := card_goodSets_le fr
          have : fr.goodSets.card ≤ 2 ^ G.rDim := h
          exact_mod_cast this
        have : (0 : ℝ) ≤ δ₁ / 2 ^ G.rDim := by positivity
        exact mul_le_mul_of_nonneg_right hc this
    _ = δ₁ := by field_simp

end NormalNumbers.G4
