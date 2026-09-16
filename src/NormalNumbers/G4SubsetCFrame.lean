/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetCTW
import NormalNumbers.G4UnboundedFrame
import NormalNumbers.G4SubsetJunk

/-!
# Campaign B: §4D for the merged weight `w_{c,S}`, at the effective constant

The merged four-way split is the `S`-filtered `weightC_split`:

    w_{c,S}(m) = [ ω_S restricted to p ∣ P₀ + frozenExcess_{c·1_S}(m) ]   (frozen → γ)
               + ω_{(smallPrimes R P₀) ∩ S}(m)                            (retained vector)
               + ω_{S,big}(m)                                             (large-prime junk)
               + junk_{c·1_S}(m)                                          (valuation junk)

so §4D reduces to the three sample averages already available:

* `bigAvgS_le'` — the `S`-large-prime average, weight-free (campaign A);
* `junkAvgC_le'` at the coefficient vector `c·1_S`, plus `junkShiftBoundC_le_effC`
  (`Tame (coeffOn S c) A` by `tame_coeffOn`);
* `farAvgW_le_effC` for `W = TWeight.weightSU`, which now only needs the *domination*
  `w_{c,S} ≤ w_c` (`weightSU_le`).
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (S : ℕ → Prop) [DecidablePred S] (c : ℕ → ℕ)

/-! ### The pointwise split -/

/-- **The four-way split of `w_{c,S}`.** -/
theorem weightSC_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    weightSW S c m
      = ((omegaOn (P₀.primeFactors.filter S) m : ℕ) : ℝ) + frozenExcess (coeffOn S c) P₀ m
        + ((omegaOn ((smallPrimes R P₀).filter S) m : ℕ) : ℝ)
        + ((omegaBigS S R P₀ m : ℕ) : ℝ) + junk (coeffOn S c) P₀ m := by
  have h3 := excess_eq_frozen_add_junk (coeffOn S c) hP₀ hm
  rw [weightSW, h3, omegaS_split S R hP₀ hm]
  push_cast
  ring

/-! ### The frozen translate -/

/-- The weight the modulus freezes for `w_{c,S}`. -/
noncomputable def frozenWeightSC (P₀ m : ℕ) : ℝ :=
  ((omegaOn (P₀.primeFactors.filter S) m : ℕ) : ℝ) + frozenExcess (coeffOn S c) P₀ m

/-- The merged frozen translate. -/
noncomputable def frozenTranslateSC (bb : ℕ) (G : GridParams) (ν : Fin G.rDim) : ℝ :=
  blockSum bb G (frozenWeightSC S c G.P₀) G.b₀ (G.rowEquiv.symm ν)

/-- The merged frozen translate as a point of the torus. -/
noncomputable def frozenGammaSC (bb : ℕ) (G : GridParams) : Torus G.rDim :=
  fun ν => ((frozenTranslateSC S c bb G ν : ℝ) : UnitAddCircle)

lemma blockSum_frozenSC_eq (bb : ℕ) (G : GridParams) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (a : Fin G.K → Fin G.s) :
    blockSum bb G (frozenWeightSC S c G.P₀) n a
      = blockSum bb G (frozenWeightSC S c G.P₀) G.b₀ a := by
  refine blockSum_congr bb G a fun α jj => ?_
  have h1 : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have h2 : G.b₀ % G.P₀ = G.b₀ := Nat.mod_eq_of_lt G.b₀_lt_P₀
  have hρ : 0 < shiftAL G.B G.Q G.D₀ (α, jj) := shiftAL_pos G (α, jj)
  unfold frozenWeightSC
  rw [omegaOn_filter_primeFactors_congr S (h1.trans h2.symm),
    frozenExcess_congr (coeffOn S c) (h1.trans h2.symm) (by omega) (by omega)]

/-! ### The block split -/

/-- **The exact remainder decomposition for `w_{c,S}`.** -/
theorem blockSum_weightSC_split (bb : ℕ) (G : GridParams) (R : ℕ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => weightSW S c m) n a
      = blockSum bb G (frozenWeightSC S c G.P₀) n a
        + Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n a
        + blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n a
        + blockSum bb G (junk (coeffOn S c) G.P₀) n a := by
  rw [Sval_eq_blockSum, ← blockSum_add, ← blockSum_add, ← blockSum_add]
  refine blockSum_congr bb G a fun α jj => ?_
  have hρ : 0 < shiftAL G.B G.Q G.D₀ (α, jj) := shiftAL_pos G (α, jj)
  have h := weightSC_split S c R (P₀ := G.P₀) (m := n + shiftAL G.B G.Q G.D₀ (α, jj))
    G.P₀_pos.ne' (by omega)
  rw [h]
  unfold frozenWeightSC
  ring

/-! ### `Ffull`, fully decomposed -/

theorem gridFrameW_weightSC_Ffull_decomp (W : TWeight)
    (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) = weightSW S c m) (bb : ℕ)
    (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrameW W bb hbb G X hne ((smallPrimes R G.P₀).filter S)
        (frozenGammaSC S c bb G) hη hε D).Ffull n ν
      = (((Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
            (G.rowEquiv.symm ν)
          + blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
          + blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)
          + farPartW W bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle) := by
  have hw : (fun m => ((W).wN m : ℝ)) = fun m => weightSW S c m := funext fun m => hW m
  rw [gridFrameW_Ffull_eq W bb hbb G X hne _ _ hη hε D hn ν,
    tailFrom_splitW W bb hbb G X hne _ _ hη hε D hn ν, hw,
    blockSum_weightSC_split S c bb G R n (G.rowEquiv.symm ν),
    blockSum_frozenSC_eq S c bb G hn (G.rowEquiv.symm ν)]
  show (((frozenTranslateSC S c bb G ν
      + Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
          (G.rowEquiv.symm ν)
      + blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
      + blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)
      + farPartW W bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle)
      - ((frozenTranslateSC S c bb G ν : ℝ) : UnitAddCircle) = _
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  ring

/-! ### `PropD`, reduced to three sample averages -/

/-- **`PropD` for the merged weight**, reduced to the three arithmetic estimates. -/
theorem gridFrameW_weightSC_propD (W : TWeight)
    (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) = weightSW S c m) (bb : ℕ)
    (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δjunk δfar : ℝ}
    (hbig : bigAvgS S bb G X R ≤ δbig * (ε * η))
    (hjunk : junkAvgC (coeffOn S c) bb G X ≤ δjunk * (ε * η))
    (hfar : farAvgW W bb G X ≤ δfar * (ε * η)) :
    (gridFrameW W bb hbb G X hne ((smallPrimes R G.P₀).filter S)
      (frozenGammaSC S c bb G) hη hε D).PropD (δbig + δjunk + δfar) := by
  classical
  set fr := gridFrameW W bb hbb G X hne ((smallPrimes R G.P₀).filter S)
    (frozenGammaSC S c bb G) hη hε D with hfr
  have hcard : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hstep : ∀ n ∈ apSample X G.P₀ G.b₀, dAv (fr.S n) (fr.Ffull n)
      ≤ (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
        + ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)|
          + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |farPartW W bb G n (G.rowEquiv.symm ν)|) := by
    intro n hn
    have hpt : ∀ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)
        ≤ |blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
          + (|blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)|
            + |farPartW W bb G n (G.rowEquiv.symm ν)|) := by
      intro ν
      rw [gridFrameW_weightSC_Ffull_decomp S c W hW bb hbb G X hne R hη hε D hn ν]
      refine (dist_coe_le' _ _).trans ?_
      have hrw : Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
              (G.rowEquiv.symm ν)
          - (Sval bb ((smallPrimes R G.P₀).filter S) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
              (G.rowEquiv.symm ν)
            + blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
            + blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)
            + farPartW W bb G n (G.rowEquiv.symm ν))
          = -(blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
              + (blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)
                + farPartW W bb G n (G.rowEquiv.symm ν))) := by ring
      rw [hrw, abs_neg]
      exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    calc dAv (fr.S n) (fr.Ffull n)
        = (∑ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)) / (G.rDim : ℝ) := rfl
      _ ≤ (∑ ν : Fin G.rDim,
            (|blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
              + (|blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)|
                + |farPartW W bb G n (G.rowEquiv.symm ν)|)))
            / (G.rDim : ℝ) := by
            gcongr with ν
            exact hpt ν
      _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            ring
  show ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
      dAv (fr.S n) (fr.Ffull n) ≤ (δbig + δjunk + δfar) * fr.res
  have hres : fr.res = ε * η := rfl
  rw [hres]
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        dAv (fr.S n) (fr.Ffull n)
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
          ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
              |blockSum bb G (fun m => ((omegaBigS S R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
            + ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |blockSum bb G (junk (coeffOn S c) G.P₀) n (G.rowEquiv.symm ν)|
              + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |farPartW W bb G n (G.rowEquiv.symm ν)|)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hcard
    _ = bigAvgS S bb G X R + (junkAvgC (coeffOn S c) bb G X + farAvgW W bb G X) := by
        unfold bigAvgS junkAvgC farAvgW
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
    _ ≤ δbig * (ε * η) + (δjunk * (ε * η) + δfar * (ε * η)) :=
        add_le_add hbig (add_le_add hjunk hfar)
    _ = (δbig + δjunk + δfar) * (ε * η) := by ring

/-! ### §4D for the merged weight from the closed-form bounds -/

/-- **§4D for `w_{c,S}` at the effective constant** — the merged analogue of
`gridFrameW_weightU_propD_of_bounds`, with the `S`-filtered small primes. -/
theorem gridFrameW_weightSU_propD_of_bounds {A : ℝ} (hT : Tame c A)
    (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams)
    (X R Y : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    (hΩ : (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ))
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δjunk δfar : ℝ}
    (hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K ≤ δbig * (ε * η))
    (hjunk : (effC (coeffOn S c) G.P₀ A * junkShiftBound G.P₀ X ρmax
          / ((apSample X G.P₀ G.b₀).card : ℝ)) * rowL1 bb G.K ≤ δjunk * (ε * η))
    (hfar : effC c G.P₀ A * ((2 : ℝ) ^ G.K *
        ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
            + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
          + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
              / ((apSample X G.P₀ G.b₀).card : ℝ))) ≤ δfar * (ε * η)) :
    (gridFrameW (TWeight.weightSU S c hT) bb (by omega) G X hne
      ((smallPrimes R G.P₀).filter S)
      (frozenGammaSC S c bb G) hη hε D).PropD (δbig + δjunk + δfar) := by
  have hTS : Tame (coeffOn S c) A := tame_coeffOn hT S
  refine gridFrameW_weightSC_propD S c (TWeight.weightSU S c hT)
    (TWeight.weightSU_wN S c hT) bb (by omega) G X hne R hη hε D
    ((bigAvgS_le' S bb (by omega) G X R Y hne hK hR hRY hMx1 hMx).trans hbig) ?_
    ((farAvgW_le_effC c hT bb hbb G X hne hP₀ hΩ hDm (TWeight.weightSU S c hT)
      (TWeight.weightSU_le S c hT)).trans hfar)
  refine (junkAvgC_le' (coeffOn S c) bb (by omega) G X hne hP₀ hρm).trans (le_trans ?_ hjunk)
  have h := junkShiftBoundC_le_effC hTS G.P₀ X ρmax
  have hrow : 0 ≤ rowL1 bb G.K :=
    rowL1_nonneg (by exact_mod_cast (show 2 ≤ bb by omega) : (2:ℝ) ≤ bb) G.K
  gcongr

end NormalNumbers.G4
