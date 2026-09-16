/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaWeight
import NormalNumbers.G4RemainderW

/-!
# G5 §4D for `Ω`: the four-way split of the retained tail, and `PropD`

`Ω = ω + excess 1`, and both summands split on the progression modulus `P₀`:

    Ω(m) = [ ω_{p ∣ P₀}(m) + frozenExcess(m) ]   (constant on the progression → the translate γ)
         + ω_{smallPrimes R P₀}(m)               (the frame's retained vector)
         + ω_big(m)                              (the §4D large-prime junk, as for `ω`)
         + junk(m)                               (the §4D *valuation* junk, new for `Ω`)

`cardFactors_split` is that identity; `blockSum_cardFactors_split` transports it through one
layer block; `gridFrameW_cardFactors_Ffull_decomp` is the resulting shape of `Ffull`; and
`gridFrameW_cardFactors_propD` reduces `PropD` to **three** sample averages — the two `ω` ones
(`bigAvgΩ`, `farAvgΩ`) and the new `junkAvgΩ`, whose arithmetic input is
`G4WeightJunk.sum_junk_le`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-! ### The pointwise split -/

/-- **The four-way split of `Ω`** at a progression modulus `P₀` and a small-prime cutoff `R`. -/
theorem cardFactors_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    (Ω m : ℝ)
      = ((omegaOn P₀.primeFactors m : ℕ) : ℝ) + frozenExcess (fun _ => (1 : ℕ)) P₀ m
        + ((omegaOn (smallPrimes R P₀) m : ℕ) : ℝ)
        + ((omegaBig R P₀ m : ℕ) : ℝ) + junk (fun _ => (1 : ℕ)) P₀ m := by
  have h1 := cardFactors_eq_omegaR_add_excess m
  have h3 := excess_eq_frozen_add_junk (fun _ => (1 : ℕ)) hP₀ hm
  rw [h1, h3, omegaR, omega_split R hP₀ hm]
  push_cast
  ring

/-! ### The frozen translate for `Ω` -/

/-- The weight the modulus freezes: the `P₀`-prime count plus the frozen excess. -/
noncomputable def frozenWeightΩ (P₀ m : ℕ) : ℝ :=
  ((omegaOn P₀.primeFactors m : ℕ) : ℝ) + frozenExcess (fun _ => (1 : ℕ)) P₀ m

/-- The `Ω`-frozen translate. -/
noncomputable def frozenTranslateΩ (bb : ℕ) (G : GridParams) (ν : Fin G.rDim) : ℝ :=
  blockSum bb G (frozenWeightΩ G.P₀) G.b₀ (G.rowEquiv.symm ν)

/-- The `Ω`-frozen translate as a point of the torus. -/
noncomputable def frozenGammaΩ (bb : ℕ) (G : GridParams) : Torus G.rDim :=
  fun ν => ((frozenTranslateΩ bb G ν : ℝ) : UnitAddCircle)

lemma blockSum_frozenΩ_eq (bb : ℕ) (G : GridParams) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (a : Fin G.K → Fin G.s) :
    blockSum bb G (frozenWeightΩ G.P₀) n a
      = blockSum bb G (frozenWeightΩ G.P₀) G.b₀ a := by
  refine blockSum_congr bb G a fun α jj => ?_
  have h1 : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have h2 : G.b₀ % G.P₀ = G.b₀ := Nat.mod_eq_of_lt G.b₀_lt_P₀
  have hρ : 0 < shiftAL G.B G.Q G.D₀ (α, jj) := shiftAL_pos G (α, jj)
  unfold frozenWeightΩ
  rw [omegaOn_primeFactors_congr (h1.trans h2.symm),
    frozenExcess_congr (fun _ => (1 : ℕ)) (h1.trans h2.symm) (by omega) (by omega)]

/-! ### The block split -/

/-- **The exact remainder decomposition for `Ω`.** -/
theorem blockSum_cardFactors_split (bb : ℕ) (G : GridParams) (R : ℕ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => (Ω m : ℝ)) n a
      = blockSum bb G (frozenWeightΩ G.P₀) n a
        + Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n a
        + blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n a
        + blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n a := by
  rw [Sval_eq_blockSum, ← blockSum_add, ← blockSum_add, ← blockSum_add]
  refine blockSum_congr bb G a fun α jj => ?_
  have hρ : 0 < shiftAL G.B G.Q G.D₀ (α, jj) := shiftAL_pos G (α, jj)
  have h := cardFactors_split R (P₀ := G.P₀) (m := n + shiftAL G.B G.Q G.D₀ (α, jj))
    G.P₀_pos.ne' (by omega)
  rw [h]
  unfold frozenWeightΩ
  ring

/-! ### `Ffull` for `Ω`, fully decomposed -/

theorem gridFrameW_cardFactors_Ffull_decomp (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrameW TWeight.cardFactors bb hbb G X hne (smallPrimes R G.P₀)
        (frozenGammaΩ bb G) hη hε D).Ffull n ν
      = (((Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
          + blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
          + blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)
          + farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle) := by
  have hw : (fun m => (TWeight.cardFactors.wN m : ℝ)) = fun m => (Ω m : ℝ) := rfl
  rw [gridFrameW_Ffull_eq TWeight.cardFactors bb hbb G X hne _ _ hη hε D hn ν,
    tailFrom_splitW TWeight.cardFactors bb hbb G X hne _ _ hη hε D hn ν, hw,
    blockSum_cardFactors_split bb G R n (G.rowEquiv.symm ν),
    blockSum_frozenΩ_eq bb G hn (G.rowEquiv.symm ν)]
  show (((frozenTranslateΩ bb G ν
      + Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
      + blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
      + blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)
      + farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle)
      - ((frozenTranslateΩ bb G ν : ℝ) : UnitAddCircle) = _
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  ring

/-! ### `PropD` for `Ω`, reduced to three sample averages -/

/-- The large-prime block average. -/
noncomputable def bigAvgΩ (bb : ℕ) (G : GridParams) (X R : ℕ) : ℝ :=
  ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
    (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
      |blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|

/-- The **valuation-junk** block average — the one term `ω` does not have. -/
noncomputable def junkAvgΩ (bb : ℕ) (G : GridParams) (X : ℕ) : ℝ :=
  ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
    (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
      |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|

/-- The far-tail average for `Ω`. -/
noncomputable def farAvgΩ (bb : ℕ) (G : GridParams) (X : ℕ) : ℝ :=
  ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
    (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
      |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|

/-- **`PropD` for `Ω`**, reduced to three arithmetic estimates. -/
theorem gridFrameW_cardFactors_propD (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δjunk δfar : ℝ}
    (hbig : bigAvgΩ bb G X R ≤ δbig * (ε * η))
    (hjunk : junkAvgΩ bb G X ≤ δjunk * (ε * η))
    (hfar : farAvgΩ bb G X ≤ δfar * (ε * η)) :
    (gridFrameW TWeight.cardFactors bb hbb G X hne (smallPrimes R G.P₀)
      (frozenGammaΩ bb G) hη hε D).PropD (δbig + δjunk + δfar) := by
  classical
  set fr := gridFrameW TWeight.cardFactors bb hbb G X hne (smallPrimes R G.P₀)
    (frozenGammaΩ bb G) hη hε D with hfr
  have hcard : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hstep : ∀ n ∈ apSample X G.P₀ G.b₀, dAv (fr.S n) (fr.Ffull n)
      ≤ (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
        + ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
          + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|) := by
    intro n hn
    have hpt : ∀ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)
        ≤ |blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
          + (|blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
            + |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|) := by
      intro ν
      rw [gridFrameW_cardFactors_Ffull_decomp bb hbb G X hne R hη hε D hn ν]
      refine (dist_coe_le' _ _).trans ?_
      have hrw : Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
              (G.rowEquiv.symm ν)
          - (Sval bb (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
              (G.rowEquiv.symm ν)
            + blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
            + blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)
            + farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν))
          = -(blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
              + (blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)
                + farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν))) := by ring
      rw [hrw, abs_neg]
      exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    calc dAv (fr.S n) (fr.Ffull n)
        = (∑ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)) / (G.rDim : ℝ) := rfl
      _ ≤ (∑ ν : Fin G.rDim,
            (|blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
              + (|blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
                + |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|)))
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
              |blockSum bb G (fun m => ((omegaBig R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
            + ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
              + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hcard
    _ = bigAvgΩ bb G X R + (junkAvgΩ bb G X + farAvgΩ bb G X) := by
        unfold bigAvgΩ junkAvgΩ farAvgΩ
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
    _ ≤ δbig * (ε * η) + (δjunk * (ε * η) + δfar * (ε * η)) :=
        add_le_add hbig (add_le_add hjunk hfar)
    _ = (δbig + δjunk + δfar) * (ε * η) := by ring

end NormalNumbers.G4
