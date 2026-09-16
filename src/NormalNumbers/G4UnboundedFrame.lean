/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedAvg
import NormalNumbers.G4UnboundedTW

/-!
# Campaign B, step B2d/B2e: §4D for the unbounded weight

`G4WeightRemainder`'s `gridFrameW_weightC_propD` is now generic in the `TWeight`, so the only
thing §4D still needs for `TWeight.weightU c hT` is the three sample-average estimates at the
**effective constant** `effC c P₀ A` in place of `max C 1`:

* `bigAvgC` — weight-free, unchanged;
* `junkAvgC` — `junkAvgC_le'` plus `junkShiftBoundC_le_effC`;
* `farAvgW` — `sum_abs_farPartW_le_of_layer` fed by `sum_weightW_shiftG_le_effC`.

The resulting `gridFrameW_weightU_propD_of_bounds` is *literally* the bounded
`gridFrameW_weightC_propD_of_bounds` with `(C : ℝ)` and `((max C 1 : ℕ) : ℝ)` both replaced by
`effC c G.P₀ A`, so a schedule that supplies the bounded fields at any natural number
`C ≥ effC` supplies these.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **The far average, generic in the weight and in `κ`** — `farAvgC_le` with the pointwise
domination replaced by the per-layer hypothesis of `sum_abs_farPartW_le_of_layer`. -/
theorem farAvgW_le_of_layer (W : TWeight) (c : ℕ → ℕ)
    (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) ≤ weightW c m)
    (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hlay : ∀ (α : G.Atom) (j : ℕ), 1 ≤ j →
      ∑ n ∈ apSample X G.P₀ G.b₀, weightW c (n + shiftG G.B G.Q G.D₀ α j)
        ≤ κ * ((apSample X G.P₀ G.b₀).card
              * ((farC G X Dm + 2 * j) / Real.log 2 + ((Ω G.P₀ : ℕ) : ℝ))
            + junkShiftBound G.P₀ X (j * Dm))) :
    farAvgW W bb G X
      ≤ κ * ((2 : ℝ) ^ G.K *
          ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
                / ((apSample X G.P₀ G.b₀).card : ℝ))) := by
  have hbr : (3 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hbr2 : (2 : ℝ) ≤ bb := by linarith
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set Bd : ℝ := κ * ((2 : ℝ) ^ G.K *
      ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
          + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
        + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm) / (P.card : ℝ))) with hBd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCn := farC_nonneg G X hne Dm
  have hfb := farBound_nonneg hbr2 (G.K + G.N) hCn
  have hfj := farJunkBound_nonneg hbr (G.K + G.N) (junkA_nonneg G.P₀ X) (junkB_nonneg X Dm)
  have hgeo : (0 : ℝ)
      ≤ ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))) := by
    have h1 : (0 : ℝ) < bb - 1 := by linarith
    have h2 : (0 : ℝ) ≤ 1 / (bb : ℝ) := by positivity
    positivity
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    have h4 : (0 : ℝ) ≤ farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm) / (P.card : ℝ) :=
      div_nonneg hfj hc.le
    have h5 : (0 : ℝ) ≤ farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2 :=
      div_nonneg hfb hlog2.le
    positivity
  have hrow : ∀ ν : Fin G.rDim,
      (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW W bb G n (G.rowEquiv.symm ν)| ≤ Bd := by
    intro ν
    have h := sum_abs_farPartW_le_of_layer W c hW bb hbb G X hne hP₀ hDm hκ0 hlay
      (G.rowEquiv.symm ν)
    rw [← hP] at h
    calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW W bb G n (G.rowEquiv.symm ν)|
        ≤ (P.card : ℝ)⁻¹ * (κ * ((2 : ℝ) ^ G.K *
            ((P.card : ℝ) * (farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
                + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
              + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Bd := by rw [hBd]; field_simp
  unfold farAvgW
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |farPartW W bb G n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |farPartW W bb G n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ hBd0 fun ν _ => hrow ν

/-- **The far average for the tame weight at the effective constant.** -/
theorem farAvgW_le_effC (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A) (bb : ℕ) (hbb : 3 ≤ bb)
    (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    (hΩ : (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ)) {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (W : TWeight)
    (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) ≤ weightW c m) :
    farAvgW W bb G X
      ≤ effC c G.P₀ A * ((2 : ℝ) ^ G.K *
          ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
                / ((apSample X G.P₀ G.b₀).card : ℝ))) :=
  farAvgW_le_of_layer W c hW bb hbb G X hne hP₀ hDm (effC_nonneg (c := c) hT.one_le G.P₀)
    (fun α j hj => sum_weightW_shiftG_le_effC c hT G X hne hP₀ hΩ hDm α hj)

/-- **§4D for the unbounded (tame) weight**, at the effective constant `effC c G.P₀ A`. -/
theorem gridFrameW_weightU_propD_of_bounds (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A)
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
    (hjunk : (effC c G.P₀ A * junkShiftBound G.P₀ X ρmax
          / ((apSample X G.P₀ G.b₀).card : ℝ)) * rowL1 bb G.K ≤ δjunk * (ε * η))
    (hfar : effC c G.P₀ A * ((2 : ℝ) ^ G.K *
        ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
            + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
          + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
              / ((apSample X G.P₀ G.b₀).card : ℝ))) ≤ δfar * (ε * η)) :
    (gridFrameW (TWeight.weightU c hT) bb (by omega) G X hne (smallPrimes R G.P₀)
      (frozenGammaC c bb G) hη hε D).PropD (δbig + δjunk + δfar) := by
  have hcard : (0 : ℝ) < ((apSample X G.P₀ G.b₀).card : ℝ) := by exact_mod_cast hne.card_pos
  refine gridFrameW_weightC_propD c (TWeight.weightU c hT) (TWeight.weightU_wN c hT) bb
    (by omega) G X hne R hη hε D
    ((bigAvgC_le' bb (by omega) G X R Y hne hK hR hRY hMx1 hMx).trans hbig) ?_
    ((farAvgW_le_effC c hT bb hbb G X hne hP₀ hΩ hDm (TWeight.weightU c hT)
      (fun m => le_of_eq (TWeight.weightU_wN c hT m))).trans hfar)
  refine (junkAvgC_le' c bb (by omega) G X hne hP₀ hρm).trans (le_trans ?_ hjunk)
  have h := junkShiftBoundC_le_effC hT G.P₀ X ρmax
  have hrow : 0 ≤ rowL1 bb G.K :=
    rowL1_nonneg (by exact_mod_cast (show 2 ≤ bb by omega) : (2:ℝ) ≤ bb) G.K
  gcongr

end NormalNumbers.G4
