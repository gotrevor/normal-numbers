/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4GridTube
import NormalNumbers.G4Jackson
import NormalNumbers.G4FarTail

/-!
# G4 disjunctivity, §5 interface: a schedule witness gives `SeparatingFrameExists`

Every named input of brief §4 is now discharged on the concrete `gridFrame`:
`gridFrame_propA`, `gridFrame_propB_of_bound` (one real inequality),
`gridFrame_propC` (a closed-form `δ₃`), `gridFrame_propD_of_bounds` (two real inequalities)
and `Frame.propJackson` (no side conditions).  This file packages what the §5 schedule must
supply for one omitted base-four cylinder `[w/4^ℓ, (w+1)/4^ℓ)` as a `ScheduleWitness ℓ w`:
the grid parameters, the scales `X, R, Y, M, D`, the resolutions `η, ε`, and the **five real
inequalities** (B, D-big, D-far, and the closed budget), together with the bookkeeping side
conditions.  `separatingFrameExists_of_witness` turns a witness for every cylinder into
`SeparatingFrameExists`, hence (via `isDisjunctive_four_of_frames`) into the headline.

Nothing here is proved about the schedule; this is the exact residual obligation.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **What §5 must supply** for the omitted cylinder `[w/4^ℓ, (w+1)/4^ℓ)`. -/
structure ScheduleWitness (ℓ w : ℕ) where
  /-- grid parameters -/
  G : GridParams
  hK : 0 < G.K
  hr : 1 ≤ G.rDim
  /-- outer scale -/
  X : ℕ
  hne : (apSample X G.P₀ G.b₀).Nonempty
  /-- resolution and tube fraction -/
  η : ℝ
  hη : 0 < η
  ε : ℝ
  hε : 0 < ε
  hε1 : ε < 1
  /-- cylinder depth for B -/
  M : ℕ
  hM : 1 / ((4 : ℝ) ^ ℓ) ^ M ≤ η
  /-- spectral bound -/
  Lg : ℝ
  hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg
  /-- **B** -/
  δ₁ : ℝ
  hδ₁ : 0 ≤ δ₁
  hB : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
    (((4 ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
      * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
      ≤ δ₁ / 2 ^ G.rDim
  /-- small-prime cutoff and the medium cutoff -/
  R : ℕ
  hR : 2 ≤ R
  Y : ℕ
  hRY : R ≤ Y
  /-- Jackson degree -/
  D : ℕ
  hN : 1 + Nat.clog 4 (2 ^ G.K * D) ≤ G.N
  /-- **C** moment order and Laplace parameters -/
  Mc : ℕ
  hMc : 1 ≤ Mc
  lam' : ℝ
  hlam' : 1 ≤ lam'
  lam : ℝ
  hlam : 0 < lam
  /-- **D** size bounds -/
  Mx : ℝ
  hMx1 : 1 ≤ Mx
  hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
    ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx
  Dm : ℕ
  hDm : ∀ α, G.d α ≤ Dm
  δbig : ℝ
  δfar : ℝ
  hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R))
          * ((1 / 8 : ℝ) ^ G.K / 15)
        + 2 * (Y : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ G.K / 3) ^ 2 / (apSample X G.P₀ G.b₀).card)
      + (Real.log Mx / Real.log Y) * (1 / 2 : ℝ) ^ G.K / 3 ≤ δbig * (ε * η)
  hfar : (2 : ℝ) ^ G.K / Real.log 2
    * ((1 / 4 : ℝ) ^ (G.K + G.N) * ((farC G X Dm + 2 * (G.K + G.N : ℕ) + 2) / 3 + 2 / 9))
      ≤ δfar * (ε * η)
  /-- **the closed budget** `δ₁ + δ₂ + 2κ + Λ δ₃ < 1` -/
  hbudget : δ₁ + (δbig + δfar) + 2 * (1 / (ε * η * Real.sqrt (D + 1)))
    + (((2 * D + 1) ^ G.rDim : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes R G.P₀) (Fintype.card G.Idx) R Mc
          (apSample X G.P₀ G.b₀).card lam' lam (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K) < 1

lemma smallPrimeBound_nonneg (sm : Finset ℕ) (T R M Psz : ℕ) {lam' lam θ₀ : ℝ}
    (hlam' : 0 < lam') (hlam : 0 < lam) : 0 ≤ smallPrimeBound sm T R M Psz lam' lam θ₀ := by
  unfold smallPrimeBound
  positivity

/-- **The residual obligation of the whole campaign.**  A schedule witness for every omitted
base-four cylinder gives `SeparatingFrameExists`, hence the headline. -/
theorem separatingFrameExists_of_witness
    (hw : ∀ ℓ w : ℕ, w < 4 ^ ℓ →
      (∀ m, orbit 4 primeLambertFour m ∉
        Set.Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ)) →
      Nonempty (ScheduleWitness ℓ w)) :
    SeparatingFrameExists 4 := by
  intro a c ha hac hc hno
  obtain ⟨ℓ, w, hw4, hsub⟩ := exists_cylinder_subset ha hac hc
  have hno' : ∀ n, orbit 4 primeLambertFour n ∉ Set.Ico a c := hno
  have homit : ∀ m, orbit 4 primeLambertFour m ∉
      Set.Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ) := fun m h => hno' m (hsub h)
  obtain ⟨W⟩ := hw ℓ w hw4 homit
  refine ⟨gridFrame W.G W.X W.hne (smallPrimes W.R W.G.P₀) (frozenGamma W.G) W.hη W.hε W.D,
    W.δ₁, W.δbig + W.δfar, _, _, _,
    gridFrame_propA _ _ _ _ _ _ _ _,
    gridFrame_propB_of_bound W.G W.X W.hne _ _ W.hη W.hε W.D hw4 homit W.M W.hM W.hε1 W.hr
      W.hlog W.hδ₁ W.hB,
    gridFrame_propC W.G W.X W.hne _ _ W.hη W.hε (R := W.R)
      (fun p hp => (mem_smallPrimes.1 hp).1) (fun p hp => (mem_smallPrimes.1 hp).2.2)
      (by have := W.hR; omega) (fun p hp => (mem_smallPrimes.1 hp).2.1) W.hN W.hMc W.hlam'
      W.hlam,
    gridFrame_propD_of_bounds W.G W.X W.R W.Y W.hne W.hK W.hR W.hRY W.hMx1 W.hMx W.hDm
      W.hη W.hε W.D W.hbig W.hfar,
    Frame.propJackson _,
    smallPrimeBound_nonneg _ _ _ _ _ (by linarith [W.hlam']) W.hlam, ?_⟩
  exact W.hbudget

/-- The headline, conditional on the witness. -/
theorem isDisjunctive_four_of_witness
    (hw : ∀ ℓ w : ℕ, w < 4 ^ ℓ →
      (∀ m, orbit 4 primeLambertFour m ∉
        Set.Ico ((w : ℝ) / 4 ^ ℓ) (((w : ℝ) + 1) / 4 ^ ℓ)) →
      Nonempty (ScheduleWitness ℓ w)) :
    IsDisjunctive 4 primeLambertFour :=
  isDisjunctive_four_of_frames (separatingFrameExists_of_witness hw)

end NormalNumbers.G4
