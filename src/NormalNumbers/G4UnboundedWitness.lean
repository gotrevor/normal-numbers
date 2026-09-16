/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedFrame
import NormalNumbers.G4WeightWitness

/-!
# Campaign B: the §5 schedule interface for the unbounded (tame) weight

`ScheduleWitnessU c hT bb ℓ w` is `ScheduleWitnessC` with the two §4D budgets stated at the
**effective constant** `effC c G.P₀ A` instead of `C` and `max C 1`, and with the harmless
extra field `hΩ : 1 ≤ Ω(P₀)` the far-field split needs.  Everything else — A, B, C, the
Jackson budget — never sees the weight, so it is copied verbatim.
-/

open MeasureTheory Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A)

include hT

/-- **What §5 must supply for `∑_n w_c(n)/bbⁿ`** at the omitted cylinder. -/
structure ScheduleWitnessU (c : ℕ → ℕ) (A : ℝ) (bb ℓ w : ℕ) where
  /-- grid parameters -/
  G : GridParams
  hK : 0 < G.K
  hr : 1 ≤ G.rDim
  hP₀ : 0 < G.P₀
  hΩ : (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ)
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
  hM : 1 / ((bb : ℝ) ^ ℓ) ^ M ≤ η
  /-- spectral bound -/
  Lg : ℝ
  hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg
  /-- **B** -/
  δ₁ : ℝ
  hδ₁ : 0 ≤ δ₁
  hB : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
    (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
      * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
      ≤ δ₁ / 2 ^ G.rDim
  /-- small-prime cutoff and the medium cutoff -/
  R : ℕ
  hR : 2 ≤ R
  Y : ℕ
  hRY : R ≤ Y
  /-- Jackson degree -/
  D : ℕ
  hN : 1 + Nat.clog bb (2 ^ G.K * D) ≤ G.N
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
  ρmax : ℕ
  hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax
  δbig : ℝ
  δjunk : ℝ
  δfar : ℝ
  hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
        + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
      + (Real.log Mx / Real.log Y) * rowL1 bb G.K ≤ δbig * (ε * η)
  hjunk : (effC c G.P₀ A * junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ))
      * rowL1 bb G.K ≤ δjunk * (ε * η)
  hfar : effC c G.P₀ A * ((2 : ℝ) ^ G.K *
      ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
          + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
        + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
            / ((apSample X G.P₀ G.b₀).card : ℝ))) ≤ δfar * (ε * η)
  /-- **the closed budget** -/
  hbudget : δ₁ + (δbig + δjunk + δfar) + 2 * (1 / (ε * η * Real.sqrt (D + 1)))
    + (((2 * D + 1) ^ G.rDim : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes R G.P₀) (Fintype.card G.Idx) R Mc
          (apSample X G.P₀ G.b₀).card lam' lam (freqSeed bb G.K) < 1

/-- **The residual obligation for `∑_n Ω(n)/bbⁿ`.** -/
theorem separatingFrameExistsW_weightU_of_witness (bb : ℕ) (hbb : 3 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb ((TWeight.weightU c hT).lambert bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessU c A bb ℓ w)) :
    SeparatingFrameExistsW bb ((TWeight.weightU c hT).lambert bb) := by
  have hbb2 : 2 ≤ bb := by omega
  intro a y ha hay hy hno
  obtain ⟨ℓ, w, hwℓ, hsub⟩ := exists_cylinder_subset bb hbb2 ha hay hy
  have homit : ∀ m, orbit bb ((TWeight.weightU c hT).lambert bb) m ∉
      Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ) :=
    fun m h => hno m (hsub h)
  obtain ⟨W⟩ := hw ℓ w hwℓ homit
  refine ⟨gridFrameW (TWeight.weightU c hT) bb hbb2 W.G W.X W.hne
      (smallPrimes W.R W.G.P₀) (frozenGammaC c bb W.G) W.hη W.hε W.D,
    W.δ₁, W.δbig + W.δjunk + W.δfar, _, _, _,
    gridFrameW_propA _ _ _ _ _ _ _ _ _ _ _,
    gridFrameW_propB_of_bound (TWeight.weightU c hT) bb hbb2 W.G W.X W.hne _ _ W.hη W.hε W.D hwℓ
      homit W.M W.hM W.hε1 W.hr W.hlog W.hδ₁ W.hB,
    gridFrameW_propC_gen (TWeight.weightU c hT) bb hbb2 W.G W.X W.hne _ _ W.hη W.hε (R := W.R)
      (fun p hp => (mem_smallPrimes.1 hp).1)
      (fun p hp => (mem_smallPrimes.1 hp).2.2)
      (by have := W.hR; omega)
      (fun p hp => (mem_smallPrimes.1 hp).2.1) W.hN W.hMc W.hlam' W.hlam,
    gridFrameW_weightU_propD_of_bounds c hT bb hbb W.G W.X W.R W.Y W.hne W.hP₀ W.hΩ W.hK W.hR
      W.hRY W.hMx1 W.hMx W.hDm W.hρm W.hη W.hε W.D W.hbig W.hjunk W.hfar,
    Frame.propJackson _,
    smallPrimeBound_nonneg _ _ _ _ _ (by linarith [W.hlam']) W.hlam, ?_⟩
  exact W.hbudget

/-- **The conditional headline for `w_c`.**  A schedule witness for every omitted base-`bb`
cylinder makes `∑_n w_c(n)/bbⁿ` disjunctive in base `bb ≥ 3`. -/
theorem isDisjunctive_weightU_of_witness (bb : ℕ) (hbb : 3 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb ((TWeight.weightU c hT).lambert bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessU c A bb ℓ w)) :
    IsDisjunctive bb ((TWeight.weightU c hT).lambert bb) :=
  isDisjunctive_of_framesW (separatingFrameExistsW_weightU_of_witness c hT bb hbb hw)

end NormalNumbers.G4
