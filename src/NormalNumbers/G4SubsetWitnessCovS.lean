/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetWitnessCov
import NormalNumbers.G4FarTailS

/-!
# The covariance-form schedule witness with the `S`-restricted far tail

`ScheduleWitnessSCS` is `ScheduleWitnessSC` with `hfar` stated through `farCS` (the far-tail
constant whose harmonic part is the `S`-mass `F_S(X+Dm)` rather than `log log(X+Dm)`,
`G4FarTailS`).  Every other field is unchanged; in particular `R`, `Y` and the moment order `Mc`
are free fields, so the decoupled frame `SchedB.Dec.HypE2` can fill it.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (S : ℕ → Prop) [DecidablePred S]

theorem gridFrameW_subset_propD_of_covS (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y)
    {V κ : ℝ} (hV : 0 ≤ V) (hκ : 0 ≤ κ) (hcov : VeryLargeCov S G X Y V κ)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δfar : ℝ}
    (hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + Real.sqrt (rowL2 bb G.K * V + rowL1 bb G.K ^ 2 * κ) ≤ δbig * (ε * η))
    (hfar : (2 : ℝ) ^ G.K / Real.log 2 * farBound bb (G.K + G.N) (farCS S G X Dm)
        ≤ δfar * (ε * η)) :
    (gridFrameW (TWeight.subset S) bb hbb G X hne ((smallPrimes R G.P₀).filter S)
      (frozenGammaS S bb G) hη hε D).PropD (δbig + δfar) := by
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  refine gridFrameW_subset_propD S bb hbb G X hne R hη hε D
    ((bigAvgS_le_of_cov S bb hbb G X R Y hne hK hRY hV hκ hcov).trans (le_trans ?_ hbig))
    ((farAvgS_leS S bb hbb G X hne hDm).trans hfar)
  gcongr
  unfold medBudget
  have hcard : ((medPrimes R Y G.P₀).card : ℝ) ≤ Y := by exact_mod_cast card_medPrimes_le R Y G.P₀
  have h1 := sum_inv_medPrimes_le (P₀ := G.P₀) hR hRY
  have h2 := rowL2_nonneg hbr G.K
  have h3 := rowL1_nonneg hbr G.K
  have h4 : (0 : ℝ) ≤ ((medPrimes R Y G.P₀).card : ℝ) := by positivity
  gcongr

/-- **The schedule witness with the covariance interface.** -/
structure ScheduleWitnessSCS (bb ℓ w : ℕ) where
  G : GridParams
  hK : 0 < G.K
  hr : 1 ≤ G.rDim
  X : ℕ
  hne : (apSample X G.P₀ G.b₀).Nonempty
  η : ℝ
  hη : 0 < η
  ε : ℝ
  hε : 0 < ε
  hε1 : ε < 1
  M : ℕ
  hM : 1 / ((bb : ℝ) ^ ℓ) ^ M ≤ η
  Lg : ℝ
  hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg
  δ₁ : ℝ
  hδ₁ : 0 ≤ δ₁
  hB : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
    (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
      * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
      ≤ δ₁ / 2 ^ G.rDim
  R : ℕ
  hR : 2 ≤ R
  Y : ℕ
  hRY : R ≤ Y
  D : ℕ
  hN : 1 + Nat.clog bb (2 ^ G.K * D) ≤ G.N
  Mc : ℕ
  hMc : 1 ≤ Mc
  lam' : ℝ
  hlam' : 1 ≤ lam'
  lam : ℝ
  hlam : 0 < lam
  /-- **the very-large covariance bound** -/
  V : ℝ
  κ : ℝ
  hV : 0 ≤ V
  hκ : 0 ≤ κ
  hcov : VeryLargeCov S G X Y V κ
  Dm : ℕ
  hDm : ∀ α, G.d α ≤ Dm
  δbig : ℝ
  δfar : ℝ
  hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
        + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
      + Real.sqrt (rowL2 bb G.K * V + rowL1 bb G.K ^ 2 * κ) ≤ δbig * (ε * η)
  hfar : (2 : ℝ) ^ G.K / Real.log 2 * farBound bb (G.K + G.N) (farCS S G X Dm) ≤ δfar * (ε * η)
  hbudget : δ₁ + (δbig + δfar) + 2 * (1 / (ε * η * Real.sqrt (D + 1)))
    + (((2 * D + 1) ^ G.rDim : ℕ) : ℝ)
      * smallPrimeBound ((smallPrimes R G.P₀).filter S) (Fintype.card G.Idx) R Mc
          (apSample X G.P₀ G.b₀).card lam' lam (freqSeed bb G.K) < 1

theorem separatingFrameExistsW_subset_of_witnessCS (bb : ℕ) (hbb : 2 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb (subsetLambert S bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessSCS S bb ℓ w)) :
    SeparatingFrameExistsW bb (subsetLambert S bb) := by
  intro a c ha hac hc hno
  obtain ⟨ℓ, w, hwℓ, hsub⟩ := exists_cylinder_subset bb hbb ha hac hc
  have homit : ∀ m, orbit bb (subsetLambert S bb) m ∉
      Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ) :=
    fun m h => hno m (hsub h)
  have hlam : (TWeight.subset S).lambert bb = subsetLambert S bb := TWeight.lambert_subset S
  obtain ⟨W⟩ := hw ℓ w hwℓ homit
  refine ⟨gridFrameW (TWeight.subset S) bb hbb W.G W.X W.hne
      ((smallPrimes W.R W.G.P₀).filter S) (frozenGammaS S bb W.G) W.hη W.hε W.D,
    W.δ₁, W.δbig + W.δfar, _, _, _,
    gridFrameW_propA _ _ _ _ _ _ _ _ _ _ _,
    gridFrameW_propB_of_bound (TWeight.subset S) bb hbb W.G W.X W.hne _ _ W.hη W.hε W.D hwℓ
      (by rw [hlam]; exact homit) W.M W.hM W.hε1 W.hr W.hlog W.hδ₁ W.hB,
    gridFrameW_propC_gen (TWeight.subset S) bb hbb W.G W.X W.hne _ _ W.hη W.hε (R := W.R)
      (fun p hp => (mem_smallPrimes.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (mem_smallPrimes.1 (Finset.mem_filter.1 hp).1).2.2)
      (by have := W.hR; omega)
      (fun p hp => (mem_smallPrimes.1 (Finset.mem_filter.1 hp).1).2.1) W.hN W.hMc W.hlam'
      W.hlam,
    gridFrameW_subset_propD_of_covS S bb hbb W.G W.X W.R W.Y W.hne W.hK W.hR W.hRY W.hV W.hκ
      W.hcov W.hDm W.hη W.hε W.D W.hbig W.hfar,
    Frame.propJackson _,
    smallPrimeBound_nonneg _ _ _ _ _ (by linarith [W.hlam']) W.hlam, ?_⟩
  exact W.hbudget

/-- **Conditional headline, covariance form.** -/
theorem isDisjunctive_subsetLambert_of_witnessCS (bb : ℕ) (hbb : 2 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb (subsetLambert S bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessSCS S bb ℓ w)) :
    IsDisjunctive bb (subsetLambert S bb) :=
  isDisjunctive_of_framesW (separatingFrameExistsW_subset_of_witnessCS S bb hbb hw)

end NormalNumbers.G4
