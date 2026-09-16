/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleWitness
import NormalNumbers.G4SubsetJunk

/-!
# The §5 schedule interface for the prime-subset constant `c_S(bb) = ∑_n ω_S(n)/bbⁿ`

`ScheduleWitnessS S bb ℓ w` is `ScheduleWitnessB` with exactly one field changed: the small
primes carried by the vector `S` are the *`S`-filtered* ones, so the budget's `δ₃` is
`smallPrimeBound ((smallPrimes R P₀).filter S) …`.  Everything else — B, D-big, D-far and the
Jackson/budget arithmetic — is character for character the same, because §4C is stated for an
arbitrary finset of primes and the §4D junk of `ω_S` is dominated by that of `ω`
(`G4SubsetJunk`).

`separatingFrameExistsW_subset_of_witness` and `isDisjunctive_subsetLambert_of_witness` are the
conditional headline of campaign A: divergence of `∑_{p ∈ S} 1/p` (in the *rate* form of
`G4MertensAP.MertensRate`, see `DESIGN-2026-09-16-prime-subset.md`) enters only through the
contraction factor `exp(−4θ₀ ∑_{p ∈ sm} 1/p)` inside `smallPrimeBound`, i.e. only through the
last field `hbudget`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (S : ℕ → Prop) [DecidablePred S]

/-- **What §5 must supply for the prime-subset constant** at the omitted cylinder. -/
structure ScheduleWitnessS (bb ℓ w : ℕ) where
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
  δbig : ℝ
  δfar : ℝ
  hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
        + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
      + (Real.log Mx / Real.log Y) * rowL1 bb G.K ≤ δbig * (ε * η)
  hfar : (2 : ℝ) ^ G.K / Real.log 2 * farBound bb (G.K + G.N) (farC G X Dm) ≤ δfar * (ε * η)
  /-- **the closed budget**, with the `S`-restricted small primes -/
  hbudget : δ₁ + (δbig + δfar) + 2 * (1 / (ε * η * Real.sqrt (D + 1)))
    + (((2 * D + 1) ^ G.rDim : ℕ) : ℝ)
      * smallPrimeBound ((smallPrimes R G.P₀).filter S) (Fintype.card G.Idx) R Mc
          (apSample X G.P₀ G.b₀).card lam' lam (freqSeed bb G.K) < 1

/-- **The residual obligation for the prime-subset constant.** -/
theorem separatingFrameExistsW_subset_of_witness (bb : ℕ) (hbb : 2 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb (subsetLambert S bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessS S bb ℓ w)) :
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
    gridFrameW_subset_propD_of_bounds S bb hbb W.G W.X W.R W.Y W.hne W.hK W.hR W.hRY W.hMx1
      W.hMx W.hDm W.hη W.hε W.D W.hbig W.hfar,
    Frame.propJackson _,
    smallPrimeBound_nonneg _ _ _ _ _ (by linarith [W.hlam']) W.hlam, ?_⟩
  exact W.hbudget

/-- **The conditional headline of campaign A.**  A schedule witness for every omitted base-`bb`
cylinder makes `c_S(bb) = ∑_n ω_S(n)/bbⁿ = ∑_{p ∈ S} 1/(b^p − 1)` disjunctive in base `bb`. -/
theorem isDisjunctive_subsetLambert_of_witness (bb : ℕ) (hbb : 2 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb (subsetLambert S bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessS S bb ℓ w)) :
    IsDisjunctive bb (subsetLambert S bb) :=
  isDisjunctive_of_framesW (separatingFrameExistsW_subset_of_witness S bb hbb hw)

end NormalNumbers.G4
