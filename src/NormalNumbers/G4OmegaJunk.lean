/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaRemainder
import NormalNumbers.G4MediumPrimes

/-!
# `junkAvgΩ` — the one genuinely new §4D estimate for `Ω`

`Ω`'s retained tail carries one term the `ω`-route does not have: the **valuation junk**
`junk 1 P₀ (m) = ∑_{p} (v_p(m) − v_p(P₀))⁺` restricted to the excess above the frozen depth.
`G4WeightJunk.sum_junk_le` bounds its *sample sum* at a single shift `ρ`; this file pushes that
through a layer block.

The mechanism is the ℓ¹ row budget, applied in the `n`-averaged (not pointwise) form: the junk is
nonnegative, so

  `card⁻¹ ∑_n |blockSum bb G junk n a| ≤ ∑_i |c_i| · (card⁻¹ ∑_n junk(n+ρ_i)) ≤ B · rowL1 bb K`

whenever every shift obeys `card⁻¹ ∑_n junk(n+ρ_i) ≤ B`.  `sampleAvg_abs_blockSum_le_of_shift`
is that step for an arbitrary weight, and `junkAvgΩ_le` is the instance.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-! ### A layer block as a row-coefficient sum -/

/-- `blockSum bb G w n a = ∑_i c_i · w(n + ρ_i)` — the `w`-generic form of the identity
inside `blockSum_omegaOn_eq`. -/
lemma blockSum_eq_sum_rowCoeff (bb : ℕ) (G : GridParams) (w : ℕ → ℝ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G w n a = ∑ i : G.Idx, rowCoeff bb G a i * w (n + shiftAL G.B G.Q G.D₀ i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun jj _ => ?_
  unfold rowCoeff
  ring

/-- **The `n`-averaged ℓ¹ row budget.**  If every shift's sample average of `|w|` is at most `B`,
the sample average of the block is at most `B · rowL1`. -/
theorem sampleAvg_abs_blockSum_le_of_shift (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (w : ℕ → ℝ) (a : Fin G.K → Fin G.s)
    (hw : ∀ i : G.Idx, ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
      ∑ n ∈ apSample X G.P₀ G.b₀, |w (n + shiftAL G.B G.Q G.D₀ i)| ≤ B) :
    ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
        ∑ n ∈ apSample X G.P₀ G.b₀, |blockSum bb G w n a| ≤ B * rowL1 bb G.K := by
  sorry

/-! ### The junk at a single shift -/

/-- The closed bound of `sum_junk_le` at `c ≡ 1`, with the shift replaced by a uniform cap. -/
noncomputable def junkShiftBound (P₀ X ρmax : ℕ) : ℝ :=
  (X : ℝ) / P₀ * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)
    + (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ)

lemma junkShiftBound_nonneg (P₀ X ρmax : ℕ) : 0 ≤ junkShiftBound P₀ X ρmax := by
  sorry

/-- The sample sum of the valuation junk at any shift `1 ≤ ρ ≤ ρmax`. -/
theorem sum_junk_one_le {X P₀ b₀ ρ ρmax : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) (hρm : ρ ≤ ρmax) :
    ∑ n ∈ apSample X P₀ b₀, junk (fun _ => (1 : ℕ)) P₀ (n + ρ) ≤ junkShiftBound P₀ X ρmax := by
  sorry

/-! ### `junkAvgΩ` -/

/-- **The valuation-junk block average.** -/
theorem junkAvgΩ_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax) :
    junkAvgΩ bb G X
      ≤ (junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ)) * rowL1 bb G.K := by
  sorry

end NormalNumbers.G4
