/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaRemainder
import NormalNumbers.G4MediumPrimes
import NormalNumbers.G4FarTail

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
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hc : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hstep : ∀ n ∈ apSample X G.P₀ G.b₀, |blockSum bb G w n a|
      ≤ ∑ i : G.Idx, |rowCoeff bb G a i| * |w (n + shiftAL G.B G.Q G.D₀ i)| := by
    intro n _
    rw [blockSum_eq_sum_rowCoeff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
        ∑ n ∈ apSample X G.P₀ G.b₀, |blockSum bb G w n a|
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
          ∑ i : G.Idx, |rowCoeff bb G a i| * |w (n + shiftAL G.B G.Q G.D₀ i)| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hc
    _ = ∑ i : G.Idx, |rowCoeff bb G a i| * (((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
          ∑ n ∈ apSample X G.P₀ G.b₀, |w (n + shiftAL G.B G.Q G.D₀ i)|) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        ring
    _ ≤ ∑ i : G.Idx, |rowCoeff bb G a i| * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
    _ = (∑ i : G.Idx, |rowCoeff bb G a i|) * B := by rw [Finset.sum_mul]
    _ ≤ rowL1 bb G.K * B := mul_le_mul_of_nonneg_right (sum_abs_rowCoeff_le bb hbb G a) hB
    _ = B * rowL1 bb G.K := mul_comm _ _

/-! ### The junk at a single shift -/

/-- The closed bound of `sum_junk_le` at `c ≡ 1`, with the shift replaced by a uniform cap. -/
noncomputable def junkShiftBound (P₀ X ρmax : ℕ) : ℝ :=
  (X : ℝ) / P₀ * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)
    + (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ)

lemma junkShiftBound_nonneg (P₀ X ρmax : ℕ) : 0 ≤ junkShiftBound P₀ X ρmax := by
  unfold junkShiftBound
  have h1 : (0 : ℝ) ≤ ∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  positivity

/-- The sample sum of the valuation junk at any shift `1 ≤ ρ ≤ ρmax`. -/
theorem sum_junk_one_le {X P₀ b₀ ρ ρmax : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) (hρm : ρ ≤ ρmax) :
    ∑ n ∈ apSample X P₀ b₀, junk (fun _ => (1 : ℕ)) P₀ (n + ρ) ≤ junkShiftBound P₀ X ρmax := by
  have h := sum_junk_le (fun _ => (1 : ℕ)) (C := 1) (fun _ => by norm_num) (X := X) (b₀ := b₀) hP₀ hρ
  refine h.trans ?_
  rw [one_mul]
  unfold junkShiftBound
  have hmono : ((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ)
      ≤ ((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) :=
    Nat.mul_le_mul (by
        have := Nat.sqrt_le_sqrt (show X + ρ ≤ X + ρmax by omega)
        omega)
      (Nat.log_mono_right (by omega))
  have : (((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ) : ℝ)
      ≤ (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) := by exact_mod_cast hmono
  linarith

/-! ### `junkAvgΩ` -/

/-- **The valuation-junk block average.** -/
theorem junkAvgΩ_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax) :
    junkAvgΩ bb G X
      ≤ (junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ)) * rowL1 bb G.K := by
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set B : ℝ := junkShiftBound G.P₀ X ρmax / (P.card : ℝ) with hBdef
  have hB0 : 0 ≤ B := div_nonneg (junkShiftBound_nonneg _ _ _) hc.le
  have hjunk0 : ∀ m : ℕ, 0 ≤ junk (fun _ => (1 : ℕ)) G.P₀ m := by
    intro m
    unfold junk
    exact Finset.sum_nonneg fun p _ => by positivity
  have hshift : ∀ i : G.Idx, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |junk (fun _ => (1 : ℕ)) G.P₀ (n + shiftAL G.B G.Q G.D₀ i)| ≤ B := by
    intro i
    have habs : ∑ n ∈ P, |junk (fun _ => (1 : ℕ)) G.P₀ (n + shiftAL G.B G.Q G.D₀ i)|
        = ∑ n ∈ P, junk (fun _ => (1 : ℕ)) G.P₀ (n + shiftAL G.B G.Q G.D₀ i) :=
      Finset.sum_congr rfl fun n _ => abs_of_nonneg (hjunk0 _)
    rw [habs, hP]
    have := sum_junk_one_le (b₀ := G.b₀) (X := X) hP₀ (shiftAL_pos G i) (hρm i)
    rw [hBdef, ← hP, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hrow : ∀ ν : Fin G.rDim, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
      ≤ B * rowL1 bb G.K := fun ν =>
    sampleAvg_abs_blockSum_le_of_shift bb hbb G X hB0 _ (G.rowEquiv.symm ν) hshift
  unfold junkAvgΩ
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ (mul_nonneg hB0 (rowL1_nonneg hbr G.K)) fun ν _ => hrow ν

/-! ### `bigAvgΩ`: literally the `ω` estimate -/

lemma bigAvgΩ_eq_bigAvg (bb : ℕ) (G : GridParams) (X R : ℕ) :
    bigAvgΩ bb G X R = bigAvg bb G X R := rfl

/-- **`bigAvgΩ` in closed form** — the same RHS as `bigAvg_le'`: the large-prime block of `Ω`
*is* the large-prime block of `ω` (the valuation excess was split off into the junk). -/
theorem bigAvgΩ_le' (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvgΩ bb G X R
      ≤ Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
  rw [bigAvgΩ_eq_bigAvg]
  exact bigAvg_le' bb hbb G X R Y hne hK hR hRY hMx1 hMx

/-! ### The AP-mean of `Ω` — the far-tail input

`Ω` is **not** controlled by `log d(m)` (the inequality `2^{Ω} ≥ d` goes the wrong way), and the
pointwise bound `Ω(m) ≤ log₂ m` costs a `log X` the schedule cannot pay.  The working route is the
same split as §4D: `Ω = ω + frozenExcess + junk`, where the frozen part is bounded by `Ω(P₀)` and
the junk by `junkShiftBound`. -/

/-- The frozen excess at `c ≡ 1` never exceeds `Ω(P₀)`. -/
lemma frozenExcess_one_le {P₀ : ℕ} (hP₀ : P₀ ≠ 0) (m : ℕ) :
    frozenExcess (fun _ => (1 : ℕ)) P₀ m ≤ ((ArithmeticFunction.cardFactors P₀ : ℕ) : ℝ) := by
  sorry

/-- **The AP-mean of `Ω` at layer `j`** — the `ω` bound plus the two `Ω`-specific costs. -/
theorem sum_cardFactors_shiftG_le (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (α : G.Atom) {j : ℕ} (hj : 1 ≤ j) :
    ∑ n ∈ apSample X G.P₀ G.b₀,
        ((ArithmeticFunction.cardFactors (n + shiftG G.B G.Q G.D₀ α j) : ℕ) : ℝ)
      ≤ (apSample X G.P₀ G.b₀).card *
            ((farC G X Dm + 2 * j) / Real.log 2
              + ((ArithmeticFunction.cardFactors G.P₀ : ℕ) : ℝ))
          + junkShiftBound G.P₀ X (j * Dm) := by
  sorry

end NormalNumbers.G4
