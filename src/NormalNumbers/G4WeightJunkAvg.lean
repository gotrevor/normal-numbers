/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightRemainder
import NormalNumbers.G4OmegaJunk

/-!
# The three §4D estimates for `w_c`

The `Ω` estimates of `G4OmegaJunk` at a general bounded coefficient vector `c ≤ C`.  Writing
`κ = max C 1`:

* `bigAvgC = bigAvg` — the large-prime block never sees the weight;
* `junkAvgC ≤ C · (junkShiftBound / |P|) · rowL1` — one factor `C` from
  `G4WeightJunk.sum_junk_le`;
* `farAvgC ≤ κ · (the Ω far bound)` — from the pointwise domination
  `w_c(m) ≤ κ · Ω(m)` (`weightW_le_kappa_mul_cardFactors`).

So the whole `C`-dependence of §4D is a single factor `κ` in front of the `Ω` budget, which the
schedule pays by enlarging `K` (the deltas are fixed fractions of `ε·η = 2^{-k₄}/K`).
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C)

include hC

/-- **Pointwise domination**: `w_c(m) ≤ max(C,1) · Ω(m)`. -/
theorem weightW_le_kappa_mul_cardFactors (m : ℕ) :
    weightW c m ≤ ((max C 1 : ℕ) : ℝ) * ((Ω m : ℕ) : ℝ) := by
  have hN : m.primeFactors.card ≤ Ω m := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
      Nat.support_factorization]
    calc m.primeFactors.card = ∑ _p ∈ m.primeFactors, 1 := by simp
      _ ≤ ∑ p ∈ m.primeFactors, m.factorization p := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := Nat.mem_primeFactors.1 hp
          exact hp'.1.factorization_pos_of_dvd hp'.2.2 hp'.2.1
  have homega : omegaR m ≤ ((Ω m : ℕ) : ℝ) := by
    rw [omegaR_eq]
    exact_mod_cast hN
  have hex : excess c m ≤ (C : ℝ) * (((Ω m : ℕ) : ℝ) - omegaR m) :=
    excess_le (C := (C : ℝ)) (fun p => by exact_mod_cast hC p) m
  have hCk : (C : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left C 1
  have h1k : (1 : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right C 1
  have hdiff : (0 : ℝ) ≤ ((Ω m : ℕ) : ℝ) - omegaR m := by linarith
  have hom0 : (0 : ℝ) ≤ omegaR m := omegaR_nonneg m
  unfold weightW
  nlinarith

/-! ### `junkAvgC` -/

/-- The sample sum of the `c`-junk at any shift `1 ≤ ρ ≤ ρmax`. -/
theorem sum_junk_C_le {X P₀ b₀ ρ ρmax : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) (hρm : ρ ≤ ρmax) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ) ≤ (C : ℝ) * junkShiftBound P₀ X ρmax := by
  have h := sum_junk_le c (C := (C : ℝ)) (fun p => by exact_mod_cast hC p)
    (X := X) (b₀ := b₀) hP₀ hρ
  refine h.trans ?_
  unfold junkShiftBound
  have hmono : ((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ)
      ≤ ((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) :=
    Nat.mul_le_mul (by
        have := Nat.sqrt_le_sqrt (show X + ρ ≤ X + ρmax by omega)
        omega)
      (Nat.log_mono_right (by omega))
  have hm : (((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ) : ℝ)
      ≤ (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) := by exact_mod_cast hmono
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  nlinarith

/-- **The valuation-junk block average for `w_c`.** -/
theorem junkAvgC_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax) :
    junkAvgC c bb G X
      ≤ ((C : ℝ) * junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ))
          * rowL1 bb G.K := by
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set B : ℝ := (C : ℝ) * junkShiftBound G.P₀ X ρmax / (P.card : ℝ) with hBdef
  have hB0 : 0 ≤ B :=
    div_nonneg (mul_nonneg hC0 (junkShiftBound_nonneg _ _ _)) hc.le
  have hjunk0 : ∀ m : ℕ, 0 ≤ junk c G.P₀ m := by
    intro m
    unfold junk
    exact Finset.sum_nonneg fun p _ => by positivity
  have hshift : ∀ i : G.Idx, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |junk c G.P₀ (n + shiftAL G.B G.Q G.D₀ i)| ≤ B := by
    intro i
    have habs : ∑ n ∈ P, |junk c G.P₀ (n + shiftAL G.B G.Q G.D₀ i)|
        = ∑ n ∈ P, junk c G.P₀ (n + shiftAL G.B G.Q G.D₀ i) :=
      Finset.sum_congr rfl fun n _ => abs_of_nonneg (hjunk0 _)
    rw [habs, hP]
    have := sum_junk_C_le c C hC (b₀ := G.b₀) (X := X) hP₀ (shiftAL_pos G i) (hρm i)
    rw [hBdef, ← hP, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hrow : ∀ ν : Fin G.rDim, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
      ≤ B * rowL1 bb G.K := fun ν =>
    sampleAvg_abs_blockSum_le_of_shift bb hbb G X hB0 _ (G.rowEquiv.symm ν) hshift
  unfold junkAvgC
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ (mul_nonneg hB0 (rowL1_nonneg hbr G.K)) fun ν _ => hrow ν

/-! ### `bigAvgC`: the `ω` estimate verbatim -/

omit hC in
lemma bigAvgC_eq_bigAvg (bb : ℕ) (G : GridParams) (X R : ℕ) :
    bigAvgC bb G X R = bigAvg bb G X R := rfl

omit hC in
theorem bigAvgC_le' (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvgC bb G X R
      ≤ Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
  rw [bigAvgC_eq_bigAvg]
  exact bigAvg_le' bb hbb G X R Y hne hK hR hRY hMx1 hMx

end NormalNumbers.G4
