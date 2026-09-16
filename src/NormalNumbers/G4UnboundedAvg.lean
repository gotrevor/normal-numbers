/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightJunkAvg
import NormalNumbers.G4UnboundedJunk

/-!
# Campaign B: the junk block average with no uniform bound on `c`

`G4WeightJunkAvg.junkAvgC_le` bounds the §4D valuation-junk average by
`(C · junkShiftBound P₀ X ρmax / |P|) · rowL1`.  Its proof touches `C` in exactly one place —
`sum_junk_C_le` — so replacing that by `G4UnboundedJunk.sum_junk_C_le'` gives the same bound
with `C · junkShiftBound` replaced by the `C`-free `junkShiftBoundC`, and **no hypothesis on
`c` at all**.

This is the second of the two `C`-sites of `isDisjunctive_weight` reduced to an explicit
arithmetic quantity; the third (the far field's `w_c ≤ (max C 1)·Ω`) is B2.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **The valuation-junk block average for `w_c`, with no bound on `c`.**  The `C`-free form of
`junkAvgC_le`: the whole `c`-dependence is the explicit arithmetic quantity
`junkShiftBoundC c P₀ X ρmax`. -/
theorem junkAvgC_le' (c : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax) :
    junkAvgC c bb G X
      ≤ (junkShiftBoundC c G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ))
          * rowL1 bb G.K := by
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set B : ℝ := junkShiftBoundC c G.P₀ X ρmax / (P.card : ℝ) with hBdef
  have hB0 : 0 ≤ B := div_nonneg (junkShiftBoundC_nonneg _ _ _ _) hc.le
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
    have := sum_junk_C_le' c (b₀ := G.b₀) (X := X) hP₀ (shiftAL_pos G i) (hρm i)
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

/-! ### B2: the far-field weight sum without `κ = max C 1`

`G4WeightJunkAvg.sum_abs_farPartC_le` prices the far tail through the pointwise domination
`w_c ≤ (max C 1)·Ω`, which has no unbounded analogue (`max_{p²∣m} c_p` grows with `m`).  The
replacement is the §4D split itself — the route `sum_cardFactors_shiftG_le` already takes for
`Ω`: `w_c = ω + frozenExcess_c + junk_c`, where the frozen part is bounded by the **constant**
`frozenCap c P₀ = ∑_{p∣P₀} c_p·v_p(P₀)` (it only sees `m mod P₀`) and the junk part by
`junkShiftBoundC`. -/

/-- The frozen cap `∑_{p∣P₀} c_p · v_p(P₀)` — the `c`-weighted analogue of `Ω(P₀)`. -/
noncomputable def frozenCap (c : ℕ → ℕ) (P₀ : ℕ) : ℝ :=
  ∑ p ∈ P₀.primeFactors, (c p : ℝ) * ((P₀.factorization p : ℕ) : ℝ)

lemma frozenCap_nonneg (c : ℕ → ℕ) (P₀ : ℕ) : 0 ≤ frozenCap c P₀ :=
  Finset.sum_nonneg fun p _ => by positivity

/-- The frozen excess never exceeds the cap: it only sees `min(v_p(m), v_p(P₀))`. -/
lemma frozenExcess_le_frozenCap (c : ℕ → ℕ) {P₀ : ℕ} (m : ℕ) :
    frozenExcess c P₀ m ≤ frozenCap c P₀ := by
  unfold frozenExcess frozenCap
  refine Finset.sum_le_sum fun p _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h : (min (m.factorization p) (P₀.factorization p) - 1 : ℕ) ≤ P₀.factorization p := by omega
  exact_mod_cast h

/-- **The far-field sample sum of `w_c`, with no bound on `c`.**  The `C`-free analogue of the
`κ · sum_cardFactors_shiftG_le` step inside `sum_abs_farPartC_le`. -/
theorem sum_weightW_shiftG_le (c : ℕ → ℕ) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (α : G.Atom) {j : ℕ} (hj : 1 ≤ j) :
    ∑ n ∈ apSample X G.P₀ G.b₀, weightW c (n + shiftG G.B G.Q G.D₀ α j)
      ≤ (apSample X G.P₀ G.b₀).card
            * ((farC G X Dm + 2 * j) / Real.log 2 + frozenCap c G.P₀)
          + junkShiftBoundC c G.P₀ X (j * Dm) := by
  classical
  set P := apSample X G.P₀ G.b₀ with hP
  set ρ := shiftG G.B G.Q G.D₀ α j with hρ
  have hρ1 : 1 ≤ ρ := shiftG_pos G α hj
  have hρle : ρ ≤ j * Dm := by
    rw [hρ]; unfold shiftG
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left j (hDm α))
  have hP₀' : G.P₀ ≠ 0 := hP₀.ne'
  have hpt : ∀ n, weightW c (n + ρ)
      = omegaR (n + ρ) + frozenExcess c G.P₀ (n + ρ) + junk c G.P₀ (n + ρ) := by
    intro n
    unfold weightW
    rw [excess_eq_frozen_add_junk c hP₀' (show n + ρ ≠ 0 by omega)]
    ring
  calc ∑ n ∈ P, weightW c (n + ρ)
      = ∑ n ∈ P, omegaR (n + ρ) + ∑ n ∈ P, frozenExcess c G.P₀ (n + ρ)
          + ∑ n ∈ P, junk c G.P₀ (n + ρ) := by
        simp_rw [hpt]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (P.card * ((farC G X Dm + 2 * j) / Real.log 2)
          + P.card * frozenCap c G.P₀) + junkShiftBoundC c G.P₀ X (j * Dm) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · rw [hP, hρ]
          exact sum_omegaR_shiftG_le G X hne hDm α hj
        · calc ∑ n ∈ P, frozenExcess c G.P₀ (n + ρ)
              ≤ ∑ _n ∈ P, frozenCap c G.P₀ :=
                Finset.sum_le_sum fun n _ => frozenExcess_le_frozenCap c _
            _ = P.card * frozenCap c G.P₀ := by rw [Finset.sum_const, nsmul_eq_mul]
        · rw [hP]
          exact sum_junk_C_le' c hP₀ hρ1 hρle
    _ = _ := by ring

end NormalNumbers.G4
