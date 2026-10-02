/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureTTEquidistributed
import NormalNumbers.C3MrtTTDefect

/-!
# `TTEquidistributedCorrelation` is vacuous (found 2026-10-02, Erdős #257 base-2 lap 1)

The frozen transcription of Tao–Teräväinen Theorem 3.1(i) (`LiteratureTTEquidistributed.lean`)
repeats the defect already recorded for case (ii) on 2026-09-25 (`C3MrtTTDefect` §3, Maze row
"Lebesgue-measured exceptional set of scales"): the exceptional set `E ⊆ ℝ` is charged by
`∫_E t⁻¹`, but the conclusion is asked only at **natural** scales `N`.  The naturals in
`[√X, X]` form a null set, so `E` may exclude every scale for free.

* `ttEquidistributedCorrelation_trivially_true` — the `Prop` is a theorem, so it carries no
  information.  In particular the base-2 route's step N6 (`VeryLargeCov` from TT, audit §4) cannot
  be derived from it, and the frozen headline `Erdos257.isDisjunctive_subsetLambert_two`, being
  conditional on a true `Prop`, is as strong as the *unconditional* base-2 disjunctivity of
  `∑_{p∈S} 1/(2ᵖ−1)` (new even for `S` = all primes).
* `TTEquidistributedDyadic` — the faithful repair, mirroring `TwoPointDyadicCorrelation`: a
  **counted** set of exceptional dyadic scales.  Guard: `full_exceptional_set_not_admissible`
  applies verbatim.
-/

open MeasureTheory

namespace NormalNumbers.CastingOut

/-- **The frozen case-(i) input is provably true** (hence empty): take `E` to be the naturals in
`[√X, X]`, a countable, hence null, set. -/
theorem ttEquidistributedCorrelation_trivially_true : TTEquidistributedCorrelation := by
  refine ⟨1, 1, one_pos, one_pos, fun g₁ g₂ _ _ _ _ _ X L hX hL1 hLX δ _ _ => ?_⟩
  refine ⟨Set.range (fun n : ℕ => (n : ℝ)) ∩ Set.Icc (Real.sqrt X) X, ?_,
    Set.inter_subset_right, ?_, ?_⟩
  · exact ((Set.countable_range _).mono Set.inter_subset_left).measurableSet
  · have hzero : volume (Set.range (fun n : ℕ => (n : ℝ)) ∩ Set.Icc (Real.sqrt X) X) = 0 :=
      ((Set.countable_range _).mono Set.inter_subset_left).measure_zero volume
    rw [MeasureTheory.setIntegral_measure_zero _ hzero]
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have : (0 : ℝ) ≤ L ^ (-(1 : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  · intro N hN1 hN2 hNE
    exact absurd (Set.mem_inter (Set.mem_range_self (f := fun n : ℕ => (n : ℝ)) N)
      (Set.mem_Icc.mpr ⟨hN1, hN2⟩)) hNE

/-- **Theorem 3.1(i), with the exceptional scales counted** (the repair; not yet consumed).
Same hypotheses as `TTEquidistributedCorrelation`; the exceptional set is a `Finset` of dyadic
exponents of `[√X, X]` holding at most a fraction `Cst · L^{-c}` of them, and the conclusion
holds at every natural `N ∈ [2^j, 2^{j+1})` of every non-exceptional scale `j`.  Unverified
against the paper beyond the case-(ii) precedent: TT measure `E` by logarithmic density, which
for a union of dyadic blocks is this count up to a constant. -/
def TTEquidistributedDyadic : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → ∀ δ : ℝ → ℝ,
        (∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖(∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), g₁ n)
              - (((N / q) * δ N : ℝ) : ℂ)‖ ≤ N / L) →
        (∀ p : ℕ, p.Prime → Real.exp (Real.log X ^ ((1 : ℝ) / 11)) ≤ p →
          (p : ℝ) ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 10)) → g₁ p = 1) →
        ∃ E : Finset ℕ, E ⊆ dyadicScales X ∧
          (E.card : ℝ) ≤ Cst * L ^ (-c) * ((dyadicScales X).card : ℝ) ∧
          ∀ j ∈ dyadicScales X, j ∉ E →
            ∀ N : ℕ, (2 : ℝ) ^ j ≤ (N : ℝ) → (N : ℝ) < 2 ^ (j + 1) →
              ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
                (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
                ‖((W : ℝ) / (N : ℝ) : ℝ) •
                    ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                      (g₁ (n + h₁) - ((δ N : ℝ) : ℂ)) * g₂ (n + h₂)‖
                  ≤ Cst * L ^ (-c)

end NormalNumbers.CastingOut
