import NormalNumbers.PrimeModelKMT
import NormalNumbers.PrimeModelDensityMass

/-!
# Prime model, Part II-b: the family theorem

`papers/prime-model-assembly-2026-09-22.md`, Part II.

**Theorem.**  If `P` is a set of primes with `π_P(x) · log log x ≤ π(x)` eventually (`Sparse P`)
and `∑_{p∈P} 1/p = ∞` (`DivergentRecip P`), then `IsNormal 4 (subsetLambert P 4)`.

Schedule, built from the **actual accumulated mass** `S = recipSumLe P y_N`:

    ε_N = 2 / log log N,   y_N = ⌊N^{ε_N}⌋₊,   J_N = min(⌊log log log N / 24⌋₊, ⌊S/8⌋₊).

The four terms of `KMT_quant₂ C₁ C₂` (Part I) at `(k, x, ε) = (J_N, N, ε_N)`, and the L¹ tail
`(recipSumLe P (2N) + 5J_N + 12)/4^{J_N}` (`tail_error_L1`), all tend to `0`; the wiring theorem
`isNormal_subsetLambert_of_KMT_along` then gives normality.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.Family

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra

variable (P : ℕ → Prop) [DecidablePred P]

/-- `log log N`. -/
noncomputable def L2 (N : ℕ) : ℝ := Real.log (Real.log N)

/-- `log log log N`. -/
noncomputable def L3 (N : ℕ) : ℝ := Real.log (Real.log (Real.log N))

/-- `ε_N = 2 / log log N`. -/
noncomputable def epsN (N : ℕ) : ℝ := 2 / L2 N

/-- `y_N = ⌊N^{ε_N}⌋₊`. -/
noncomputable def yN (N : ℕ) : ℕ := ⌊(N : ℝ) ^ epsN N⌋₊

/-- `J_N = min(⌊L₃ N / 24⌋₊, ⌊recipSumLe P y_N / 8⌋₊)`. -/
noncomputable def JN (N : ℕ) : ℕ :=
  min ⌊L3 N / 24⌋₊ ⌊recipSumLe P (yN N) / 8⌋₊

/-! ### Elementary schedule facts -/

theorem L2_tendsto : Tendsto L2 atTop atTop := by
  sorry

theorem L3_tendsto : Tendsto L3 atTop atTop := by
  sorry

/-- The frozen `ε`-window holds eventually. -/
theorem epsN_range : ∀ᶠ N : ℕ in atTop,
    1 / Real.log (Real.log N) < epsN N ∧ epsN N < 1 / 2 := by
  sorry

/-- `y_N ≥ 2`, `y_N ≤ N`, and `log log y_N ≥ (log log N)/2`, eventually. -/
theorem yN_facts : ∀ᶠ N : ℕ in atTop,
    2 ≤ yN N ∧ yN N ≤ N ∧ L2 N / 2 ≤ Real.log (Real.log (yN N)) := by
  sorry

theorem yN_tendsto : Tendsto yN atTop atTop := by
  sorry

theorem JN_le_L3 : ∀ᶠ N : ℕ in atTop, (JN P N : ℝ) ≤ L3 N / 24 := by
  sorry

theorem JN_le_mass (N : ℕ) : 8 * (JN P N : ℝ) ≤ recipSumLe P (yN N) := by
  sorry

theorem JN_tendsto (hP : DivergentRecip P) : Tendsto (JN P) atTop atTop := by
  sorry

/-! ### The mass bounds along the schedule -/

/-- Fresh mass between `y_N` and `N` (from (M1') with `δ = 1/log log y_N ≤ 2/L₂N`). -/
theorem fresh_mass (hS : Sparse P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yN N) N ≤ (2 / L2 N) * (9 + 12 * L3 N) := by
  sorry

/-- Fresh mass between `y_N` and `2N` is eventually at most `1`. -/
theorem fresh_mass_two (hS : Sparse P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yN N) (2 * N) ≤ 1 := by
  sorry

/-! ### The four limits -/

/-- Term 1: `C₁(J) √log(1/ε) √(2 recipSumIoc) → 0`. -/
theorem term_one (hS : Sparse P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => C₁ (JN P N) *
      (Real.sqrt (Real.log (1 / epsN N)) * Real.sqrt (2 * recipSumIoc P (yN N) N)))
      atTop (𝓝 0) := by
  sorry

/-- Term 2: `C₁(J) exp(−recipSumLe P y_N) → 0` (uses `8J ≤ S`). -/
theorem term_two (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => C₁ (JN P N) * Real.exp (- recipSumLe P (yN N))) atTop (𝓝 0) := by
  sorry

/-- Term 3: `C₂(J) exp(−1/(8J²ε_N)) → 0`. -/
theorem term_three (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => C₂ (JN P N) * Real.exp (-1 / (8 * (JN P N : ℝ) ^ 2 * epsN N)))
      atTop (𝓝 0) := by
  sorry

/-- The L¹ tail: `(recipSumLe P (2N) + 5J + 12)/4^J → 0`. -/
theorem tail_family (hS : Sparse P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JN P N : ℝ) + 12) / (4 : ℝ) ^ JN P N)
      atTop (𝓝 0) := by
  sorry

/-! ### Assembly -/

/-- `TailOK P J_N`. -/
theorem tailOK_family (hS : Sparse P) (hP : DivergentRecip P) : TailOK P (JN P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_family P hS hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JN P N) N hN

/-- `KMT_along P J_N`. -/
theorem kmt_along_family (hS : Sparse P) (hP : DivergentRecip P) : KMT_along P (JN P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      C₁ (JN P N) * (Real.sqrt (Real.log (1 / epsN N))
          * Real.sqrt (2 * recipSumIoc P (yN N) N))
        + C₁ (JN P N) * Real.exp (- recipSumLe P (yN N))
        + C₂ (JN P N) * Real.exp (-1 / (8 * (JN P N : ℝ) ^ 2 * epsN N))) atTop (𝓝 0) := by
    have := ((term_one P hS hP).add (term_two P hP)).add (term_three P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [epsN_range, (JN_tendsto P hP).eventually_ge_atTop (h.natAbs + 1),
    eventually_ge_atTop 3] with N hε hJ hN3
  have hntw : NontrivialWindow (JN P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := KMT_quant₂_primeModel P (JN P N) h hh hntw N hN3 (epsN N) hε.1 hε.2
  have hy : yN N = ⌊(N : ℝ) ^ epsN N⌋₊ := rfl
  rw [hy]
  linarith [hb]

/-- **The family theorem.**  Every prime set with `π_P(x) log log x ≤ π(x)` eventually and
divergent reciprocal sum has a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sparse (hS : Sparse P) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JN P) (tailOK_family P hS hP) (kmt_along_family P hS hP)

end NormalNumbers.PrimeModel.Family
