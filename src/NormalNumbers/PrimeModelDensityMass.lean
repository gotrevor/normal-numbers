import NormalNumbers.PrimeModelParameters

/-!
# Prime model, Part II-a: from a prime-density bound to reciprocal-mass bounds

`papers/prime-model-assembly-2026-09-22.md`, Part II, "(M1)" and "(M2)".

Write `π_P(t) = #{p < t : p prime, p ∈ P}` (`(t.primesBelow.filter P).card`).

* **(M1)** dominated Abel summation: if `π_P(t) ≤ δ π(t)` for `y < t ≤ N+1` then
  `recipSumIoc P y N ≤ δ (∑_{y<p≤N} 1/p + 1)`.
* **(M1')** with the interval Mertens bound `primeRecipSum_le`:
  `recipSumIoc P y N ≤ δ (9 + 12 log(log N / log y))` for `2 ≤ y ≤ N`.
* **(M2)** under `Sparse P` (`π_P(x) log log x ≤ π(x)` eventually), the accumulated mass is
  `recipSumLe P N ≤ C_P + 100 log log log N` for all large `N`: cut `(a_i, a_{i+1}]` at
  `a_i = ⌊exp exp 2^i⌋₊`, where the density is `≤ 1/(2^i − 1)` and the Mertens ratio is
  `log a_{i+1}/log a_i ≤ 2 exp 2^i`, so each range carries mass `≤ 42`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.DensityMass

open NormalNumbers.G4Sparse

variable (P : ℕ → Prop) [DecidablePred P]

/-- `π_P(t) = #{p < t : p prime, p ∈ P}`. -/
def piP (t : ℕ) : ℕ := (t.primesBelow.filter P).card

/-- **The density hypothesis of the family theorem**: `π_P(x) · log log x ≤ π(x)` eventually. -/
def Sparse : Prop :=
  ∀ᶠ x : ℕ in atTop, (piP P x : ℝ) * Real.log (Real.log x) ≤ (x.primesBelow.card : ℝ)

/-- `recipSumLe` splits at any intermediate point. -/
theorem recipSumLe_add_recipSumIoc {a b : ℕ} (hab : a ≤ b) :
    recipSumLe P b = recipSumLe P a + recipSumIoc P a b := by
  sorry

/-- `recipSumLe P` is monotone. -/
theorem recipSumLe_mono {a b : ℕ} (hab : a ≤ b) : recipSumLe P a ≤ recipSumLe P b := by
  sorry

/-- `recipSumIoc ≥ 0`. -/
theorem recipSumIoc_nonneg (y N : ℕ) : 0 ≤ recipSumIoc P y N := by
  sorry

/-- Divergent reciprocal sum ⇒ the partial sums tend to infinity. -/
theorem recipSumLe_tendsto_atTop (hP : DivergentRecip P) :
    Tendsto (recipSumLe P) atTop atTop := by
  sorry

/-- **(M1) dominated Abel summation.**  If `π_P(t) ≤ δ π(t)` for all `y < t ≤ N + 1`, then
`∑_{y<p≤N, p∈P} 1/p ≤ δ (∑_{y<p≤N} 1/p + 1)`. -/
theorem recipSumIoc_le_of_dominated {δ : ℝ} (hδ : 0 ≤ δ) (y N : ℕ)
    (hdom : ∀ t, y < t → t ≤ N + 1 → (piP P t : ℝ) ≤ δ * (t.primesBelow.card : ℝ)) :
    recipSumIoc P y N ≤ δ * ((∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (1 : ℝ) / p) + 1) := by
  sorry

/-- **(M1')** with the interval Mertens bound. -/
theorem recipSumIoc_le_of_dominated' {δ : ℝ} (hδ : 0 ≤ δ) {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N)
    (hdom : ∀ t, y < t → t ≤ N + 1 → (piP P t : ℝ) ≤ δ * (t.primesBelow.card : ℝ)) :
    recipSumIoc P y N ≤ δ * (9 + 12 * Real.log (Real.log N / Real.log y)) := by
  sorry

/-- **(M2) accumulated mass under `Sparse`.** -/
theorem recipSumLe_le_of_sparse (hS : Sparse P) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      recipSumLe P N ≤ C + 100 * Real.log (Real.log (Real.log N)) := by
  sorry

end NormalNumbers.PrimeModel.DensityMass
