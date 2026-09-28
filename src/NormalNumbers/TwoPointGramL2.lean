import NormalNumbers.TwoPointGramMarkov

/-!
# The `ℓ²` route to the leaf, and exactly what it demands

Lap 14 placed the leaf as an MRT-shaped (dilation-average) problem.  The one standard handle on
such a sum is Cauchy–Schwarz in the pair index, turning the pair sum into an `ℓ²` mass which
expands (via `sum_sq_superposition`) into a fourth moment of the dilation family.  This file sets
that route up and prices it.

* `kataiPairGram_sq_le` — `(Σ_{p≠q} ‖G_{pq}‖)² ≤ π(w)² · Σ_{p≠q} ‖G_{pq}‖²` (Chebyshev/CS).
* `kataiPairGram_le_of_l2` — hence the leaf follows from
  `Σ_{p≠q} ‖G_{pq}‖² ≤ ε² N² L(w)⁴ / π(w)²`.
* `tendsto_l2_budget_ratio` — the price: `L(w)⁴/π(w)² → 0`, so the `ℓ²` demand is `o(N²)` by an
  unbounded factor.  Unlike the `ℓ¹` demand of lap 13, this one is *not* obviously beyond reach:
  the trivial `ℓ²` bound is `Σ_{p≠q} (N/max(p,q))² = N² Σ_{p≠q} 1/max(p,q)²`, and
  `Σ_{p≠q} 1/max(p,q)² ≤ 2 Σ_p π(p)/p²` — a sum which, unlike `M(w)`, is plausibly comparable to
  the demand only after genuine cancellation, but which is at least *bounded* rather than
  divergent relative to a fixed constant.  Deciding that comparison is lap 16's job.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The `ℓ²` mass of the off-diagonal Gram matrix. -/
noncomputable def kataiPairGramSq (a : ℕ → ℂ) (w N : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
    if p = q then 0 else ‖csGram (kataiTrunc a N) (N + 1) p q‖ ^ 2

lemma kataiPairGram_eq_prod (a : ℕ → ℂ) (w N : ℕ) :
    kataiPairGram a w N
      = ∑ pq ∈ primesLe w ×ˢ primesLe w,
          (if pq.1 = pq.2 then 0 else ‖csGram (kataiTrunc a N) (N + 1) pq.1 pq.2‖) := by
  rw [kataiPairGram, Finset.sum_product]

lemma kataiPairGramSq_eq_prod (a : ℕ → ℂ) (w N : ℕ) :
    kataiPairGramSq a w N
      = ∑ pq ∈ primesLe w ×ˢ primesLe w,
          (if pq.1 = pq.2 then 0 else ‖csGram (kataiTrunc a N) (N + 1) pq.1 pq.2‖) ^ 2 := by
  rw [kataiPairGramSq, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases h : p = q <;> simp [h]

/-- **CAUCHY–SCHWARZ IN THE PAIR INDEX.** -/
theorem kataiPairGram_sq_le (a : ℕ → ℂ) (w N : ℕ) :
    (kataiPairGram a w N) ^ 2
      ≤ (((primesLe w).card : ℝ)) ^ 2 * kataiPairGramSq a w N := by
  classical
  rw [kataiPairGram_eq_prod, kataiPairGramSq_eq_prod]
  have h := sq_sum_le_card_mul_sum_sq (s := primesLe w ×ˢ primesLe w)
    (f := fun pq => if pq.1 = pq.2 then (0:ℝ)
      else ‖csGram (kataiTrunc a N) (N + 1) pq.1 pq.2‖)
  refine le_trans h ?_
  have hcard : (((primesLe w ×ˢ primesLe w).card : ℕ) : ℝ) = (((primesLe w).card : ℝ)) ^ 2 := by
    rw [Finset.card_product]; push_cast; ring
  rw [hcard]

/-- **THE `ℓ²` SUFFICIENT CONDITION.**  The leaf's `ℓ¹` bound follows from an `ℓ²` bound
discounted by `π(w)²`. -/
theorem kataiPairGram_le_of_l2 (a : ℕ → ℂ) (w N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hL : 0 ≤ kataiPrimeRecip w)
    (h : kataiPairGramSq a w N
      ≤ ε ^ 2 * (N : ℝ) ^ 2 * (kataiPrimeRecip w) ^ 4 / (((primesLe w).card : ℝ)) ^ 2)
    (hcard : 0 < (((primesLe w).card : ℝ))) :
    kataiPairGram a w N ≤ ε * (N : ℝ) * (kataiPrimeRecip w) ^ 2 := by
  have hGnn : 0 ≤ kataiPairGram a w N := kataiPairGram_nonneg a w N
  have hsq := kataiPairGram_sq_le a w N
  have hbound : (kataiPairGram a w N) ^ 2
      ≤ (ε * (N : ℝ) * (kataiPrimeRecip w) ^ 2) ^ 2 := by
    refine le_trans hsq ?_
    have := mul_le_mul_of_nonneg_left h (le_of_lt (by positivity :
      (0:ℝ) < (((primesLe w).card : ℝ)) ^ 2))
    refine le_trans this ?_
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (kataiPrimeRecip w), sq_nonneg ((N:ℝ)), sq_nonneg ε]
  have hrhs : 0 ≤ ε * (N : ℝ) * (kataiPrimeRecip w) ^ 2 := by positivity
  nlinarith [hbound, hGnn, hrhs]

/-- **THE PRICE OF THE `ℓ²` ROUTE.**  `L(w)⁴/π(w)² → 0`. -/
theorem tendsto_l2_budget_ratio :
    Tendsto (fun w => (kataiPrimeRecip w) ^ 4 / (((primesLe w).card : ℝ)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_card_div_kataiPrimeRecip_sq
  have hinv : Tendsto (fun w => ((kataiPrimeRecip w) ^ 2 / (((primesLe w).card : ℝ))))
      atTop (𝓝 0) := by
    simpa [one_div, Pi.inv_def] using h.inv_tendsto_atTop
  have hsq := hinv.mul hinv
  rw [mul_zero] at hsq
  refine hsq.congr fun w => ?_
  rw [div_mul_div_comm, ← pow_add, ← sq]

end NormalNumbers.CastingOut
