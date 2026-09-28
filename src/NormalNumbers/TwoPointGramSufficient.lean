import NormalNumbers.TwoPointGramForced

/-!
# What per-pair strength WOULD prove the leaf

Laps 13–18 priced the two Cauchy–Schwarz presentations of the leaf.  A correction to the prose of
laps 17–18 first, then the positive statement.

## Correction (honest bookkeeping)

Laps 17–18 said "both routes are refuted".  What is actually proved is weaker and should be
stated as such:

* lap 13 (`tendsto_maxRecipSum_div_sq`): *trivial* per-pair bounds cannot give the leaf — the
  trivial mass exceeds the budget by an unbounded factor.  That refutes an estimate, not a route.
* laps 17–18 (`kataiPairGramSq_split`, `fourthMoment_offDiag_ge`): *if* one bounds
  `kataiPairGramSq` through the fourth-moment presentation, one must evaluate a quantity that is
  `≥ N²/8` to vanishing relative error.  That refutes that presentation, not every possible
  bound on `kataiPairGramSq`.

Neither result rules out a direct argument.  The confidences in the lap-17/18 handoffs are kept,
but the word "refuted" there should be read as "refuted as an estimation strategy".

## The positive statement

Since `M(w) ≤ 2π(w)` (lap 18), a *uniform relative saving* over the trivial per-pair bound
suffices, and the required saving is explicit:

* `twoPointGramSum_le_of_uniform` — if `‖T_{p,q}(N)‖ ≤ δ·N/max(p,q)` for all `p ≠ q ≤ w`, then
  `twoPointGramSum b t w N ≤ 2δ·N·π(w)`.
* **`gramBudget_of_uniform_saving`** — hence `δ ≤ ε·L(w)²/(2π(w))` gives the leaf's budget
  `twoPointGramSum ≤ ε·N·L(w)²`.

So the leaf follows from a per-pair bound with relative saving `L(w)²/π(w)` — a saving measured
in the **size of the primes**, not in `N`.  With `w = w(N)` free to grow as slowly as one likes
(subject only to `w → ∞`, `w² ≤ N`), this is the concrete target a future analytic argument must
hit, and it is the form in which Elliott-type input would arrive.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- A uniform relative saving over the trivial per-pair bound controls the pair sum. -/
theorem twoPointGramSum_le_of_uniform (b : ℕ) (t : ℝ) (δ : ℝ) (w N : ℕ) (hδ : 0 ≤ δ)
    (h : ∀ p ∈ primesLe w, ∀ q ∈ primesLe w, p ≠ q →
      ‖twoPointTruncSum b p q t N‖ ≤ δ * (N : ℝ) / ((max p q : ℕ) : ℝ)) :
    twoPointGramSum b t w N ≤ 2 * δ * (N : ℝ) * ((primesLe w).card : ℝ) := by
  classical
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hstep : twoPointGramSum b t w N ≤ δ * (N : ℝ) * maxRecipSum w := by
    rw [twoPointGramSum, maxRecipSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    by_cases hpq : p = q
    · simp [hpq]
    · rw [if_neg hpq, if_neg hpq, mul_one_div]
      exact h p hp q hq hpq
  refine le_trans hstep ?_
  have hM := maxRecipSum_le_two_card w
  have hcoef : (0 : ℝ) ≤ δ * (N : ℝ) := by positivity
  calc δ * (N : ℝ) * maxRecipSum w ≤ δ * (N : ℝ) * (2 * ((primesLe w).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hM hcoef
    _ = 2 * δ * (N : ℝ) * ((primesLe w).card : ℝ) := by ring

/-- **THE PER-PAIR TARGET.**  A uniform relative saving `L(w)²/(2π(w))` gives the leaf's budget. -/
theorem gramBudget_of_uniform_saving (b : ℕ) (t : ℝ) (ε δ : ℝ) (w N : ℕ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hw : 2 ≤ w)
    (hsave : δ ≤ ε * (kataiPrimeRecip w) ^ 2 / (2 * ((primesLe w).card : ℝ)))
    (h : ∀ p ∈ primesLe w, ∀ q ∈ primesLe w, p ≠ q →
      ‖twoPointTruncSum b p q t N‖ ≤ δ * (N : ℝ) / ((max p q : ℕ) : ℝ)) :
    twoPointGramSum b t w N ≤ ε * (N : ℝ) * (kataiPrimeRecip w) ^ 2 := by
  have hcard : (0 : ℝ) < ((primesLe w).card : ℝ) := by
    exact_mod_cast card_primesLe_pos hw
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  refine le_trans (twoPointGramSum_le_of_uniform b t δ w N hδ h) ?_
  have hmul : 2 * δ * ((primesLe w).card : ℝ) ≤ ε * (kataiPrimeRecip w) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsave (by norm_num : (0:ℝ) ≤ 2)
    rw [mul_div_assoc'] at this
    have hrw : 2 * (ε * (kataiPrimeRecip w) ^ 2) / (2 * ((primesLe w).card : ℝ))
        = ε * (kataiPrimeRecip w) ^ 2 / ((primesLe w).card : ℝ) := by
      field_simp
    rw [hrw] at this
    have h2 := mul_le_mul_of_nonneg_right this hcard.le
    rw [div_mul_cancel₀ _ (ne_of_gt hcard)] at h2
    linarith [h2]
  calc 2 * δ * (N : ℝ) * ((primesLe w).card : ℝ)
      = (N : ℝ) * (2 * δ * ((primesLe w).card : ℝ)) := by ring
    _ ≤ (N : ℝ) * (ε * (kataiPrimeRecip w) ^ 2) := mul_le_mul_of_nonneg_left hmul hNnn
    _ = ε * (N : ℝ) * (kataiPrimeRecip w) ^ 2 := by ring

end NormalNumbers.CastingOut
