import NormalNumbers.TwoPointGramDiag

/-!
# The `ℓ²` obstruction, made quantitative

Lap 17's split is exact but its reading ("the bracket is of order `−N²`") was prose.  This file
proves it, with explicit constants and no asymptotic hand-waving:

* `maxRecipSum_le_two_card` — `M(w) = Σ_{p≠q≤w} 1/max(p,q) ≤ 2π(w)`.
  (Split at `q < p`; the inner sum is `#{q < p}/p ≤ 1` because the primes below `p` are distinct
  naturals in `[0,p)`.  No prime counting beyond that.)
* `sum_min_le` — `Σ_{p,q≤w} min(⌊N/p⌋,⌊N/q⌋) ≤ N·(M(w) + L(w))`.
* `sum_floor_sq_ge` — `Σ_{p≤w} ⌊N/p⌋² ≥ ⌊N/2⌋²` (the prime `2` alone).
* **`fourthMoment_offDiag_ge`** — for `25 ≤ w`, `w² ≤ N`, unimodular `a`:

      Σ_{m ≠ m' ≤ N} ‖Σ_{p≤w} a(pm) conj a(pm')‖²  ≥  kataiPairGramSq a w N  +  N²/8 .

So the off-diagonal fourth moment of the dilation family is bounded **below** by `N²/8`, while
the `ℓ²` route (lap 15) needs `kataiPairGramSq ≤ ε²N²L(w)⁴/π(w)²`, i.e. it needs that fourth
moment evaluated to relative precision `≤ 8ε²L(w)⁴/π(w)² → 0`.  A lower bound of order `N²` with
a demand for `o(N²)` accuracy is an asymptotic-evaluation problem, not an estimation problem;
this is the kernel-checked form of lap 17's verdict.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `M(w) ≤ 2π(w)`. -/
theorem maxRecipSum_le_two_card (w : ℕ) :
    maxRecipSum w ≤ 2 * ((primesLe w).card : ℝ) := by
  classical
  have hsplit : ∀ p q : ℕ, 0 < p → 0 < q →
      (if p = q then (0:ℝ) else 1 / ((max p q : ℕ) : ℝ))
        ≤ (if q < p then 1 / (p:ℝ) else 0) + (if p < q then 1 / (q:ℝ) else 0) := by
    intro p q hp hq
    by_cases hpq : p = q
    · simp [hpq]
    · rw [if_neg hpq]
      rcases lt_or_gt_of_ne hpq with h | h
      · rw [if_neg (by omega), if_pos h, max_eq_right (by omega : p ≤ q)]
        simp
      · rw [if_pos h, if_neg (by omega), max_eq_left (by omega : q ≤ p)]
        simp
  have hrow : ∀ p ∈ primesLe w,
      ∑ q ∈ primesLe w, (if q < p then 1 / (p:ℝ) else 0) ≤ 1 := by
    intro p hp
    have hppos : 0 < p := (prime_of_mem_primesLe hp).pos
    have hcard : (((primesLe w).filter (fun q => q < p)).card : ℝ) ≤ (p : ℝ) := by
      have hsub : ((primesLe w).filter (fun q => q < p)) ⊆ Finset.range p := by
        intro q hq
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hq).2
      have h := Finset.card_le_card hsub
      rw [Finset.card_range] at h
      exact_mod_cast h
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      div_le_one (by exact_mod_cast hppos)]
    exact hcard
  have hcol : ∀ q ∈ primesLe w,
      ∑ p ∈ primesLe w, (if p < q then 1 / (q:ℝ) else 0) ≤ 1 := by
    intro q hq
    have hqpos : 0 < q := (prime_of_mem_primesLe hq).pos
    have hcard : (((primesLe w).filter (fun p => p < q)).card : ℝ) ≤ (q : ℝ) := by
      have hsub : ((primesLe w).filter (fun p => p < q)) ⊆ Finset.range q := by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      have h := Finset.card_le_card hsub
      rw [Finset.card_range] at h
      exact_mod_cast h
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      div_le_one (by exact_mod_cast hqpos)]
    exact hcard
  calc maxRecipSum w
      ≤ ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          ((if q < p then 1 / (p:ℝ) else 0) + (if p < q then 1 / (q:ℝ) else 0)) := by
        refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
        exact hsplit p q (prime_of_mem_primesLe hp).pos (prime_of_mem_primesLe hq).pos
    _ = (∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if q < p then 1 / (p:ℝ) else 0))
          + ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p < q then 1 / (q:ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib
    _ ≤ ((primesLe w).card : ℝ) + ((primesLe w).card : ℝ) := by
        have h1 : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if q < p then 1 / (p:ℝ) else 0)
            ≤ ((primesLe w).card : ℝ) := by
          calc ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if q < p then 1 / (p:ℝ) else 0)
              ≤ ∑ _p ∈ primesLe w, (1:ℝ) := Finset.sum_le_sum hrow
            _ = ((primesLe w).card : ℝ) := by simp
        have h2 : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p < q then 1 / (q:ℝ) else 0)
            ≤ ((primesLe w).card : ℝ) := by
          rw [Finset.sum_comm]
          calc ∑ q ∈ primesLe w, ∑ p ∈ primesLe w, (if p < q then 1 / (q:ℝ) else 0)
              ≤ ∑ _q ∈ primesLe w, (1:ℝ) := Finset.sum_le_sum hcol
            _ = ((primesLe w).card : ℝ) := by simp
        linarith
    _ = 2 * ((primesLe w).card : ℝ) := by ring

/-- `Σ_{p,q} min(⌊N/p⌋,⌊N/q⌋) ≤ N·(M(w) + L(w))`. -/
theorem sum_min_le (w N : ℕ) :
    ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, ((min (N / p) (N / q) : ℕ) : ℝ)
      ≤ (N : ℝ) * (maxRecipSum w + kataiPrimeRecip w) := by
  classical
  have hterm : ∀ p ∈ primesLe w, ∀ q ∈ primesLe w,
      ((min (N / p) (N / q) : ℕ) : ℝ)
        ≤ (N:ℝ) * ((if p = q then (0:ℝ) else 1 / ((max p q : ℕ) : ℝ))
            + (if p = q then 1 / (p:ℝ) else 0)) := by
    intro p hp q hq
    have hppos : 0 < p := (prime_of_mem_primesLe hp).pos
    have hqpos : 0 < q := (prime_of_mem_primesLe hq).pos
    by_cases hpq : p = q
    · subst hpq
      have hrw : (N:ℝ) * ((if p = p then (0:ℝ) else 1 / ((max p p : ℕ) : ℝ))
          + (if p = p then 1 / (p:ℝ) else 0)) = (N:ℝ) / p := by
        simp [div_eq_mul_inv]
      rw [min_self, hrw]
      exact Nat.cast_div_le
    · rw [if_neg hpq, if_neg hpq, add_zero, mul_one_div]
      exact min_div_le N p q hppos hqpos
  calc ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, ((min (N / p) (N / q) : ℕ) : ℝ)
      ≤ ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          (N:ℝ) * ((if p = q then (0:ℝ) else 1 / ((max p q : ℕ) : ℝ))
            + (if p = q then 1 / (p:ℝ) else 0)) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hterm p hp q hq
    _ = (N : ℝ) * (maxRecipSum w + kataiPrimeRecip w) := by
        have hstep : ∀ p ∈ primesLe w,
            ∑ q ∈ primesLe w, (N:ℝ) * ((if p = q then (0:ℝ) else 1 / ((max p q : ℕ) : ℝ))
                + (if p = q then 1 / (p:ℝ) else 0))
              = (N:ℝ) * (∑ q ∈ primesLe w,
                  (if p = q then (0:ℝ) else 1 / ((max p q : ℕ) : ℝ))) + (N:ℝ) * (1 / (p:ℝ)) := by
          intro p hp
          simp only [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_ite_eq (primesLe w) p (fun _ => 1 / (p:ℝ))]
          simp [hp]
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← mul_add, maxRecipSum, kataiPrimeRecip]

/-- `Σ_{p ≤ w} ⌊N/p⌋² ≥ ⌊N/2⌋²`. -/
theorem sum_floor_sq_ge (w N : ℕ) (hw : 2 ≤ w) :
    (((N / 2 : ℕ)) : ℝ) ^ 2 ≤ ∑ p ∈ primesLe w, ((N / p : ℕ) : ℝ) ^ 2 := by
  classical
  have h2 : (2 : ℕ) ∈ primesLe w :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  exact Finset.single_le_sum (f := fun p : ℕ => ((N / p : ℕ) : ℝ) ^ 2) (fun p _ => by positivity) h2

/-- **THE OFF-DIAGONAL FOURTH MOMENT IS FORCED TO BE `≥ N²/8`.** -/
theorem fourthMoment_offDiag_ge (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ = 1) (w N : ℕ)
    (hw : 25 ≤ w) (hN : w ^ 2 ≤ N) :
    kataiPairGramSq a w N + (N : ℝ) ^ 2 / 8
      ≤ ∑ m ∈ Finset.range (N + 1), ∑ m' ∈ Finset.range (N + 1),
          (if m = m' then 0
            else ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2) := by
  have hsplit := kataiPairGramSq_split a ha w N
  have hwR : (25 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hNR : ((w : ℝ)) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [hwR, hNR]
  -- `M(w) + L(w) ≤ 2w + w/2`
  have hM : maxRecipSum w ≤ 2 * (w : ℝ) := by
    refine le_trans (maxRecipSum_le_two_card w) ?_
    have : ((primesLe w).card : ℝ) ≤ (w : ℝ) := by
      have h := card_primesLe_le w
      have : (primesLe w).card ≤ w := le_trans h (Nat.sub_le _ _)
      exact_mod_cast this
    linarith
  have hL : kataiPrimeRecip w ≤ (w : ℝ) := kataiPrimeRecip_le_self w
  have hmin := sum_min_le w N
  have hfloor := sum_floor_sq_ge w N (by omega)
  -- `⌊N/2⌋ ≥ (N-1)/2`
  have hhalf : ((N : ℝ) - 1) / 2 ≤ (((N / 2 : ℕ)) : ℝ) := by
    have : (N : ℝ) ≤ 2 * (((N / 2 : ℕ)) : ℝ) + 1 := by
      have h := Nat.lt_succ_of_le (Nat.div_mul_le_self N 2)
      have h2 : N ≤ 2 * (N / 2) + 1 := by omega
      exact_mod_cast h2
    linarith
  have hhalfnn : (0:ℝ) ≤ ((N : ℝ) - 1) / 2 := by nlinarith [hwR, hNR]
  have hfloorsq : ((N : ℝ) - 1) ^ 2 / 4 ≤ ∑ p ∈ primesLe w, ((N / p : ℕ) : ℝ) ^ 2 := by
    refine le_trans ?_ hfloor
    have : (((N : ℝ) - 1) / 2) ^ 2 ≤ (((N / 2 : ℕ)) : ℝ) ^ 2 := by
      nlinarith [hhalf, hhalfnn]
    calc ((N : ℝ) - 1) ^ 2 / 4 = (((N : ℝ) - 1) / 2) ^ 2 := by ring
      _ ≤ _ := this
  -- assemble the bracket bound
  have hbracket : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, ((min (N / p) (N / q) : ℕ) : ℝ)
      - ∑ p ∈ primesLe w, ((N / p : ℕ) : ℝ) ^ 2 ≤ - ((N : ℝ) ^ 2 / 8) := by
    have h1 : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, ((min (N / p) (N / q) : ℕ) : ℝ)
        ≤ (N : ℝ) * (2 * (w:ℝ) + (w:ℝ)) := by
      refine le_trans hmin ?_
      have : maxRecipSum w + kataiPrimeRecip w ≤ 2 * (w:ℝ) + (w:ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left this hNpos.le
    have hNw : 3 * (w : ℝ) + 1/2 ≤ (N:ℝ)/8 := by nlinarith [hwR, hNR]
    have hmulN := mul_le_mul_of_nonneg_right hNw hNpos.le
    have hwN : 3 * (w : ℝ) * (N:ℝ) + (N:ℝ)^2/8 ≤ ((N:ℝ) - 1)^2/4 := by
      nlinarith [hmulN, hNpos]
    linarith [h1, hfloorsq, hwN]
  linarith [hsplit, hbracket]

end NormalNumbers.CastingOut
