import NormalNumbers.TwoPointGramArith

/-!
# The trivial bound misses the Kátai budget by an unbounded factor

The leaf `twoPointGramSum b t (w N) N = o(N · L(w)²)` is a statement about cancellation.  How
much cancellation?  Trivially

    ‖twoPointTruncSum b p q t N‖ ≤ min(⌊N/p⌋, ⌊N/q⌋) ≤ N / max(p, q),

so the trivial bound on the pair sum is `N · M(w)` with `M(w) = Σ_{p≠q≤w} 1/max(p,q)`.  This file
proves `M(w) / L(w)² → ∞`: the required saving, averaged over pairs, is an **unbounded** factor.
So no amount of averaging over multipliers makes the leaf free — genuine two-point cancellation
is needed for almost every pair.

The proof needs no prime counting, only Mertens divergence (`tendsto_kataiPrimeRecip`, already in
kernel): restricting to pairs with both primes `> z` gives `M(w) ≥ z·D² − D` with
`D = L(w) − L(z)`, and `D ≥ L(w)/2` eventually, so `M(w)/L(w)² ≥ z/4 − 1` for every `z`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `M(w) = Σ_{p ≠ q ≤ w} 1/max(p,q)`, the trivial bound's shape. -/
noncomputable def maxRecipSum (w : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, if p = q then 0 else 1 / ((max p q : ℕ) : ℝ)

lemma norm_twoPointTruncSum_le (b p q : ℕ) (t : ℝ) (N : ℕ) :
    ‖twoPointTruncSum b p q t N‖ ≤ ((min (N / p) (N / q) : ℕ) : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ Finset.Ioc 0 (min (N / p) (N / q)),
      ‖twoPointFactor b p q t m * peelWeight b p q t m‖ ≤ 1 := by
    intro m _
    rw [norm_mul, norm_twoPointFactor, norm_peelWeight, mul_one]
  calc ∑ m ∈ Finset.Ioc 0 (min (N / p) (N / q)), ‖twoPointFactor b p q t m * peelWeight b p q t m‖
      ≤ ∑ _m ∈ Finset.Ioc 0 (min (N / p) (N / q)), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((min (N / p) (N / q) : ℕ) : ℝ) := by simp

/-- `min(⌊N/p⌋, ⌊N/q⌋) ≤ N / max(p,q)`. -/
lemma min_div_le (N p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ((min (N / p) (N / q) : ℕ) : ℝ) ≤ (N : ℝ) / ((max p q : ℕ) : ℝ) := by
  rcases le_total p q with h | h
  · have : min (N / p) (N / q) = N / q := by
      simpa [min_eq_right] using min_eq_right (Nat.div_le_div_left h hp)
    rw [this, max_eq_right h]
    exact Nat.cast_div_le
  · have : min (N / p) (N / q) = N / p := by
      simpa [min_eq_left] using min_eq_left (Nat.div_le_div_left h hq)
    rw [this, max_eq_left h]
    exact Nat.cast_div_le

/-- **THE TRIVIAL BOUND.** -/
theorem twoPointGramSum_le (b : ℕ) (t : ℝ) (w N : ℕ) :
    twoPointGramSum b t w N ≤ (N : ℝ) * maxRecipSum w := by
  classical
  rw [maxRecipSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_neg hpq, if_neg hpq]
    have hppos : 0 < p := (prime_of_mem_primesLe hp).pos
    have hqpos : 0 < q := (prime_of_mem_primesLe hq).pos
    calc ‖twoPointTruncSum b p q t N‖ ≤ ((min (N / p) (N / q) : ℕ) : ℝ) :=
          norm_twoPointTruncSum_le b p q t N
      _ ≤ (N : ℝ) / ((max p q : ℕ) : ℝ) := min_div_le N p q hppos hqpos
      _ = (N : ℝ) * (1 / ((max p q : ℕ) : ℝ)) := by rw [mul_one_div]

/-! ### `M(w) / L(w)² → ∞` -/

lemma offdiag_sq (S : Finset ℕ) (c : ℕ → ℝ) :
    ∑ p ∈ S, ∑ q ∈ S, (if p = q then (0 : ℝ) else c p * c q)
      = (∑ p ∈ S, c p) ^ 2 - ∑ p ∈ S, (c p) ^ 2 := by
  classical
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h : ∀ q ∈ S, (if p = q then (0 : ℝ) else c p * c q)
      = c p * c q - (if p = q then c p * c q else 0) := by
    intro q _
    by_cases hq : p = q <;> simp [hq]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib,
    Finset.sum_ite_eq S p (fun q => c p * c q)]
  simp [hp, sq]

/-- Restricting the pair sum to primes `> z` gives `M(w) ≥ z·D² − D`, `D = L(w) − L(z)`. -/
lemma maxRecipSum_ge (z w : ℕ) (hz : 1 ≤ z) (hzw : z ≤ w) :
    (z : ℝ) * (kataiPrimeRecip w - kataiPrimeRecip z) ^ 2
        - (kataiPrimeRecip w - kataiPrimeRecip z)
      ≤ maxRecipSum w := by
  classical
  set S := primesLe w \ primesLe z with hS
  have hSsub : S ⊆ primesLe w := Finset.sdiff_subset
  have hgt : ∀ p ∈ S, (z : ℝ) < (p : ℝ) := by
    intro p hp
    have hpw := Finset.mem_sdiff.mp hp
    have hprime := prime_of_mem_primesLe hpw.1
    have : ¬ (p ≤ z) := by
      intro hle
      exact hpw.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩)
    exact_mod_cast (by omega : z < p)
  have hD : ∑ p ∈ S, (1 : ℝ) / p = kataiPrimeRecip w - kataiPrimeRecip z := by
    rw [kataiPrimeRecip, kataiPrimeRecip, hS, Finset.sum_sdiff_eq_sub (primesLe_mono hzw)]
  set D := kataiPrimeRecip w - kataiPrimeRecip z with hDdef
  -- lower bound the full sum by the restricted one
  have hnn : ∀ p q : ℕ, (0 : ℝ) ≤ if p = q then 0 else 1 / ((max p q : ℕ) : ℝ) := by
    intro p q
    by_cases h : p = q
    · simp [h]
    · rw [if_neg h]; positivity
  have hrestrict : ∑ p ∈ S, ∑ q ∈ S, (if p = q then (0 : ℝ) else 1 / ((max p q : ℕ) : ℝ))
      ≤ maxRecipSum w := by
    rw [maxRecipSum]
    refine le_trans (Finset.sum_le_sum (fun p _ =>
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun q _ _ => hnn p q))) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
      (fun p _ _ => Finset.sum_nonneg fun q _ => hnn p q)
  -- termwise: `1/max(p,q) ≥ z/(pq)` for `p, q > z`
  have hterm : ∀ p ∈ S, ∀ q ∈ S,
      (z : ℝ) * (if p = q then (0:ℝ) else (1/(p:ℝ)) * (1/(q:ℝ)))
        ≤ if p = q then (0 : ℝ) else 1 / ((max p q : ℕ) : ℝ) := by
    intro p hp q hq
    by_cases hpq : p = q
    · simp [hpq]
    · rw [if_neg hpq, if_neg hpq]
      have hzR : (0 : ℝ) < z := by exact_mod_cast hz
      have hpz := hgt p hp
      have hqz := hgt q hq
      have hp0 : (0 : ℝ) < p := lt_trans hzR hpz
      have hq0 : (0 : ℝ) < q := lt_trans hzR hqz
      have hmax : ((max p q : ℕ) : ℝ) = max (p : ℝ) (q : ℝ) := by
        rcases le_total p q with h | h
        · rw [max_eq_right h, max_eq_right (by exact_mod_cast h : (p:ℝ) ≤ q)]
        · rw [max_eq_left h, max_eq_left (by exact_mod_cast h : (q:ℝ) ≤ p)]
      rw [hmax]
      rcases le_total (p : ℝ) (q : ℝ) with h | h
      · rw [max_eq_right h]
        have hzp : (z : ℝ) / p ≤ 1 := by rw [div_le_one hp0]; linarith
        calc (z : ℝ) * (1 / (p:ℝ) * (1 / (q:ℝ))) = ((z:ℝ)/p) * (1/(q:ℝ)) := by ring
          _ ≤ 1 * (1/(q:ℝ)) := mul_le_mul_of_nonneg_right hzp (by positivity)
          _ = 1 / (q:ℝ) := by ring
      · rw [max_eq_left h]
        have hzq : (z : ℝ) / q ≤ 1 := by rw [div_le_one hq0]; linarith
        calc (z : ℝ) * (1 / (p:ℝ) * (1 / (q:ℝ))) = ((z:ℝ)/q) * (1/(p:ℝ)) := by ring
          _ ≤ 1 * (1/(p:ℝ)) := mul_le_mul_of_nonneg_right hzq (by positivity)
          _ = 1 / (p:ℝ) := by ring
  have hlow : (z : ℝ) * (D ^ 2 - ∑ p ∈ S, (1/(p:ℝ)) ^ 2)
      ≤ ∑ p ∈ S, ∑ q ∈ S, (if p = q then (0 : ℝ) else 1 / ((max p q : ℕ) : ℝ)) := by
    have := offdiag_sq S (fun p => 1/(p:ℝ))
    rw [hD] at this
    calc (z : ℝ) * (D ^ 2 - ∑ p ∈ S, (1/(p:ℝ)) ^ 2)
        = (z : ℝ) * ∑ p ∈ S, ∑ q ∈ S, (if p = q then (0:ℝ) else (1/(p:ℝ)) * (1/(q:ℝ))) := by
          rw [this]
      _ = ∑ p ∈ S, ∑ q ∈ S, (z : ℝ) * (if p = q then (0:ℝ) else (1/(p:ℝ)) * (1/(q:ℝ))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hterm p hp q hq
  -- `Σ_{p ∈ S} 1/p² ≤ D/z`
  have hsq : ∑ p ∈ S, (1/(p:ℝ)) ^ 2 ≤ D / z := by
    have hzR : (0 : ℝ) < z := by exact_mod_cast hz
    have : ∀ p ∈ S, (1/(p:ℝ)) ^ 2 ≤ (1/(z:ℝ)) * (1/(p:ℝ)) := by
      intro p hp
      have hpz := hgt p hp
      have hp0 : (0 : ℝ) < p := lt_trans hzR hpz
      have hle : 1 / (p:ℝ) ≤ 1 / (z:ℝ) := one_div_le_one_div_of_le hzR hpz.le
      calc (1/(p:ℝ)) ^ 2 = (1/(p:ℝ)) * (1/(p:ℝ)) := by ring
        _ ≤ (1/(z:ℝ)) * (1/(p:ℝ)) := mul_le_mul_of_nonneg_right hle (by positivity)
    calc ∑ p ∈ S, (1/(p:ℝ)) ^ 2 ≤ ∑ p ∈ S, (1/(z:ℝ)) * (1/(p:ℝ)) := Finset.sum_le_sum this
      _ = (1/(z:ℝ)) * D := by rw [← Finset.mul_sum, hD]
      _ = D / z := by ring
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hstep : (z : ℝ) * D ^ 2 - D ≤ (z : ℝ) * (D ^ 2 - ∑ p ∈ S, (1/(p:ℝ)) ^ 2) := by
    have : (z : ℝ) * (D / z) = D := by field_simp
    nlinarith [hsq, hzR]
  linarith [hstep, hlow, hrestrict]

/-- **THE BUDGET GAP.**  `M(w)/L(w)² → ∞`: the trivial bound exceeds the Kátai budget by an
unbounded factor, so the open leaf demands genuine two-point cancellation, not merely averaging
over multipliers. -/
theorem tendsto_maxRecipSum_div_sq :
    Tendsto (fun w => maxRecipSum w / (kataiPrimeRecip w) ^ 2) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  obtain ⟨z, hz⟩ := exists_nat_gt (max (4 * (M + 1)) 1)
  have hz1 : 1 ≤ z := by
    have : (1 : ℝ) < z := lt_of_le_of_lt (le_max_right _ _) hz
    exact_mod_cast this.le
  have hzM : 4 * (M + 1) < (z : ℝ) := lt_of_le_of_lt (le_max_left _ _) hz
  have hLtop := tendsto_kataiPrimeRecip
  filter_upwards [hLtop.eventually_ge_atTop (2 * kataiPrimeRecip z),
    hLtop.eventually_ge_atTop 1, Filter.eventually_ge_atTop z] with w hw1 hw2 hw3
  set L := kataiPrimeRecip w with hLdef
  set D := L - kataiPrimeRecip z with hDdef
  have hDhalf : L / 2 ≤ D := by rw [hDdef]; linarith
  have hL1 : (1 : ℝ) ≤ L := hw2
  have hDpos : 0 < D := by linarith
  have hkey := maxRecipSum_ge z w hz1 hw3
  rw [← hLdef, ← hDdef] at hkey
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz1
  have hDL : D ≤ L := by
    have : 0 ≤ kataiPrimeRecip z := Finset.sum_nonneg fun p _ => by positivity
    rw [hDdef]; linarith
  have hnum : M * L ^ 2 ≤ maxRecipSum w := by
    have hsq : (L / 2) ^ 2 ≤ D ^ 2 := by nlinarith [hDhalf, hL1]
    have h1 : (z : ℝ) * (L / 2) ^ 2 ≤ (z : ℝ) * D ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hzR.le
    have h2 : (M + 1) * L ^ 2 ≤ (z : ℝ) * (L / 2) ^ 2 := by nlinarith [hzM, sq_nonneg L, hL1]
    have h3 : D ≤ L ^ 2 := by nlinarith [hDL, hL1]
    nlinarith [hkey, h1, h2, h3]
  rw [le_div_iff₀ (by positivity)]
  exact hnum

end NormalNumbers.CastingOut
