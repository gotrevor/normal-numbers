import NormalNumbers.TwoPointGramSufficient

/-!
# The deficit identity: how phase separation cashes out as cancellation

Lap 19 reduced the leaf to a per-pair bound with relative saving `L(w)²/(2π(w))` over the trivial
bound.  Any arithmetic argument producing such a saving must convert a *qualitative* statement
("the summand takes noticeably different values on two sizeable sets of `m`") into a
*quantitative* one.  This file proves the exact conversion, for unimodular summands:

    ‖Σ_{m ∈ S} f(m)‖²  =  |S|²  −  ½ Σ_{m,m' ∈ S} ‖f(m) − f(m')‖² .

The triangle inequality `‖Σ‖ ≤ |S|` is the case where all values coincide; every pair of indices
whose values differ subtracts exactly `‖f(m) − f(m')‖²` from the square.  Consequences:

* `sum_unimodular_deficit` — the identity;
* `norm_sum_le_of_separated` — if `A, B ⊆ S` are disjoint and `‖f(m) − f(m')‖ ≥ d` for all
  `m ∈ A`, `m' ∈ B`, then `‖Σ_S f‖² ≤ |S|² − |A||B|d²`;
* **`twoPointTruncSum_saving`** — the per-pair target of lap 19 in usable form: two blocks of
  relative size `α` with phase separation `d` give
  `‖T_{p,q}(N)‖ ≤ (1 − α²d²/2)·min(⌊N/p⌋,⌊N/q⌋)`.

So the remaining arithmetic question is sharp and finite-dimensional: exhibit, for a pair of
primes `p ≠ q`, two sets of `m` of positive relative density on which
`ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W_{p,q}(m)` points in separated directions.  The required saving
`L(w)²/(2π(w))` then needs `α²d² ≍ L(w)²/π(w)`, i.e. densities and separations that may both
degrade slowly with `w` — a much weaker demand than equidistribution.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

lemma normSq_sub_unimodular (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ^ 2 = 2 - 2 * (z * (starRingEnd ℂ) w).re := by
  have h := Complex.normSq_sub z w
  rw [← Complex.normSq_eq_norm_sq, h, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    hz, hw]
  ring

/-- **THE DEFICIT IDENTITY.** -/
theorem sum_unimodular_deficit (S : Finset ℕ) (f : ℕ → ℂ) (hf : ∀ m ∈ S, ‖f m‖ = 1) :
    ‖∑ m ∈ S, f m‖ ^ 2
      = ((S.card : ℝ)) ^ 2 - (1/2) * ∑ m ∈ S, ∑ m' ∈ S, ‖f m - f m'‖ ^ 2 := by
  classical
  set T : ℂ := ∑ m ∈ S, f m with hT
  have hTsq : ‖T‖ ^ 2 = (∑ m ∈ S, ∑ m' ∈ S, (f m * (starRingEnd ℂ) (f m'))).re := by
    have : ((‖T‖ ^ 2 : ℝ) : ℂ) = ∑ m ∈ S, ∑ m' ∈ S, (f m * (starRingEnd ℂ) (f m')) := by
      rw [normSq_cast, hT, map_sum, Finset.sum_mul_sum]
    rw [← Complex.ofReal_re ((‖T‖ ^ 2 : ℝ)), this]
  have hdef : ∑ m ∈ S, ∑ m' ∈ S, ‖f m - f m'‖ ^ 2
      = 2 * ((S.card : ℝ)) ^ 2 - 2 * ‖T‖ ^ 2 := by
    have hterm : ∀ m ∈ S, ∑ m' ∈ S, ‖f m - f m'‖ ^ 2
        = 2 * (S.card : ℝ) - 2 * (∑ m' ∈ S, (f m * (starRingEnd ℂ) (f m'))).re := by
      intro m hm
      have h : ∀ m' ∈ S, ‖f m - f m'‖ ^ 2
          = 2 - 2 * (f m * (starRingEnd ℂ) (f m')).re := fun m' hm' =>
        normSq_sub_unimodular (f m) (f m') (hf m hm) (hf m' hm')
      rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
        ← Complex.re_sum]
      simp [nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
      ← Complex.re_sum, ← hTsq]
    simp [nsmul_eq_mul]
    ring
  rw [hdef]; ring

/-- Separation on two disjoint blocks forces cancellation. -/
theorem norm_sum_le_of_separated (S A B : Finset ℕ) (f : ℕ → ℂ) (hf : ∀ m ∈ S, ‖f m‖ = 1)
    (hA : A ⊆ S) (hB : B ⊆ S) (hAB : Disjoint A B) (d : ℝ) (hd : 0 ≤ d)
    (hsep : ∀ m ∈ A, ∀ m' ∈ B, d ≤ ‖f m - f m'‖) :
    ‖∑ m ∈ S, f m‖ ^ 2 ≤ ((S.card : ℝ)) ^ 2 - (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by
  classical
  have hid := sum_unimodular_deficit S f hf
  have hnn : ∀ m ∈ S, ∀ m' ∈ S, (0:ℝ) ≤ ‖f m - f m'‖ ^ 2 := fun _ _ _ _ => by positivity
  -- the `A × B` and `B × A` pairs alone contribute `2|A||B|d²`
  have hAB' : ∑ m ∈ A, ∑ m' ∈ B, ‖f m - f m'‖ ^ 2 ≥ (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by
    calc ∑ m ∈ A, ∑ m' ∈ B, ‖f m - f m'‖ ^ 2
        ≥ ∑ _m ∈ A, ∑ _m' ∈ B, d ^ 2 := by
          refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => ?_
          have := hsep m hm m' hm'
          nlinarith [this, hd]
      _ = (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [nsmul_eq_mul]; ring
  have hBA' : ∑ m ∈ B, ∑ m' ∈ A, ‖f m - f m'‖ ^ 2 ≥ (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by
    calc ∑ m ∈ B, ∑ m' ∈ A, ‖f m - f m'‖ ^ 2
        ≥ ∑ _m ∈ B, ∑ _m' ∈ A, d ^ 2 := by
          refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => ?_
          have := hsep m' hm' m hm
          rw [← norm_neg, neg_sub] at this
          nlinarith [this, hd]
      _ = (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [nsmul_eq_mul]; ring
  -- and the full double sum dominates those two blocks
  have hfull : ∑ m ∈ A, ∑ m' ∈ B, ‖f m - f m'‖ ^ 2 + ∑ m ∈ B, ∑ m' ∈ A, ‖f m - f m'‖ ^ 2
      ≤ ∑ m ∈ S, ∑ m' ∈ S, ‖f m - f m'‖ ^ 2 := by
    have hrow : ∀ m ∈ S, (if m ∈ A then ∑ m' ∈ B, ‖f m - f m'‖ ^ 2 else 0)
        + (if m ∈ B then ∑ m' ∈ A, ‖f m - f m'‖ ^ 2 else 0)
        ≤ ∑ m' ∈ S, ‖f m - f m'‖ ^ 2 := by
      intro m hm
      by_cases hmA : m ∈ A
      · have hmB : m ∉ B := Finset.disjoint_left.mp hAB hmA
        rw [if_pos hmA, if_neg hmB, add_zero]
        exact Finset.sum_le_sum_of_subset_of_nonneg hB (fun m' hm' _ => by positivity)
      · rw [if_neg hmA, zero_add]
        by_cases hmB : m ∈ B
        · rw [if_pos hmB]
          exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun m' hm' _ => by positivity)
        · rw [if_neg hmB]
          exact Finset.sum_nonneg fun m' _ => by positivity
    have hsum := Finset.sum_le_sum hrow
    rw [Finset.sum_add_distrib] at hsum
    have e1 : ∑ m ∈ S, (if m ∈ A then ∑ m' ∈ B, ‖f m - f m'‖ ^ 2 else 0)
        = ∑ m ∈ A, ∑ m' ∈ B, ‖f m - f m'‖ ^ 2 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hA]
    have e2 : ∑ m ∈ S, (if m ∈ B then ∑ m' ∈ A, ‖f m - f m'‖ ^ 2 else 0)
        = ∑ m ∈ B, ∑ m' ∈ A, ‖f m - f m'‖ ^ 2 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]
    rw [e1, e2] at hsum
    exact hsum
  have hd2 : (0:ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by positivity
  rw [hid]
  linarith [hAB', hBA', hfull]

/-- **THE PER-PAIR TARGET IN USABLE FORM.**  Two blocks of relative size `α` with phase
separation `d` inside the truncated range give the relative saving `α²d²/2`. -/
theorem twoPointTruncSum_saving (b p q : ℕ) (t : ℝ) (N : ℕ) (A B : Finset ℕ) (α d : ℝ)
    (hA : A ⊆ Finset.Ioc 0 (min (N / p) (N / q)))
    (hB : B ⊆ Finset.Ioc 0 (min (N / p) (N / q)))
    (hAB : Disjoint A B) (hα : 0 ≤ α) (hd : 0 ≤ d) (hx : α ^ 2 * d ^ 2 ≤ 1)
    (hcardA : α * ((min (N / p) (N / q) : ℕ) : ℝ) ≤ (A.card : ℝ))
    (hcardB : α * ((min (N / p) (N / q) : ℕ) : ℝ) ≤ (B.card : ℝ))
    (hsep : ∀ m ∈ A, ∀ m' ∈ B, d ≤ ‖(twoPointFactor b p q t m * peelWeight b p q t m)
      - (twoPointFactor b p q t m' * peelWeight b p q t m')‖) :
    ‖twoPointTruncSum b p q t N‖
      ≤ (1 - α ^ 2 * d ^ 2 / 2) * ((min (N / p) (N / q) : ℕ) : ℝ) := by
  classical
  set S := Finset.Ioc 0 (min (N / p) (N / q)) with hS
  set f : ℕ → ℂ := fun m => twoPointFactor b p q t m * peelWeight b p q t m with hfdef
  have hf : ∀ m ∈ S, ‖f m‖ = 1 := by
    intro m _
    rw [hfdef, norm_mul, norm_twoPointFactor, norm_peelWeight, mul_one]
  have hcardS : (S.card : ℝ) = ((min (N / p) (N / q) : ℕ) : ℝ) := by
    rw [hS, Nat.card_Ioc]; simp
  have hM : (0:ℝ) ≤ ((min (N / p) (N / q) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hkey := norm_sum_le_of_separated S A B f hf hA hB hAB d hd hsep
  rw [hcardS] at hkey
  set M := ((min (N / p) (N / q) : ℕ) : ℝ) with hMdef
  have hAB2 : α ^ 2 * M ^ 2 * d ^ 2 ≤ (A.card : ℝ) * (B.card : ℝ) * d ^ 2 := by
    have h1 : 0 ≤ α * M := by positivity
    have h2 : (α * M) * (α * M) ≤ (A.card : ℝ) * (B.card : ℝ) :=
      mul_le_mul hcardA hcardB h1 (by positivity)
    nlinarith [h2, sq_nonneg d, hd]
  have hsq : ‖∑ m ∈ S, f m‖ ^ 2 ≤ (M * (1 - α ^ 2 * d ^ 2 / 2)) ^ 2 := by
    nlinarith [hkey, hAB2, hM, sq_nonneg (α ^ 2 * d ^ 2), hx]
  have hTnn : (0:ℝ) ≤ ‖∑ m ∈ S, f m‖ := norm_nonneg _
  have hRnn : (0:ℝ) ≤ M * (1 - α ^ 2 * d ^ 2 / 2) := by nlinarith [hM, hx, sq_nonneg (α*d)]
  have hfinal : ‖∑ m ∈ S, f m‖ ≤ M * (1 - α ^ 2 * d ^ 2 / 2) := by
    nlinarith [hsq, hTnn, hRnn]
  calc ‖twoPointTruncSum b p q t N‖ = ‖∑ m ∈ S, f m‖ := by rw [twoPointTruncSum, hS, hfdef]
    _ ≤ M * (1 - α ^ 2 * d ^ 2 / 2) := hfinal
    _ = (1 - α ^ 2 * d ^ 2 / 2) * M := by ring

end NormalNumbers.CastingOut
