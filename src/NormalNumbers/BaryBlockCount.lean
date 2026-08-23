/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# W4 b-ary side — Becher–Yuhjtman Lemma 8 (lap-authored groundwork)

Counting bound for base-`b` blocks with large simple discrepancy
(B–Y Lemma 8 = Becher–Heiber–Slaman Lemma 2.5, adapted from Hardy–Wright
Theorem 148): for `0 ≤ ε ≤ 1/b`, the number of length-`k` blocks whose
count of some digit `s` deviates from `k/b` by at least `εk` is at most
`2·b^(k+1)·exp(−bε²k/6)`.

The proof here is a purely combinatorial Chernoff argument — no measure
theory, no calculus:

* `sum_exp_digitCount` — the generating identity
  `Σ_u exp(λ·count_s u) = (e^λ + (b−1))^k` over all blocks `u : Fin k → Fin b`
  (distribute the product over the sum, `Finset.sum_prod_piFinset`).
* `card_tilt_le` — the counting Markov step: on any block set where
  `λm ≤ λ·count`, `card · e^{λm} ≤ (e^λ + (b−1))^k`.
* exponential tilting at `λ = ±bε/2`, with the per-symbol bases controlled by
  `Real.exp_bound` (order-2 Taylor: `e^{±y} ≤ 1 ± y + (3/4)y²` for `|y| ≤ 1`)
  and `Real.add_one_le_exp`; the exponents combine to exactly `−bε²/6` per
  symbol on both tails.

The hypothesis is only `0 ≤ ε` and `bε ≤ 1`; B–Y additionally assume
`6/k ≤ ε`, which is not needed on this route.
-/

namespace NormalNumbers

open Finset Real

attribute [local instance] Classical.propDecidable

/-- Number of occurrences of the digit `s` in the length-`k` base-`b` block
`u`. -/
def digitCount {b k : ℕ} (s : Fin b) (u : Fin k → Fin b) : ℕ :=
  ∑ i, if u i = s then 1 else 0

/-- Generating identity for the exponential tilt of the digit count:
`Σ_u e^{λ·count_s(u)} = (e^λ + (b−1))^k`. -/
theorem sum_exp_digitCount {b k : ℕ} (s : Fin b) (lam : ℝ) :
    ∑ u : Fin k → Fin b, Real.exp (lam * (digitCount s u : ℝ))
      = (Real.exp lam + ((b : ℝ) - 1)) ^ k := by
  have hterm : ∀ u : Fin k → Fin b,
      Real.exp (lam * (digitCount s u : ℝ))
        = ∏ i, (if u i = s then Real.exp lam else 1) := by
    intro u
    rw [digitCount]
    push_cast
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : u i = s <;> simp [h]
  simp only [hterm]
  rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset
    (Finset.univ : Finset (Fin b)) (fun _ a => if a = s then Real.exp lam else 1)]
  have hsum : (∑ a : Fin b, if a = s then Real.exp lam else 1)
      = Real.exp lam + ((b : ℝ) - 1) := by
    have hsplit : ∀ a : Fin b, (if a = s then Real.exp lam else 1)
        = 1 + (if a = s then Real.exp lam - 1 else 0) := by
      intro a; by_cases h : a = s <;> simp [h]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ s, Finset.mem_univ, if_true,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  simp only [hsum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Counting Markov/Chernoff step: if `λm ≤ λ·count_s(u)` on a set of
blocks, its cardinality times `e^{λm}` is at most the full tilted sum. -/
theorem card_tilt_le {b k : ℕ} (s : Fin b) (lam m : ℝ)
    (P : (Fin k → Fin b) → Prop)
    (hP : ∀ u, P u → lam * m ≤ lam * (digitCount s u : ℝ)) :
    ((Finset.univ.filter P).card : ℝ) * Real.exp (lam * m)
      ≤ (Real.exp lam + ((b : ℝ) - 1)) ^ k := by
  calc ((Finset.univ.filter P).card : ℝ) * Real.exp (lam * m)
      = ∑ _u ∈ Finset.univ.filter P, Real.exp (lam * m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ Finset.univ.filter P, Real.exp (lam * (digitCount s u : ℝ)) :=
        Finset.sum_le_sum fun u hu =>
          Real.exp_le_exp.2 (hP u (Finset.mem_filter.1 hu).2)
    _ ≤ ∑ u : Fin k → Fin b, Real.exp (lam * (digitCount s u : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => (Real.exp_pos _).le
    _ = (Real.exp lam + ((b : ℝ) - 1)) ^ k := sum_exp_digitCount s lam

/-- Order-2 Taylor upper bound `e^{x/2} ≤ 1 + x/2 + x²/3` on `[0,1]`. -/
theorem exp_half_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp (x / 2) ≤ 1 + x / 2 + x ^ 2 / 3 := by
  have habs : |x / 2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.exp_bound habs (n := 2) (by norm_num)
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x / 2)] at h
  have hsum : ∑ m ∈ Finset.range 2, (x / 2) ^ m / m.factorial = 1 + x / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have := (abs_sub_le_iff.1 h).1
  nlinarith [sq_nonneg x]

/-- Order-2 Taylor upper bound `e^{−x/2} ≤ 1 − x/2 + x²/3` on `[0,1]`. -/
theorem exp_neg_half_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp (-(x / 2)) ≤ 1 - x / 2 + x ^ 2 / 3 := by
  have habs : |(-(x / 2))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by linarith)]; linarith
  have h := Real.exp_bound habs (n := 2) (by norm_num)
  rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ x / 2)] at h
  have hsum : ∑ m ∈ Finset.range 2, (-(x / 2)) ^ m / m.factorial
      = 1 - x / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum] at h
  have := (abs_sub_le_iff.1 h).1
  nlinarith [sq_nonneg x]

/-- Per-symbol base bound, upper tail: `e^{x/2} + (b−1) ≤ b·e^{(x/2+x²/3)/b}`. -/
theorem tilt_base_le_upper {b : ℕ} (hb : 1 ≤ b) {x : ℝ} (h0 : 0 ≤ x)
    (h1 : x ≤ 1) :
    Real.exp (x / 2) + ((b : ℝ) - 1)
      ≤ (b : ℝ) * Real.exp ((x / 2 + x ^ 2 / 3) / b) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hkey : 1 + (Real.exp (x / 2) - 1) / b
      ≤ Real.exp ((Real.exp (x / 2) - 1) / b) := by
    have := Real.add_one_le_exp ((Real.exp (x / 2) - 1) / b)
    linarith
  calc Real.exp (x / 2) + ((b : ℝ) - 1)
      = (b : ℝ) * (1 + (Real.exp (x / 2) - 1) / b) := by field_simp; ring
    _ ≤ (b : ℝ) * Real.exp ((Real.exp (x / 2) - 1) / b) := by
        exact mul_le_mul_of_nonneg_left hkey hbpos.le
    _ ≤ (b : ℝ) * Real.exp ((x / 2 + x ^ 2 / 3) / b) := by
        have hexp := exp_half_le h0 h1
        gcongr
        linarith

/-- Per-symbol base bound, lower tail:
`e^{−x/2} + (b−1) ≤ b·e^{(−x/2+x²/3)/b}`. -/
theorem tilt_base_le_lower {b : ℕ} (hb : 1 ≤ b) {x : ℝ} (h0 : 0 ≤ x)
    (h1 : x ≤ 1) :
    Real.exp (-(x / 2)) + ((b : ℝ) - 1)
      ≤ (b : ℝ) * Real.exp ((-(x / 2) + x ^ 2 / 3) / b) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hkey : 1 + (Real.exp (-(x / 2)) - 1) / b
      ≤ Real.exp ((Real.exp (-(x / 2)) - 1) / b) := by
    have := Real.add_one_le_exp ((Real.exp (-(x / 2)) - 1) / b)
    linarith
  calc Real.exp (-(x / 2)) + ((b : ℝ) - 1)
      = (b : ℝ) * (1 + (Real.exp (-(x / 2)) - 1) / b) := by field_simp; ring
    _ ≤ (b : ℝ) * Real.exp ((Real.exp (-(x / 2)) - 1) / b) := by
        exact mul_le_mul_of_nonneg_left hkey hbpos.le
    _ ≤ (b : ℝ) * Real.exp ((-(x / 2) + x ^ 2 / 3) / b) := by
        have hexp := exp_neg_half_le h0 h1
        gcongr
        linarith

/-- Chernoff upper tail: the number of length-`k` blocks with
`count_s ≥ k/b + εk` is at most `b^k·e^{−bε²k/6}`, for `0 ≤ ε ≤ 1/b`. -/
theorem card_upper_tail_le {b k : ℕ} (hb : 1 ≤ b) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεb : (b : ℝ) * ε ≤ 1) (s : Fin b) :
    ((Finset.univ.filter fun u : Fin k → Fin b =>
        (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ)).card : ℝ)
      ≤ (b : ℝ) ^ k * Real.exp (-((b : ℝ) * ε ^ 2 * k) / 6) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  set x : ℝ := (b : ℝ) * ε with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := hεb
  set lam : ℝ := x / 2 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set m : ℝ := (k : ℝ) / b + ε * k with hm
  have htilt := card_tilt_le (k := k) s lam m _
    (fun u hu => mul_le_mul_of_nonneg_left hu hlam0)
  have hbase := tilt_base_le_upper hb hx0 hx1
  have hpow : (Real.exp lam + ((b : ℝ) - 1)) ^ k
      ≤ ((b : ℝ) * Real.exp ((x / 2 + x ^ 2 / 3) / b)) ^ k := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    apply pow_le_pow_left₀ (by linarith [Real.exp_pos lam]) hbase
  have hexp_pos : (0 : ℝ) < Real.exp (lam * m) := Real.exp_pos _
  have hcard : ((Finset.univ.filter fun u : Fin k → Fin b =>
      (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ)).card : ℝ)
      ≤ ((b : ℝ) * Real.exp ((x / 2 + x ^ 2 / 3) / b)) ^ k
        * Real.exp (-(lam * m)) := by
    rw [← le_div_iff₀ hexp_pos] at htilt
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact htilt.trans (by gcongr)
  refine hcard.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 1
  have hmx : m = (k : ℝ) * (1 + x) / b := by
    rw [hm, hx]; field_simp
  rw [hlam, hmx, hx]
  field_simp
  ring_nf

/-- Chernoff lower tail: the number of length-`k` blocks with
`count_s ≤ k/b − εk` is at most `b^k·e^{−bε²k/6}`, for `0 ≤ ε ≤ 1/b`. -/
theorem card_lower_tail_le {b k : ℕ} (hb : 1 ≤ b) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεb : (b : ℝ) * ε ≤ 1) (s : Fin b) :
    ((Finset.univ.filter fun u : Fin k → Fin b =>
        (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k).card : ℝ)
      ≤ (b : ℝ) ^ k * Real.exp (-((b : ℝ) * ε ^ 2 * k) / 6) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  set x : ℝ := (b : ℝ) * ε with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := hεb
  set lam : ℝ := -(x / 2) with hlam
  have hlam0 : lam ≤ 0 := by rw [hlam]; simp; positivity
  set m : ℝ := (k : ℝ) / b - ε * k with hm
  have htilt := card_tilt_le (k := k) s lam m _
    (fun u hu => mul_le_mul_of_nonpos_left hu hlam0)
  have hbase := tilt_base_le_lower hb hx0 hx1
  have hpow : (Real.exp lam + ((b : ℝ) - 1)) ^ k
      ≤ ((b : ℝ) * Real.exp ((-(x / 2) + x ^ 2 / 3) / b)) ^ k := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    apply pow_le_pow_left₀ (by linarith [Real.exp_pos lam]) (by rw [hlam]; exact hbase)
  have hexp_pos : (0 : ℝ) < Real.exp (lam * m) := Real.exp_pos _
  have hcard : ((Finset.univ.filter fun u : Fin k → Fin b =>
      (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k).card : ℝ)
      ≤ ((b : ℝ) * Real.exp ((-(x / 2) + x ^ 2 / 3) / b)) ^ k
        * Real.exp (-(lam * m)) := by
    rw [← le_div_iff₀ hexp_pos] at htilt
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact htilt.trans (by gcongr)
  refine hcard.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 1
  have hmx : m = (k : ℝ) * (1 - x) / b := by
    rw [hm, hx]; field_simp
  rw [hlam, hmx, hx]
  field_simp
  ring_nf

/-- **Becher–Yuhjtman Lemma 8** (= BHS Lemma 2.5, from Hardy–Wright Thm 148),
in counting form: for `0 ≤ ε ≤ 1/b`, the number of length-`k` base-`b`
blocks in which some digit's count deviates from `k/b` by at least `εk`
(i.e. simple discrepancy `≥ ε`) is at most `2·b^(k+1)·e^{−bε²k/6}`.

Stronger than the paper statement: the hypothesis `6/k ≤ ε` is not needed. -/
theorem card_baryDiscrepancy_ge_le (b k : ℕ) (hb : 1 ≤ b) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεb : (b : ℝ) * ε ≤ 1) :
    ((Finset.univ.filter fun u : Fin k → Fin b =>
        ∃ s : Fin b, ε * k ≤ |(digitCount s u : ℝ) - k / b|).card : ℝ)
      ≤ 2 * (b : ℝ) ^ (k + 1) * Real.exp (-((b : ℝ) * ε ^ 2 * k) / 6) := by
  have hsub : (Finset.univ.filter fun u : Fin k → Fin b =>
      ∃ s : Fin b, ε * k ≤ |(digitCount s u : ℝ) - k / b|)
      ⊆ Finset.univ.biUnion fun s : Fin b =>
        (Finset.univ.filter fun u : Fin k → Fin b =>
          (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ))
        ∪ (Finset.univ.filter fun u : Fin k → Fin b =>
          (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k) := by
    intro u hu
    obtain ⟨s, hs⟩ := (Finset.mem_filter.1 hu).2
    rw [Finset.mem_biUnion]
    refine ⟨s, Finset.mem_univ s, ?_⟩
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs.1 hs with h | h
    · exact Or.inl ⟨Finset.mem_univ u, by linarith⟩
    · exact Or.inr ⟨Finset.mem_univ u, by linarith⟩
  have hcards : ((Finset.univ.filter fun u : Fin k → Fin b =>
      ∃ s : Fin b, ε * k ≤ |(digitCount s u : ℝ) - k / b|).card : ℝ)
      ≤ ∑ s : Fin b,
          (((Finset.univ.filter fun u : Fin k → Fin b =>
            (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ)).card : ℝ)
          + ((Finset.univ.filter fun u : Fin k → Fin b =>
            (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k).card : ℝ)) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin b)))
      (t := fun s : Fin b =>
        (Finset.univ.filter fun u : Fin k → Fin b =>
          (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ))
        ∪ (Finset.univ.filter fun u : Fin k → Fin b =>
          (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k))
    have h3 : ∀ s : Fin b,
        ((Finset.univ.filter fun u : Fin k → Fin b =>
          (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ))
        ∪ (Finset.univ.filter fun u : Fin k → Fin b =>
          (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k)).card
        ≤ (Finset.univ.filter fun u : Fin k → Fin b =>
            (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ)).card
          + (Finset.univ.filter fun u : Fin k → Fin b =>
            (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k).card :=
      fun s => Finset.card_union_le _ _
    calc ((Finset.univ.filter fun u : Fin k → Fin b =>
        ∃ s : Fin b, ε * k ≤ |(digitCount s u : ℝ) - k / b|).card : ℝ)
        ≤ ((Finset.univ.biUnion fun s : Fin b =>
            (Finset.univ.filter fun u : Fin k → Fin b =>
              (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ))
            ∪ (Finset.univ.filter fun u : Fin k → Fin b =>
              (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k)).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ((∑ s : Fin b,
            ((Finset.univ.filter fun u : Fin k → Fin b =>
              (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ))
            ∪ (Finset.univ.filter fun u : Fin k → Fin b =>
              (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k)).card : ℕ) : ℝ) := by
          exact_mod_cast h2
      _ ≤ _ := by
          push_cast
          exact Finset.sum_le_sum fun s _ => by exact_mod_cast h3 s
  refine hcards.trans ?_
  have hbound : ∀ s : Fin b,
      (((Finset.univ.filter fun u : Fin k → Fin b =>
        (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ)).card : ℝ)
      + ((Finset.univ.filter fun u : Fin k → Fin b =>
        (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k).card : ℝ))
      ≤ 2 * ((b : ℝ) ^ k * Real.exp (-((b : ℝ) * ε ^ 2 * k) / 6)) :=
    fun s => by
      have h1 := card_upper_tail_le (k := k) hb hε0 hεb s
      have h2 := card_lower_tail_le (k := k) hb hε0 hεb s
      linarith
  calc (∑ s : Fin b,
      (((Finset.univ.filter fun u : Fin k → Fin b =>
        (k : ℝ) / b + ε * k ≤ (digitCount s u : ℝ)).card : ℝ)
      + ((Finset.univ.filter fun u : Fin k → Fin b =>
        (digitCount s u : ℝ) ≤ (k : ℝ) / b - ε * k).card : ℝ)))
      ≤ ∑ _s : Fin b, 2 * ((b : ℝ) ^ k * Real.exp (-((b : ℝ) * ε ^ 2 * k) / 6)) :=
        Finset.sum_le_sum fun s _ => hbound s
    _ = 2 * (b : ℝ) ^ (k + 1) * Real.exp (-((b : ℝ) * ε ^ 2 * k) / 6) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          pow_succ]
        ring

end NormalNumbers
