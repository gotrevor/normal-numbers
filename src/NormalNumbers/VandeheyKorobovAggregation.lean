/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovReduction

/-!
# Gcd-class aggregation in Vandehey's differencing step

This file packages the passage on pp. 12--13 of Vandehey's proof of Proposition 4.1
which partitions the shifted correlations according to `gcd(i,n)`.  Lemma 4.3 then
controls every fiber.  Keeping this combinatorial passage separate avoids mixing the
finite-set bookkeeping with the later real-power estimates.
-/

namespace NormalNumbers.VandeheyKorobov

open Finset

/-- Partition a finite interval exactly by the possible values of `gcd(i,n)`.
The nonzero hypothesis ensures that every gcd belongs to `n.divisors`. -/
theorem sum_Ico_by_gcd (n X : ℕ) (hn : n ≠ 0) (F : ℕ → ℝ) :
    (∑ i ∈ Ico 1 X, F (Nat.gcd i n)) =
      ∑ d ∈ n.divisors, ∑ i ∈ (Ico 1 X).filter (fun i => Nat.gcd i n = d), F d := by
  have hmaps : (Ico 1 X : Set ℕ).MapsTo (fun i => Nat.gcd i n) n.divisors := by
    intro i hi
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right i n, hn⟩
  have h := Finset.sum_fiberwise_of_maps_to hmaps (fun i => F (Nat.gcd i n))
  calc
    (∑ i ∈ Ico 1 X, F (Nat.gcd i n)) =
        ∑ d ∈ n.divisors,
          ∑ i ∈ (Ico 1 X).filter (fun i => Nat.gcd i n = d), F (Nat.gcd i n) := h.symm
    _ = ∑ d ∈ n.divisors,
          ∑ i ∈ (Ico 1 X).filter (fun i => Nat.gcd i n = d), F d := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/-- Vandehey's Lemma 4.3 summed against an arbitrary nonnegative gcd-class weight.
This is the precise aggregation inequality used for the shifted correlations in
Proposition 4.1. -/
theorem sum_Ico_gcd_weight_le
    (n X s : ℕ) (hn : n ≠ 0) (hs : n.primeFactors.card ≤ s)
    (F : ℕ → ℝ) (hF : ∀ d ∈ n.divisors, 0 ≤ F d) :
    (∑ i ∈ Ico 1 X, F (Nat.gcd i n)) ≤
      ∑ d ∈ n.divisors,
        ((X : ℝ) / n * (n / d).totient + (2 : ℝ) ^ s) * F d := by
  rw [sum_Ico_by_gcd n X hn F]
  apply Finset.sum_le_sum
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hcount := gcd_Ico_count_le_two_pow n d X s hn hdvd hs
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcount (hF d hd)

/-- A slightly coarser but algebraically useful form of `sum_Ico_gcd_weight_le`:
the totient in the main term is replaced by `n/d`.  After the divisor involution
`d ↦ n/d`, its first sum is exactly the `d^(1+α)` or `d^(1-δ)` sum on
page 13 of the paper, while the second is its `2^s` error term. -/
theorem sum_Ico_gcd_weight_le_split
    (n X s : ℕ) (hn : n ≠ 0) (hs : n.primeFactors.card ≤ s)
    (F : ℕ → ℝ) (hF : ∀ d ∈ n.divisors, 0 ≤ F d) :
    (∑ i ∈ Ico 1 X, F (Nat.gcd i n)) ≤
      (X : ℝ) / n * ∑ d ∈ n.divisors, (n / d : ℕ) * F d +
        (2 : ℝ) ^ s * ∑ d ∈ n.divisors, F d := by
  refine (sum_Ico_gcd_weight_le n X s hn hs F hF).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have htot : ((n / d).totient : ℝ) ≤ (n / d : ℕ) := by
    exact_mod_cast Nat.totient_le (n / d)
  have hX : 0 ≤ (X : ℝ) / n := by positivity
  have hpow : 0 ≤ (2 : ℝ) ^ s := by positivity
  have hFd : 0 ≤ F d := hF d hd
  calc
    ((X : ℝ) / n * (n / d).totient + (2 : ℝ) ^ s) * F d =
        ((X : ℝ) / n * (n / d).totient) * F d + (2 : ℝ) ^ s * F d := by ring
    _ ≤ ((X : ℝ) / n * (n / d : ℕ)) * F d + (2 : ℝ) ^ s * F d := by
      gcongr
    _ = (X : ℝ) / n * ((n / d : ℕ) * F d) + (2 : ℝ) ^ s * F d := by ring

end NormalNumbers.VandeheyKorobov
