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

/-- The sharp-cutoff form of `sum_Ico_gcd_weight_le`.  Retaining `X - 1`
in the main term is essential when `Ico 1 X` represents the shifts satisfying
`i * τ < N`, because then `X` is a ceiling while `X - 1 < N / τ`. -/
theorem sum_Ico_gcd_weight_le_sub_one
    (n X s : ℕ) (hn : n ≠ 0) (hs : n.primeFactors.card ≤ s)
    (F : ℕ → ℝ) (hF : ∀ d ∈ n.divisors, 0 ≤ F d) :
    (∑ i ∈ Ico 1 X, F (Nat.gcd i n)) ≤
      ∑ d ∈ n.divisors,
        (((X - 1 : ℕ) : ℝ) / n * (n / d).totient + (2 : ℝ) ^ s) * F d := by
  rw [sum_Ico_by_gcd n X hn F]
  apply Finset.sum_le_sum
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hcount := gcd_Ico_count_le_sub_one_two_pow n d X s hn hdvd hs
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

/-- The split main/error form of the sharp-cutoff aggregation theorem. -/
theorem sum_Ico_gcd_weight_le_split_sub_one
    (n X s : ℕ) (hn : n ≠ 0) (hs : n.primeFactors.card ≤ s)
    (F : ℕ → ℝ) (hF : ∀ d ∈ n.divisors, 0 ≤ F d) :
    (∑ i ∈ Ico 1 X, F (Nat.gcd i n)) ≤
      ((X - 1 : ℕ) : ℝ) / n * ∑ d ∈ n.divisors, (n / d : ℕ) * F d +
        (2 : ℝ) ^ s * ∑ d ∈ n.divisors, F d := by
  refine (sum_Ico_gcd_weight_le_sub_one n X s hn hs F hF).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have htot : ((n / d).totient : ℝ) ≤ (n / d : ℕ) := by
    exact_mod_cast Nat.totient_le (n / d)
  have hX : 0 ≤ ((X - 1 : ℕ) : ℝ) / n := by positivity
  have hpow : 0 ≤ (2 : ℝ) ^ s := by positivity
  have hFd : 0 ≤ F d := hF d hd
  calc
    (((X - 1 : ℕ) : ℝ) / n * (n / d).totient + (2 : ℝ) ^ s) * F d =
        (((X - 1 : ℕ) : ℝ) / n * (n / d).totient) * F d +
          (2 : ℝ) ^ s * F d := by ring
    _ ≤ (((X - 1 : ℕ) : ℝ) / n * (n / d : ℕ)) * F d +
          (2 : ℝ) ^ s * F d := by
      gcongr
    _ = ((X - 1 : ℕ) : ℝ) / n * ((n / d : ℕ) * F d) +
          (2 : ℝ) ^ s * F d := by ring

/-- Multiplying a positive natural base by one more real power increments
the exponent. -/
lemma natCast_mul_rpow (q : ℕ) (hq : q ≠ 0) (x : ℝ) :
    (q : ℝ) * (q : ℝ) ^ x = (q : ℝ) ^ (1 + x) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  conv_lhs =>
    lhs
    rw [← Real.rpow_one q]
  exact (Real.rpow_add hqR 1 x).symm

/-- The page-13 divisor-sum estimate after Lemmas 4.2 and 4.3.

`U` and `V` stand for the two powers of the correlation length.  The
complementary divisor `n / gcd(i,n)` is the reduced denominator.  This theorem
keeps the sharp `X - 1` cutoff and collapses all four divisor sums to the
corresponding `C_{P,x}` factors. -/
theorem sum_Ico_gcd_two_rpow_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : n ≠ 0) (hsupp : n.primeFactors ⊆ P)
    (X s : ℕ) (hs : n.primeFactors.card ≤ s)
    (A B U V α δ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (∑ i ∈ Ico 1 X,
        (A * ((n / Nat.gcd i n : ℕ) : ℝ) ^ α * U +
          B * ((n / Nat.gcd i n : ℕ) : ℝ) ^ (-δ) * V)) ≤
      ((X - 1 : ℕ) : ℝ) / n *
          (A * U * (Literature.VandeheyDiff.cP P (1 + α) * (n : ℝ) ^ (1 + α)) +
            B * V * (Literature.VandeheyDiff.cP P (1 - δ) * (n : ℝ) ^ (1 - δ))) +
        (2 : ℝ) ^ s *
          (A * U * (Literature.VandeheyDiff.cP P α * (n : ℝ) ^ α) +
            B * V * Literature.VandeheyDiff.cP P δ) := by
  let F : ℕ → ℝ := fun d =>
    A * ((n / d : ℕ) : ℝ) ^ α * U + B * ((n / d : ℕ) : ℝ) ^ (-δ) * V
  have hF : ∀ d ∈ n.divisors, 0 ≤ F d := by
    intro d hd
    dsimp [F]
    positivity
  have hagg := sum_Ico_gcd_weight_le_split_sub_one n X s hn hs F hF
  have hmainEq :
      (∑ d ∈ n.divisors, (n / d : ℕ) * F d) =
        A * U * ∑ d ∈ n.divisors, (d : ℝ) ^ (1 + α) +
          B * V * ∑ d ∈ n.divisors, (d : ℝ) ^ (1 - δ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [← Nat.sum_div_divisors n (fun d : ℕ =>
      A * U * (d : ℝ) ^ (1 + α) + B * V * (d : ℝ) ^ (1 - δ))]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
    have hqpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hdpos
    dsimp [F]
    calc
      ((n / d : ℕ) : ℝ) *
          (A * ((n / d : ℕ) : ℝ) ^ α * U +
            B * ((n / d : ℕ) : ℝ) ^ (-δ) * V) =
          A * U * (((n / d : ℕ) : ℝ) * ((n / d : ℕ) : ℝ) ^ α) +
            B * V * (((n / d : ℕ) : ℝ) * ((n / d : ℕ) : ℝ) ^ (-δ)) := by ring
      _ = A * U * ((n / d : ℕ) : ℝ) ^ (1 + α) +
            B * V * ((n / d : ℕ) : ℝ) ^ (1 - δ) := by
        rw [natCast_mul_rpow (n / d) hqpos.ne' α,
          natCast_mul_rpow (n / d) hqpos.ne' (-δ)]
        congr 2 <;> ring
  have herrorEq :
      (∑ d ∈ n.divisors, F d) =
        A * U * ∑ d ∈ n.divisors, (d : ℝ) ^ α +
          B * V * ∑ d ∈ n.divisors, (d : ℝ) ^ (-δ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [← Nat.sum_div_divisors n (fun d : ℕ =>
      A * U * (d : ℝ) ^ α + B * V * (d : ℝ) ^ (-δ))]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [F]
    ring
  have hmain :
      (∑ d ∈ n.divisors, (n / d : ℕ) * F d) ≤
        A * U * (Literature.VandeheyDiff.cP P (1 + α) * (n : ℝ) ^ (1 + α)) +
          B * V * (Literature.VandeheyDiff.cP P (1 - δ) * (n : ℝ) ^ (1 - δ)) := by
    rw [hmainEq]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (sum_divisors_rpow_le_cP_mul P hP hn hsupp (by linarith))
        (mul_nonneg hA hU)
    · exact mul_le_mul_of_nonneg_left
        (sum_divisors_rpow_le_cP_mul P hP hn hsupp (by linarith))
        (mul_nonneg hB hV)
  have herror :
      (∑ d ∈ n.divisors, F d) ≤
        A * U * (Literature.VandeheyDiff.cP P α * (n : ℝ) ^ α) +
          B * V * Literature.VandeheyDiff.cP P δ := by
    rw [herrorEq]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (sum_divisors_rpow_le_cP_mul P hP hn hsupp hα) (mul_nonneg hA hU)
    · exact mul_le_mul_of_nonneg_left
        (sum_divisors_rpow_neg_le_cP P hP hn hsupp hδ) (mul_nonneg hB hV)
  refine hagg.trans ?_
  dsimp [F] at hagg ⊢
  exact add_le_add
    (mul_le_mul_of_nonneg_left hmain (by positivity))
    (mul_le_mul_of_nonneg_left herror (by positivity))

/-- `sum_Ico_gcd_two_rpow_le` with the integral endpoint replaced by any
larger real cutoff.  Proposition 4.1 uses `Y = N / τ`, justified by
`natCast_ceilDiv_sub_one_le_div`. -/
theorem sum_Ico_gcd_two_rpow_le_of_cutoff
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : n ≠ 0) (hsupp : n.primeFactors ⊆ P)
    (X s : ℕ) (hs : n.primeFactors.card ≤ s)
    (A B U V α δ Y : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcut : (((X - 1 : ℕ) : ℝ)) ≤ Y) :
    (∑ i ∈ Ico 1 X,
        (A * ((n / Nat.gcd i n : ℕ) : ℝ) ^ α * U +
          B * ((n / Nat.gcd i n : ℕ) : ℝ) ^ (-δ) * V)) ≤
      Y / n *
          (A * U * (Literature.VandeheyDiff.cP P (1 + α) * (n : ℝ) ^ (1 + α)) +
            B * V * (Literature.VandeheyDiff.cP P (1 - δ) * (n : ℝ) ^ (1 - δ))) +
        (2 : ℝ) ^ s *
          (A * U * (Literature.VandeheyDiff.cP P α * (n : ℝ) ^ α) +
            B * V * Literature.VandeheyDiff.cP P δ) := by
  have hbase := sum_Ico_gcd_two_rpow_le P hP hn hsupp X s hs A B U V α δ
    hA hB hU hV hα hδ hδ1
  have hc1a : 0 < Literature.VandeheyDiff.cP P (1 + α) :=
    cP_pos P hP (by linarith)
  have hc1d : 0 < Literature.VandeheyDiff.cP P (1 - δ) :=
    cP_pos P hP (by linarith)
  have hmain0 :
      0 ≤ A * U * (Literature.VandeheyDiff.cP P (1 + α) * (n : ℝ) ^ (1 + α)) +
        B * V * (Literature.VandeheyDiff.cP P (1 - δ) * (n : ℝ) ^ (1 - δ)) := by
    positivity
  have hcoef : ((X - 1 : ℕ) : ℝ) / n ≤ Y / n :=
    div_le_div_of_nonneg_right hcut (by positivity)
  exact hbase.trans (add_le_add (mul_le_mul_of_nonneg_right hcoef hmain0) le_rfl)

end NormalNumbers.VandeheyKorobov
