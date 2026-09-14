/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyMTowerBig

/-!
# The marched ladder, step 2: the **harmonic sums** at the marched small-prime cutoff

`G4ScheduleHarmonic` proves the two Mertens bounds for the *implemented* cutoff
`R K = 2^{2^{m₁ K}}`.  The `m₁`-march replaces it by `Rm K j = 2^{2^{mm₁ K j}}`, so the same two
bounds are needed with `m₁ K` replaced by `mm₁ K j`.

Rather than copy the proofs a second time, this module states them **generically in the
exponent**: for any `e`, with cutoff `2^{2^e}`,

* `sum_inv_smallPrimes_ge_gen` : `e·log 2 − 21K² − 4 ≤ ∑_{p ∈ sm} 1/p`;
* `sum_inv_smallPrimes_le_gen` : `∑_{p ∈ sm} 1/p ≤ 3e + 5`.

`e = m₁ K` recovers `G4ScheduleHarmonic`'s statements and `e = mm₁ K j` is what the march needs
(`sum_inv_smallPrimes_ge_m`, `sum_inv_smallPrimes_le_m`).  Nothing in either proof used anything
about `m₁ K` beyond its being a natural number, which is the audit's claim that the cone
constrains `m₁` only from below.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.PrimeLambert

variable {K e : ℕ}

lemma log_Rgen (e : ℕ) : Real.log ((2 ^ 2 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ e * Real.log 2 := by
  push_cast; rw [Real.log_pow]; push_cast; ring

lemma log_log_Rgen_ge (e : ℕ) :
    (e : ℝ) * Real.log 2 - 1 ≤ Real.log (Real.log ((2 ^ 2 ^ e : ℕ) : ℝ)) := by
  rw [log_Rgen, Real.log_mul (by positivity) (Real.log_pos (by norm_num)).ne', Real.log_pow]
  have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h2 : Real.log (1 / 2) ≤ Real.log (Real.log 2) := by
    apply Real.log_le_log (by norm_num)
    linarith [Real.log_two_gt_d9]
  have h3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  linarith

lemma two_le_two_pow_two_pow (e : ℕ) : 2 ≤ (2 : ℕ) ^ 2 ^ e :=
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ 2 ^ e := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

/-- **Lower bound, generic in the cutoff exponent.** -/
theorem sum_inv_smallPrimes_ge_gen {Rg : ℕ} (hK : 100 ≤ K) (e : ℕ) (hRg : Rg = 2 ^ 2 ^ e) :
    (e : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ smallPrimes Rg (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hR2 : 2 ≤ Rg := hRg ▸ two_le_two_pow_two_pow e
  have hM := log_log_le_sum_inv_primesBelow (Rg + 1) (by omega)
  have hRr : (2 : ℝ) ≤ (Rg : ℝ) := by exact_mod_cast hR2
  have hlogR : 0 < Real.log (Rg : ℝ) := Real.log_pos (by linarith)
  have hmono : Real.log (Real.log (Rg : ℝ)) ≤ Real.log (Real.log ((Rg + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log hlogR
    apply Real.log_le_log (by linarith)
    push_cast; linarith
  have hlow : (e : ℝ) * Real.log 2 - 1 ≤ Real.log (Real.log (Rg : ℝ)) := by
    rw [hRg]; exact log_log_Rgen_ge e
  have hsplit := Finset.sum_filter_add_sum_filter_not ((Rg + 1).primesBelow)
    (fun p => p ∣ G.P₀) (fun p => (p : ℝ)⁻¹)
  have hexcl := sum_inv_excluded_le hK Rg
  unfold smallPrimes
  linarith

/-- **Upper bound, generic in the cutoff exponent.** -/
theorem sum_inv_smallPrimes_le_gen {Rg : ℕ} (hK : 100 ≤ K) (e : ℕ) (hRg : Rg = 2 ^ 2 ^ e) :
    ∑ p ∈ smallPrimes Rg (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
      ≤ 3 * (e : ℝ) + 5 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hR2 : 2 ≤ Rg := hRg ▸ two_le_two_pow_two_pow e
  have hsub : smallPrimes Rg G.P₀ ⊆ (Rg + 1).primesBelow := Finset.filter_subset _ _
  have h1 : ∑ p ∈ smallPrimes Rg G.P₀, (p : ℝ)⁻¹ ≤ ∑ p ∈ (Rg + 1).primesBelow, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hsplit : ∑ p ∈ (Rg + 1).primesBelow, (p : ℝ)⁻¹
      = ∑ p ∈ (Rg + 1).primesBelow.filter (fun p => 2 < p), (p : ℝ)⁻¹
        + ∑ p ∈ (Rg + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdy := sum_inv_primes_Ioc_le (R := 2) (Y := Rg) le_rfl hR2
  have hlogR : Nat.log 2 Rg = 2 ^ e := by rw [hRg]; exact Nat.log_pow (by norm_num) _
  have hlog2 : Nat.log 2 2 = 1 := by simpa using Nat.log_pow (by norm_num : 1 < 2) 1
  rw [hlogR, hlog2] at hdy
  push_cast at hdy
  rw [Real.log_pow, Real.log_one] at hdy
  have hl2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hm0 : (0 : ℝ) ≤ (e : ℝ) := by positivity
  have hA : ∑ p ∈ (Rg + 1).primesBelow.filter (fun p => 2 < p), (p : ℝ)⁻¹
      ≤ 4 + 3 * (e : ℝ) := by nlinarith
  have hB : ∑ p ∈ (Rg + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹ ≤ 1 / 2 := by
    have hsub2 : (Rg + 1).primesBelow.filter (fun p => ¬ 2 < p) ⊆ {2} := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      have := hp.1.2.two_le
      rw [Finset.mem_singleton]; omega
    calc ∑ p ∈ (Rg + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹
        ≤ ∑ p ∈ ({2} : Finset ℕ), (p : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity)
      _ = 1 / 2 := by simp
  linarith

/-! ### The marched instances -/

lemma Rm_eq (K j : ℕ) : Rm K j = 2 ^ 2 ^ mm₁ K j := rfl

theorem sum_inv_smallPrimes_ge_m {K : ℕ} (hK : 100 ≤ K) (j : ℕ) :
    (mm₁ K j : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ :=
  sum_inv_smallPrimes_ge_gen hK (mm₁ K j) rfl

theorem sum_inv_smallPrimes_le_m {K : ℕ} (hK : 100 ≤ K) (j : ℕ) :
    ∑ p ∈ smallPrimes (Rm K j) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹
      ≤ 3 * (mm₁ K j : ℝ) + 5 :=
  sum_inv_smallPrimes_le_gen hK (mm₁ K j) rfl

end Sched

end NormalNumbers.G4
