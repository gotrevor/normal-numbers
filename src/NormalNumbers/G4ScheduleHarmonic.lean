/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleBig
import NormalNumbers.G4Mertens
import NormalNumbers.G4MediumPrimes

/-!
# G4 §5: the harmonic mass of the small primes, and the subset count

For the explicit schedule (`R = 2^{2^{m₁}}`, `sm = smallPrimes R P₀`):

* **lower** (`sum_inv_smallPrimes_ge`): `∑_{p∈sm} 1/p ≥ m₁ log 2 − 21K² − 4`.  Lower Mertens
  (`log_log_le_sum_inv_primesBelow`) gives `log log R − 1`, and the primes dividing `P₀` cost
  at most `log ω(P₀) + 1 ≤ log(2·logP₀Nat) + 1 ≤ 21K² + 2` because `2^{ω(P₀)} ≤ P₀`
  (`two_pow_omega_le_card_divisors`) — the crude `ω(P₀) ≤ P₀` would lose everything.
* **upper** (`sum_inv_smallPrimes_le`): `∑_{p∈sm} 1/p ≤ 3m₁ + 5`, from the dyadic Chebyshev
  bound `sum_inv_primes_Ioc_le` (constant 4).  The crude `log R + 1` would make the §4C
  error terms (b),(c) diverge.
* **count** (`card_small_subsets_le`): `#{T' ⊆ sm : T' ≠ ∅, |T'| ≤ Mc} ≤ Mc·(|sm|+1)^{Mc}`,
  from `choose ≤ n^k`; the crude `2^{|sm|}` is `≫ X`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

/-! ### `ω(n) log 2 ≤ log n` -/

lemma omega_mul_log_two_le {n : ℕ} (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have h1 := two_pow_omega_le_card_divisors hn
  have h2 := Nat.card_divisors_le_self n
  have h3 : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast h1.trans h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc (n.primeFactors.card : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n.primeFactors.card) := by
        rw [Real.log_pow]
    _ ≤ Real.log n := Real.log_le_log (by positivity) h3

/-! ### The excluded primes -/

/-- The primes `≤ R` dividing `P₀` have harmonic mass `≤ 21K² + 2`. -/
lemma sum_inv_excluded_le {K : ℕ} (hK : 100 ≤ K) (R : ℕ) :
    ∑ p ∈ (R + 1).primesBelow.filter (fun p => p ∣ (gridOf K (N K) (by omega)).P₀), (p : ℝ)⁻¹
      ≤ 21 * (K : ℝ) ^ 2 + 2 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  set E := (R + 1).primesBelow.filter (fun p => p ∣ G.P₀) with hE
  have hP₀ : G.P₀ ≠ 0 := G.P₀_pos.ne'
  have hsub : E ⊆ G.P₀.primeFactors := by
    intro p hp
    rw [hE, Finset.mem_filter, Nat.mem_primesBelow] at hp
    exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, hP₀⟩
  have hcard : E.card ≤ G.P₀.primeFactors.card := Finset.card_le_card hsub
  have h2 : ∀ t ∈ E, 2 ≤ t := fun t ht => by
    rw [hE, Finset.mem_filter, Nat.mem_primesBelow] at ht
    exact ht.1.2.two_le
  have hsum := sum_inv_le_log_card_add_one E h2
  -- `ω(P₀) ≤ 2 logP₀Nat`
  have hω : (G.P₀.primeFactors.card : ℝ) ≤ 2 * logP₀Nat K := by
    have h1 := omega_mul_log_two_le hP₀
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h3 : Real.log G.P₀ ≤ logP₀Nat K := by
      have hpos : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
      calc Real.log G.P₀ ≤ Real.log (Real.exp (logP₀Nat K)) :=
            Real.log_le_log hpos (P₀_le_exp (by omega))
        _ = logP₀Nat K := Real.log_exp _
    have h0 : (0 : ℝ) ≤ G.P₀.primeFactors.card := by positivity
    nlinarith
  have hcardr : (E.card : ℝ) ≤ 2 * logP₀Nat K := by
    have : (E.card : ℝ) ≤ G.P₀.primeFactors.card := by exact_mod_cast hcard
    linarith
  -- `log(2 logP₀Nat) ≤ 21K² + 1`
  have hlogP : Real.log (2 * (logP₀Nat K : ℝ)) ≤ 21 * (K : ℝ) ^ 2 + 1 := by
    have hP1 : 1 ≤ logP₀Nat K := by
      unfold logP₀Nat
      have := T_pos (K := K) (by omega)
      nlinarith
    have hPpos : (0 : ℝ) < logP₀Nat K := by exact_mod_cast hP1
    have hle := logP₀Nat_le hK
    have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
    have hlogK : Real.log K ≤ K := log_nat_le K
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    rw [Real.log_mul (by norm_num) hPpos.ne']
    have : Real.log (logP₀Nat K) ≤ (20 * K + 17 : ℕ) * Real.log K := by
      calc Real.log (logP₀Nat K) ≤ Real.log ((K : ℝ) ^ (20 * K + 17)) := by
            apply Real.log_le_log hPpos
            exact_mod_cast hle
        _ = (20 * K + 17 : ℕ) * Real.log K := by rw [Real.log_pow]
    push_cast at this
    have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    nlinarith
  -- assemble
  have hlogE : Real.log E.card ≤ Real.log (2 * (logP₀Nat K : ℝ)) := by
    rcases Nat.eq_zero_or_pos E.card with h | h
    · rw [h]; simp
      apply Real.log_nonneg
      have hP1 : 1 ≤ logP₀Nat K := by
        unfold logP₀Nat
        have := T_pos (K := K) (by omega)
        nlinarith
      have : (1 : ℝ) ≤ logP₀Nat K := by exact_mod_cast hP1
      linarith
    · exact Real.log_le_log (by exact_mod_cast h) hcardr
  linarith

/-! ### The lower bound -/

lemma log_R (K : ℕ) : Real.log (R K) = (2 : ℝ) ^ m₁ K * Real.log 2 := by
  unfold R; rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

lemma log_log_R_ge (K : ℕ) : (m₁ K : ℝ) * Real.log 2 - 1 ≤ Real.log (Real.log (R K)) := by
  rw [log_R, Real.log_mul (by positivity) (Real.log_pos (by norm_num)).ne', Real.log_pow]
  have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h2 : Real.log (1 / 2) ≤ Real.log (Real.log 2) := by
    apply Real.log_le_log (by norm_num)
    linarith [Real.log_two_gt_d9]
  have h3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  linarith

/-- **Lower bound**: `∑_{p∈sm} 1/p ≥ m₁ log 2 − 21K² − 4`. -/
theorem sum_inv_smallPrimes_ge {K : ℕ} (hK : 100 ≤ K) :
    (m₁ K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hR2 : 2 ≤ R K := by
    unfold R
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ m₁ K) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  -- lower Mertens at `R + 1`
  have hM := log_log_le_sum_inv_primesBelow (R K + 1) (by omega)
  have hRr : (2 : ℝ) ≤ R K := by exact_mod_cast hR2
  have hlogR : 0 < Real.log (R K) := Real.log_pos (by linarith)
  have hmono : Real.log (Real.log (R K)) ≤ Real.log (Real.log ((R K + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log hlogR
    apply Real.log_le_log (by linarith)
    push_cast; linarith
  have hlow := log_log_R_ge K
  -- split the primes below `R+1` by `p ∣ P₀`
  have hsplit := Finset.sum_filter_add_sum_filter_not ((R K + 1).primesBelow)
    (fun p => p ∣ G.P₀) (fun p => (p : ℝ)⁻¹)
  have hexcl := sum_inv_excluded_le hK (R K)
  unfold smallPrimes
  linarith

/-! ### The upper bound -/

/-- **Upper bound**: `∑_{p∈sm} 1/p ≤ 3m₁ + 5`. -/
theorem sum_inv_smallPrimes_le {K : ℕ} (hK : 100 ≤ K) :
    ∑ p ∈ smallPrimes (R K) (gridOf K (N K) (by omega)).P₀, (p : ℝ)⁻¹ ≤ 3 * m₁ K + 5 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hR2 : 2 ≤ R K := by
    unfold R
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ m₁ K) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hsub : smallPrimes (R K) G.P₀ ⊆ (R K + 1).primesBelow := Finset.filter_subset _ _
  have h1 : ∑ p ∈ smallPrimes (R K) G.P₀, (p : ℝ)⁻¹ ≤ ∑ p ∈ (R K + 1).primesBelow, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hsplit : ∑ p ∈ (R K + 1).primesBelow, (p : ℝ)⁻¹
      = ∑ p ∈ (R K + 1).primesBelow.filter (fun p => 2 < p), (p : ℝ)⁻¹
        + ∑ p ∈ (R K + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the dyadic bound for `2 < p ≤ R`
  have hdy := sum_inv_primes_Ioc_le (R := 2) (Y := R K) le_rfl hR2
  have hlogR : Nat.log 2 (R K) = 2 ^ m₁ K := natLog_R K
  have hlog2 : Nat.log 2 2 = 1 := by simpa using Nat.log_pow (by norm_num : 1 < 2) 1
  rw [hlogR, hlog2] at hdy
  push_cast at hdy
  rw [Real.log_pow, Real.log_one] at hdy
  have hl2 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hm0 : (0 : ℝ) ≤ m₁ K := by positivity
  have hA : ∑ p ∈ (R K + 1).primesBelow.filter (fun p => 2 < p), (p : ℝ)⁻¹ ≤ 4 + 3 * m₁ K := by
    nlinarith
  -- the primes `≤ 2` contribute at most `1/2`
  have hB : ∑ p ∈ (R K + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹ ≤ 1 / 2 := by
    have hsub2 : (R K + 1).primesBelow.filter (fun p => ¬ 2 < p) ⊆ {2} := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      have := hp.1.2.two_le
      rw [Finset.mem_singleton]; omega
    calc ∑ p ∈ (R K + 1).primesBelow.filter (fun p => ¬ 2 < p), (p : ℝ)⁻¹
        ≤ ∑ p ∈ ({2} : Finset ℕ), (p : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity)
      _ = 1 / 2 := by simp
  linarith

/-! ### The subset count -/

/-- `#{T' ⊆ s : T' ≠ ∅, |T'| ≤ M} ≤ M·(|s|+1)^M`. -/
theorem card_small_subsets_le (s : Finset ℕ) (M : ℕ) :
    (s.powerset.filter (fun T' => T'.Nonempty ∧ T'.card ≤ M)).card ≤ M * (s.card + 1) ^ M := by
  classical
  have hsub : s.powerset.filter (fun T' => T'.Nonempty ∧ T'.card ≤ M)
      ⊆ (Finset.Icc 1 M).biUnion (fun k => Finset.powersetCard k s) := by
    intro T' hT'
    rw [Finset.mem_filter, Finset.mem_powerset] at hT'
    rw [Finset.mem_biUnion]
    refine ⟨T'.card, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Finset.card_pos.2 hT'.2.1, hT'.2.2⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hT'.1, rfl⟩
  calc (s.powerset.filter (fun T' => T'.Nonempty ∧ T'.card ≤ M)).card
      ≤ ((Finset.Icc 1 M).biUnion (fun k => Finset.powersetCard k s)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc 1 M, (Finset.powersetCard k s).card := Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.Icc 1 M, s.card.choose k := by
        simp only [Finset.card_powersetCard]
    _ ≤ ∑ _k ∈ Finset.Icc 1 M, (s.card + 1) ^ M := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Icc] at hk
        calc s.card.choose k ≤ s.card ^ k := Nat.choose_le_pow _ _
          _ ≤ (s.card + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          _ ≤ (s.card + 1) ^ M := Nat.pow_le_pow_right (by omega) hk.2
    _ = M * (s.card + 1) ^ M := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp

lemma card_smallPrimes_le (R P₀ : ℕ) : (smallPrimes R P₀).card ≤ R + 1 := by
  unfold smallPrimes
  calc ((R + 1).primesBelow.filter (fun p => ¬ p ∣ P₀)).card
      ≤ (R + 1).primesBelow.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (Finset.range (R + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = R + 1 := Finset.card_range _

end Sched

end NormalNumbers.G4
