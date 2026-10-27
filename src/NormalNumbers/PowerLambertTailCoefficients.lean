/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertTailDefs
import NormalNumbers.PowerLambertTailBounds

/-!
# Tail coefficients for power-divisor Lambert series
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- **Prefix average bound for the actual tail power-divisor coefficients.** -/
@[blueprint (title := "Higher-power divisor tail coefficients have prefix sum at most N/8")]
theorem prefix_tailPowerDivisorCount_bound (r : ℕ) (hr : 2 ≤ r) (N : ℕ) :
    (∑ n ∈ Finset.range N, (tailPowerDivisorCount r 8 n : ℝ)) ≤ (N : ℝ) / 8 := by
  classical
  let indicator : ℕ → ℕ → ℝ := fun n d =>
    if d ∈ n.divisors ∧ 8 < d ∧ d ^ r ∣ n then 1 else 0
  have hcount (n : ℕ) (hn : n < N) :
      (tailPowerDivisorCount r 8 n : ℝ) =
        ∑ d ∈ Finset.range N, indicator n d := by
    by_cases hn0 : n = 0
    · subst n
      simp [tailPowerDivisorCount_zero, indicator]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hdivsub : n.divisors ⊆ Finset.range N := by
        intro d hd
        simp only [Finset.mem_range]
        exact lt_of_le_of_lt (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_divisors hd)) hn
      calc
        (tailPowerDivisorCount r 8 n : ℝ) =
            ∑ d ∈ n.divisors, if 8 < d ∧ d ^ r ∣ n then (1 : ℝ) else 0 := by
              rw [tailPowerDivisorCount, Finset.card_filter]
              norm_cast
        _ = ∑ d ∈ n.divisors,
              if d ∈ n.divisors ∧ 8 < d ∧ d ^ r ∣ n then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              simp [hd]
        _ = ∑ d ∈ Finset.range N, indicator n d := by
              unfold indicator
              apply Finset.sum_subset hdivsub
              intro d hd hnot
              simp [hnot]
  rw [show (∑ n ∈ Finset.range N, (tailPowerDivisorCount r 8 n : ℝ)) =
      ∑ n ∈ Finset.range N, ∑ d ∈ Finset.range N, indicator n d by
        apply Finset.sum_congr rfl
        intro n hn
        exact hcount n (Finset.mem_range.mp hn)]
  rw [Finset.sum_comm]
  calc
    (∑ d ∈ Finset.range N, ∑ n ∈ Finset.range N, indicator n d) ≤
        ∑ d ∈ Finset.range N,
          if 8 < d then (N : ℝ) / (d : ℝ) ^ r else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hD : 8 < d
      · rw [if_pos hD]
        let q := d ^ r
        have hq : 0 < q := Nat.pow_pos (by omega)
        have hmajor : d * (d - 1) ≤ q := by
          dsimp [q]
          have hsq : d ^ 2 ≤ d ^ r := Nat.pow_le_pow_right (by omega) hr
          calc
            d * (d - 1) ≤ d * d := Nat.mul_le_mul_left d (Nat.sub_le d 1)
            _ = d ^ 2 := by simp [pow_two]
            _ ≤ d ^ r := hsq
        have hsubset :
            ∑ n ∈ Finset.range N, indicator n d ≤
              ∑ n ∈ Finset.range N, if n ≠ 0 ∧ q ∣ n then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hmem : d ∈ n.divisors ∧ 8 < d ∧ d ^ r ∣ n
          · have hn0 : n ≠ 0 := by
              intro hn0
              subst n
              simp at hmem
            have hdiv : d ∣ n := Nat.dvd_of_mem_divisors hmem.1
            have hqdiv : q ∣ n := by simpa [q] using hmem.2.2
            simp [indicator, hmem, hn0, hdiv, hqdiv, q]
          · by_cases hbase : n ≠ 0 ∧ q ∣ n
            · have hdvd : d ∣ n := dvd_trans (dvd_pow_self d (by omega)) hbase.2
              have hdmem : d ∈ n.divisors :=
              Nat.mem_divisors.mpr ⟨hdvd, hbase.1⟩
              have hDfalse : ¬ 8 < d := by
                intro hD'
                apply hmem
                exact ⟨hdmem, hD', by simpa [q] using hbase.2⟩
              simp [indicator, hbase, q, hdmem, hDfalse]
            · have hzero : indicator n d = 0 := by
                have hnot : ¬ (d ∈ n.divisors ∧ 8 < d ∧ d ^ r ∣ n) := by
                  intro hi
                  have hbase' : n ≠ 0 ∧ q ∣ n := by
                    constructor
                    · exact (Nat.mem_divisors.mp hi.1).2
                    · simpa [q] using hi.2.2
                  exact hbase hbase'
                simpa [indicator] using hnot
              simp [hzero, hbase]
        have hcard :
            (∑ n ∈ Finset.range N, if n ≠ 0 ∧ q ∣ n then (1 : ℝ) else 0) =
              (((Finset.range N).filter fun n => n ≠ 0 ∧ q ∣ n).card : ℝ) := by
          rw [Finset.card_filter]
          norm_cast
        have hcountle := card_positive_multiples_lt_le N q hq
        have hcast :
            (((Finset.range N).filter fun n => n ≠ 0 ∧ q ∣ n).card : ℝ) ≤
              (N : ℝ) / (q : ℝ) := by
          calc
            _ ≤ ((N / q : ℕ) : ℝ) := by exact_mod_cast hcountle
            _ ≤ (N : ℝ) / q := Nat.cast_div_le
        calc
          ∑ n ∈ Finset.range N, indicator n d ≤ _ := hsubset
          _ = (((Finset.range N).filter fun n => n ≠ 0 ∧ q ∣ n).card : ℝ) := hcard
          _ ≤ (N : ℝ) / (q : ℝ) := hcast
          _ = (N : ℝ) / (d : ℝ) ^ r := by simp [q]
      · simp [if_neg hD, indicator, hD]
    _ ≤ (N : ℝ) / 8 := by
      calc
        _ ≤ (N : ℝ) *
              (∑ d ∈ Finset.range N,
                if 8 < d then (1 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro d hd
          by_cases hD : 8 < d
          · rw [if_pos hD, if_pos hD]
            have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
              exact_mod_cast (show 1 ≤ d by omega)
            have hsq : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ r := by
              exact pow_le_pow_right₀ hd1 (by omega)
            have hden : (d : ℝ) * ((d : ℝ) - 1) ≤ (d : ℝ) ^ r := by
              nlinarith
            have hd8real : (8 : ℝ) < (d : ℝ) := by exact_mod_cast hD
            have hdenpos : 0 < (d : ℝ) * ((d : ℝ) - 1) := by
              apply mul_pos <;> linarith
            calc
              (N : ℝ) / (d : ℝ) ^ r ≤
                  (N : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) :=
                div_le_div_of_nonneg_left (by positivity) hdenpos hden
              _ = (N : ℝ) * (1 / ((d : ℝ) * ((d : ℝ) - 1))) := by ring
          · simp [if_neg hD]
        _ ≤ (N : ℝ) * (1 / 8) :=
          mul_le_mul_of_nonneg_left (reciprocalDivisorTail_le_eighth N) (by positivity)
        _ = (N : ℝ) / 8 := by ring

end NormalNumbers.ArithmeticDisjunctivity
