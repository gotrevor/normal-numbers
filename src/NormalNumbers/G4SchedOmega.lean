/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaWitness
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Size arithmetic for the `Ω` schedule

The two `Ω`-specific §4D fields of `ScheduleWitnessΩ` (`hjunk`, `hfar`) are pure size
arithmetic in the schedule parameters.  The one non-obvious input is the frozen sum

  `T(P₀) = ∑_{p ∣ P₀} 1/(p−1)`,

which must be **log log**-size, not `ω(P₀)`-size: the junk term is multiplied by `rowL1 b K`,
which only decays like `(2/3)^K`, while `ω(P₀)` is super-exponential in `K`.  The saving is that
the `j`-th smallest prime factor is at least `j + 2`, so `T(P₀) ≤ harmonic ω(P₀) ≤ 1 + log ω(P₀)`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- A finset of positive naturals has reciprocal sum at most the harmonic number of its size:
the `j`-th smallest element is at least `j+1`. -/
theorem sum_inv_le_harmonic : ∀ (n : ℕ) (B : Finset ℕ), B.card = n → 0 ∉ B →
    ∑ k ∈ B, (1 : ℝ) / k ≤ (harmonic n : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro B hB _
      rw [Finset.card_eq_zero.1 hB]
      simp
  | succ n ih =>
      intro B hB h0
      have hne : B.Nonempty := Finset.card_pos.1 (by omega)
      set M := B.max' hne with hM
      have hMmem : M ∈ B := B.max'_mem hne
      have hsub : B ⊆ Finset.Icc 1 M := by
        intro k hk
        refine Finset.mem_Icc.2 ⟨?_, B.le_max' k hk⟩
        rcases Nat.eq_zero_or_pos k with h | h
        · exact absurd (h ▸ hk) h0
        · exact h
      have hcard : n + 1 ≤ M := by
        have := Finset.card_le_card hsub
        rw [hB, Nat.card_Icc] at this
        omega
      have herase : (B.erase M).card = n := by
        rw [Finset.card_erase_of_mem hMmem, hB]
        omega
      have h0' : 0 ∉ B.erase M := fun h => h0 (Finset.mem_of_mem_erase h)
      have hih := ih (B.erase M) herase h0'
      have hMr : ((n : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hcard
      have hMpos : (0 : ℝ) < M := by linarith [(by positivity : (0:ℝ) ≤ (n:ℝ))]
      have hsplit : ∑ k ∈ B, (1 : ℝ) / k = 1 / M + ∑ k ∈ B.erase M, (1 : ℝ) / k :=
        (Finset.add_sum_erase _ _ hMmem).symm
      have hterm : (1 : ℝ) / M ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hMr
      have hhs : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
        rw [harmonic_succ]
        push_cast
        rw [inv_eq_one_div]
      rw [hsplit, hhs]
      linarith

/-- **`∑_{p ∣ N} 1/(p−1) ≤ harmonic ω(N)`.** -/
theorem sum_inv_sub_one_primeFactors_le (N : ℕ) :
    ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) ≤ (harmonic N.primeFactors.card : ℝ) := by
  classical
  set B := N.primeFactors.image (fun p => p - 1) with hB
  have hinj : Set.InjOn (fun p => p - 1) N.primeFactors := by
    intro p hp q hq hpq
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
    simp only at hpq
    omega
  have hcard : B.card = N.primeFactors.card := Finset.card_image_of_injOn hinj
  have h0 : 0 ∉ B := by
    rw [hB]
    intro h
    obtain ⟨p, hp, hp0⟩ := Finset.mem_image.1 h
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have heq : ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) = ∑ k ∈ B, (1 : ℝ) / k := by
    rw [hB, Finset.sum_image (fun p hp q hq h => hinj hp hq h)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    congr 1
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [heq, ← hcard]
  exact sum_inv_le_harmonic B.card B rfl h0

/-- The `log log` form. -/
theorem sum_inv_sub_one_primeFactors_le_log (N : ℕ) :
    ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) ≤ 1 + Real.log (N.primeFactors.card) :=
  (sum_inv_sub_one_primeFactors_le N).trans (harmonic_le_one_add_log _)

end NormalNumbers.G4
