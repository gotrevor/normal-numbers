/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.PrimeReservoir

/-!
# Route 2: the one-step reservoir recurrence

From `n` to `n + 1` every reservoir term is multiplied by 16; primes in `(4n, 4n+4]`
leave the window (the transfer `bbpReservoirExit`), and the `j = n` pair enters
(`bbpReservoirEntry`, of size `O(1/n)`).  So `(R, S)` is a ×16 skew map on the
two-torus kicked along the antidiagonal by the exit transfer: the arithmetic source
lives entirely in `bbpReservoirExit`.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

/-- Real summand of the reservoir with an explicit window predicate on the denominator. -/
noncomputable def reservoirTerm (P : ℕ → Prop) [DecidablePred P] (k j : ℕ) : ℝ :=
  (16 : ℝ) ^ k *
    ((if Nat.Prime (8 * j + 1) ∧ P (8 * j + 1) then 4 / (8 * (j : ℝ) + 1) else 0) -
     (if Nat.Prime (8 * j + 5) ∧ P (8 * j + 5) then 1 / (8 * (j : ℝ) + 5) else 0))

/-- Mass leaving the reservoir between `n` and `n + 1`: primes in `(4n, 4n+4]`. -/
noncomputable def bbpReservoirExit (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, reservoirTerm (fun m => 4 * n < m ∧ m ≤ 4 * n + 4) (n + 1 - j) j

/-- Mass entering at `j = n`. -/
noncomputable def bbpReservoirEntry (n : ℕ) : ℝ :=
  reservoirTerm (fun m => 4 * (n + 1) < m) 1 n

/-- Exact recurrence `R_{n+1} = 16 R_n − exit_n + entry_n`. -/
theorem bbpPrimeReservoir_succ (n : ℕ) :
    bbpPrimeReservoir (n + 1) =
      16 * bbpPrimeReservoir n - bbpReservoirExit n + bbpReservoirEntry n := by
  rw [bbpPrimeReservoir, Finset.sum_range_succ, bbpReservoirEntry, bbpPrimeReservoir,
    bbpReservoirExit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j < n := Finset.mem_range.1 hj
    rw [reservoirTerm, show n + 1 - j = (n - j) + 1 by omega, pow_succ]
    push_cast
    by_cases hA : Nat.Prime (8 * j + 1) <;> by_cases hB : Nat.Prime (8 * j + 5) <;>
      simp only [hA, hB, true_and, false_and, if_false] <;> (try split_ifs) <;> first | omega | ring
  · rw [reservoirTerm, Nat.add_sub_cancel_left, pow_one]

/-- Companion recurrence `S_{n+1} = 16 S_n + exit_n + 16·kick_n − entry_n`: the exit
transfer moves from the reservoir to the residual, so `R − S` is kicked by `−2·exit`. -/
theorem bbpResidual_succ (n : ℕ) :
    bbpResidual (n + 1) =
      16 * bbpResidual n + bbpReservoirExit n + 16 * bbpKick n - bbpReservoirEntry n := by
  rw [bbpResidual, bbpResidual, bbpPrimeReservoir_succ, piPartial, piPartial,
    Finset.sum_range_succ, bbpTerm]
  have h : (16 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  ring

/-- **Exit collapse** (proved).  The only candidate
denominator in `(4n, 4n+4]` is `p = 4n+1`.  For `p = 8k+1` the exit numerator is
`4·16^{k+1} = 64·2^{(p-1)/2}`; for `p = 8k+5` it is
`-16^{k+2} = -64·2^{(p-1)/2}`.  Euler's criterion gives
`2^{(p-1)/2} ≡ (2|p) = ±1`, with the sign cancelling the coefficient.
Hence the exit transfer is `64/p` mod 1:
NOT an O(1) arithmetic source.  Probe `scripts/pi_route2_exit.py`: 1125/1125 primes
`4n+1 ≤ 20001`; control base 3: 2/1125. -/
lemma two_pow_half_eq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p / 2) = if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')
  split_ifs with h
  · exact (ZMod.euler_criterion p h2).1 ((ZMod.exists_sq_eq_two_iff hp2).2 h)
  · rcases ZMod.pow_div_two_eq_neg_one_or_one p h2 with h' | h'
    · exact absurd ((ZMod.exists_sq_eq_two_iff hp2).1 ((ZMod.euler_criterion p h2).2 h')) h
    · exact h'

lemma real_div_eq_int_add_of_zmod {p : ℕ} (hp : 0 < p) (N : ℤ) (h : (N : ZMod p) = 64) :
    ∃ z : ℤ, (N : ℝ) / p = z + 64 / p := by
  have h0 : ((N - 64 : ℤ) : ZMod p) = 0 := by push_cast; rw [h]; ring
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  refine ⟨z, ?_⟩
  have hp' : (p : ℝ) ≠ 0 := by positivity
  have hN : (N : ℝ) = p * z + 64 := by
    have := congrArg (Int.cast : ℤ → ℝ) hz; push_cast at this; linarith
  rw [hN]; field_simp

theorem bbpReservoirExit_mod_one (n : ℕ) : ∃ z : ℤ, bbpReservoirExit n =
    z + (if Nat.Prime (4 * n + 1) then 64 / (4 * (n : ℝ) + 1) else 0) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- n = 2k: the pole is p = 8k+1 at j = k, coefficient 4, exponent k+1.
    have hsum : bbpReservoirExit (2 * k) =
        (16 : ℝ) ^ (k + 1) * (if Nat.Prime (8 * k + 1) then 4 / (8 * (k : ℝ) + 1) else 0) := by
      rw [bbpReservoirExit]
      by_cases hk : k = 0
      · subst hk; simp [Nat.not_prime_one]
      rw [Finset.sum_eq_single k]
      · rw [reservoirTerm, show 2 * k + 1 - k = k + 1 by omega]
        have h5 : ¬ (8 * k + 5 ≤ 4 * (2 * k) + 4) := by omega
        simp only [h5, and_false, if_false, sub_zero]
        by_cases hp : Nat.Prime (8 * k + 1)
        · rw [if_pos ⟨hp, by omega, by omega⟩, if_pos hp]
        · rw [if_neg (fun h => hp h.1), if_neg hp]
      · intro b _ hb
        rw [reservoirTerm, if_neg (fun h => hb (by omega)), if_neg (fun h => by omega), sub_zero,
          mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    rw [hsum]
    push_cast
    rw [show 4 * (2 * (k : ℝ)) + 1 = 8 * k + 1 by ring, show 4 * (2 * k) + 1 = 8 * k + 1 by ring]
    by_cases hp : Nat.Prime (8 * k + 1)
    · have := Fact.mk hp
      rw [if_pos hp, if_pos hp]
      have h2 := two_pow_half_eq (p := 8 * k + 1) (by omega)
      rw [if_pos (by omega), show (8 * k + 1) / 2 = 4 * k by omega] at h2
      obtain ⟨z, hz⟩ := real_div_eq_int_add_of_zmod (p := 8 * k + 1) (by omega)
        (4 * 16 ^ (k + 1)) (by
          push_cast
          rw [show (16 : ZMod (8 * k + 1)) ^ (k + 1) = 16 * (2 ^ (4 * k)) by
            rw [pow_mul]; norm_num; ring, h2]
          norm_num)
      refine ⟨z, ?_⟩
      push_cast at hz
      rw [← hz]; ring
    · rw [if_neg hp, if_neg hp]; exact ⟨0, by simp⟩
  · -- n = 2k+1: the pole is p = 8k+5 at j = k, coefficient -1, exponent k+2.
    have hsum : bbpReservoirExit (2 * k + 1) =
        -((16 : ℝ) ^ (k + 2) * (if Nat.Prime (8 * k + 5) then 1 / (8 * (k : ℝ) + 5) else 0)) := by
      rw [bbpReservoirExit, Finset.sum_eq_single k]
      · rw [reservoirTerm, show 2 * k + 1 + 1 - k = k + 2 by omega]
        have h1 : ¬ (4 * (2 * k + 1) < 8 * k + 1) := by omega
        simp only [h1, and_false, false_and, if_false, zero_sub]
        by_cases hp : Nat.Prime (8 * k + 5)
        · rw [if_pos ⟨hp, by omega, by omega⟩, if_pos hp]; ring
        · rw [if_neg (fun h => hp h.1), if_neg hp]; ring
      · intro b _ hb
        rw [reservoirTerm, if_neg (fun h => by omega), if_neg (fun h => hb (by omega)), sub_zero,
          mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    rw [hsum]
    push_cast
    rw [show 4 * (2 * (k : ℝ) + 1) + 1 = 8 * k + 5 by ring,
      show 4 * (2 * k + 1) + 1 = 8 * k + 5 by ring]
    by_cases hp : Nat.Prime (8 * k + 5)
    · have := Fact.mk hp
      rw [if_pos hp, if_pos hp]
      have h2 := two_pow_half_eq (p := 8 * k + 5) (by omega)
      rw [if_neg (by omega), show (8 * k + 5) / 2 = 4 * k + 2 by omega] at h2
      obtain ⟨z, hz⟩ := real_div_eq_int_add_of_zmod (p := 8 * k + 5) (by omega)
        (-16 ^ (k + 2)) (by
          push_cast
          rw [show (16 : ZMod (8 * k + 5)) ^ (k + 2) = 64 * (2 ^ (4 * k + 2)) by
            rw [show (16 : ZMod (8 * k + 5)) = 2 ^ 4 by norm_num, ← pow_mul]; ring, h2]
          ring)
      refine ⟨z, ?_⟩
      push_cast at hz
      rw [← hz]; ring
    · rw [if_neg hp, if_neg hp]; exact ⟨0, by simp⟩

end NormalNumbers.PiDisjunctiveRoutes
