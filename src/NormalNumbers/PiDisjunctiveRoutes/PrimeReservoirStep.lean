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

/-- **Exit collapse** (frozen, 99%: English proof + exact probe).  The only candidate
denominator in `(4n, 4n+4]` is `p = 4n+1`; its exponent is `(p-1)/4 + 1 = n/2+1` or
`(n+3)/2`, and `16^{(p-1)/4} = 2^{(p-1)/2} ≡ (2|p) = ±1` by Euler's criterion, with the
sign cancelling the coefficient `4` / `-1`.  Hence the exit transfer is `64/p` mod 1:
NOT an O(1) arithmetic source.  Probe `scripts/pi_route2_exit.py`: 1125/1125 primes
`4n+1 ≤ 20001`; control base 3: 2/1125. -/
theorem bbpReservoirExit_mod_one (n : ℕ) : ∃ z : ℤ, bbpReservoirExit n =
    z + (if Nat.Prime (4 * n + 1) then 64 / (4 * (n : ℝ) + 1) else 0) := by
  sorry

end NormalNumbers.PiDisjunctiveRoutes
