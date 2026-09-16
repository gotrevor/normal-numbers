/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedEffC
import NormalNumbers.G4EntropyBand

/-!
# Campaign B: the schedule's prime-size exponent

`cMax_le_of_logLog` needs one number: a `V` with `max(Dm, 2T, ρmax) ≤ 2^{2^V}` at the
schedule's grid.  `Sched.gridDm_le_two_pow` gives `gridDm ≤ 2^{2·2^{21K²}}`, and the other two
are dwarfed by it, so `V = 23K²` works — **polynomial in `K`**, against a junk budget of
`2^{Θ(K)}`.  This is the last size fact the doubly-logarithmic headline needs.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

namespace Sched

/-- `gridDm ≤ 2^{2^{22K²}}`. -/
lemma gridDm_le_two_pow_two_pow {K : ℕ} (hK : 100 ≤ K) :
    gridDm K (N K) ≤ 2 ^ 2 ^ (22 * K ^ 2) := by
  refine (gridDm_le_two_pow hK).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 : 2 * 2 ^ (21 * K ^ 2) = 2 ^ (21 * K ^ 2 + 1) := by ring
  rw [h1]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  nlinarith [sq_nonneg K, (by nlinarith : 1 ≤ K ^ 2)]

/-- The full prime bound at the schedule's grid: `V = 23K²`. -/
theorem sched_prime_size {K : ℕ} (hK : 100 ≤ K) (hK1 : 1 ≤ K) :
    max (max (gridDm K (N K)) (2 * Fintype.card (gridOf K (N K) hK1).Idx))
        (J K * gridDm K (N K))
      ≤ 2 ^ 2 ^ (23 * K ^ 2) := by
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hbase : gridDm K (N K) ≤ 2 ^ 2 ^ (22 * K ^ 2) := gridDm_le_two_pow_two_pow hK
  have hmono : (2 : ℕ) ^ 2 ^ (22 * K ^ 2) ≤ 2 ^ 2 ^ (23 * K ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  refine max_le (max_le (hbase.trans hmono) ?_) ?_
  · -- `2T ≤ 2^{3K²+3K+1} ≤ 2^{2^{23K²}}`
    have hcard : Fintype.card (gridOf K (N K) hK1).Idx = (K ^ 2 + 1) ^ K * N K :=
      gridOf.card_Idx hK1
    have hT : (K ^ 2 + 1) ^ K * N K = T K := by
      unfold T gridT
      rfl
    have hTle : T K ≤ K ^ (3 * K + 3) := T_le hK
    have hpow : K ^ (3 * K + 3) ≤ 2 ^ (K * (3 * K + 3)) := pow_le_two_pow_mul K (3 * K + 3)
    have hexp : K * (3 * K + 3) + 1 ≤ 2 ^ (23 * K ^ 2) := by
      have h1 : K * (3 * K + 3) + 1 ≤ 23 * K ^ 2 := by nlinarith
      exact h1.trans (Nat.lt_two_pow_self).le
    calc 2 * Fintype.card (gridOf K (N K) hK1).Idx
        = 2 * T K := by rw [hcard, hT]
      _ ≤ 2 * 2 ^ (K * (3 * K + 3)) := by
          exact Nat.mul_le_mul_left 2 (hTle.trans hpow)
      _ = 2 ^ (K * (3 * K + 3) + 1) := by ring
      _ ≤ 2 ^ 2 ^ (23 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp
  · -- `J·gridDm ≤ 2^{2^{22K²}}·2^{2^{22K²}} = 2^{2^{22K²+1}} ≤ 2^{2^{23K²}}`
    have hJ : J K ≤ K ^ 4 := J_le hK
    have hJ2 : K ^ 4 ≤ 2 ^ (K * 4) := pow_le_two_pow_mul K 4
    have hJ3 : (K * 4 : ℕ) ≤ 2 ^ (22 * K ^ 2) := by
      have h1 : K * 4 ≤ 22 * K ^ 2 := by nlinarith
      exact h1.trans (Nat.lt_two_pow_self).le
    have hJle : J K ≤ 2 ^ 2 ^ (22 * K ^ 2) :=
      (hJ.trans hJ2).trans (Nat.pow_le_pow_right (by norm_num) hJ3)
    have hexp2 : 2 ^ (22 * K ^ 2) + 2 ^ (22 * K ^ 2) ≤ 2 ^ (23 * K ^ 2) := by
      have : 2 ^ (22 * K ^ 2) + 2 ^ (22 * K ^ 2) = 2 ^ (22 * K ^ 2 + 1) := by ring
      rw [this]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    calc J K * gridDm K (N K)
        ≤ 2 ^ 2 ^ (22 * K ^ 2) * 2 ^ 2 ^ (22 * K ^ 2) := Nat.mul_le_mul hJle hbase
      _ = 2 ^ (2 ^ (22 * K ^ 2) + 2 ^ (22 * K ^ 2)) := by rw [← pow_add]
      _ ≤ 2 ^ 2 ^ (23 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp2

end Sched

end NormalNumbers.G4
