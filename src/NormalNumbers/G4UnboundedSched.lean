/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightAssembly
import NormalNumbers.G4SchedLogLog

/-!
# Campaign B: a `k₄` for a coefficient bound that grows with `k₄`

For bounded `c` the schedule picks `k₄` *after* `C` (`exists_good_k₄`).  For the tame weight the
effective constant depends on `K = 4k₄` itself:

    `effC ≤ A + 23K²(1 + 15K²) = A + 368k₄² + 88320k₄⁴`

(`effC_le_of_logLog` with `V = 23K²` from `sched_prime_size` and `L = 15K²` from
`log_card_primeFactors_P₀_leE`).  The junk budget still wins, because it is exponential:
choosing `k₄ = 2^t` turns `100000·C(k₄)·k₄³ ≤ 2^{k₄}` into `34 + 7t ≤ 2^t`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

namespace SchedB

/-- `34 + 7t ≤ 2^t` for `t ≥ 7`. -/
lemma lin_le_two_pow : ∀ {t : ℕ}, 7 ≤ t → 34 + 7 * t ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n 7 with hn | hn
      · have : n = 6 := by omega
        subst this
        norm_num
      · have hih := ih hn
        calc 34 + 7 * (n + 1) = (34 + 7 * n) + 7 := by ring
          _ ≤ 2 ^ n + 7 := by omega
          _ ≤ 2 ^ n + 2 ^ n := by
              have : (7 : ℕ) ≤ 2 ^ n := by
                calc (7 : ℕ) ≤ 2 ^ 3 := by norm_num
                  _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
          _ = 2 ^ (n + 1) := by ring

/-- **A `k₄` for the tame schedule.**  Unlike `exists_good_k₄`, the coefficient bound is allowed
to be the *polynomial in `k₄`* that `effC` produces. -/
theorem exists_good_k₄_poly (b ℓ a : ℕ) :
    ∃ k₄, k₄bℓ b ℓ ≤ k₄ ∧ 40 ≤ k₄ ∧ a ≤ k₄ ∧
      100000 * (a + 368 * k₄ ^ 2 + 88320 * k₄ ^ 4) * k₄ ^ 3 ≤ 2 ^ k₄ := by
  obtain ⟨t, ht7, hts⟩ : ∃ t, 7 ≤ t ∧ max (max 40 a) (k₄bℓ b ℓ) ≤ 2 ^ t := by
    refine ⟨max 7 (max (max 40 a) (k₄bℓ b ℓ)), le_max_left _ _, ?_⟩
    exact le_trans (Nat.lt_two_pow_self).le
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  set k := 2 ^ t with hk
  have h40 : 40 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hts
  have ha : a ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hts
  have hbℓ : k₄bℓ b ℓ ≤ k := le_trans (le_max_right _ _) hts
  refine ⟨k, hbℓ, h40, ha, ?_⟩
  -- `a + 368k² + 88320k⁴ ≤ 88689·k⁴`, so the left side is at most `2^34·k^7`
  have hk1 : 1 ≤ k := by omega
  have hpoly : a + 368 * k ^ 2 + 88320 * k ^ 4 ≤ 88689 * k ^ 4 := by
    have h1 : a ≤ k ^ 4 := le_trans ha (Nat.le_self_pow (by norm_num) k)
    have h2 : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
    nlinarith
  have hstep : 100000 * (a + 368 * k ^ 2 + 88320 * k ^ 4) * k ^ 3
      ≤ 2 ^ 34 * k ^ 7 := by
    have h1 : 100000 * (a + 368 * k ^ 2 + 88320 * k ^ 4) ≤ 100000 * (88689 * k ^ 4) :=
      Nat.mul_le_mul_left _ hpoly
    have h2 : 100000 * (88689 * k ^ 4) ≤ 2 ^ 34 * k ^ 4 := by
      have : (100000 * 88689 : ℕ) ≤ 2 ^ 34 := by norm_num
      calc 100000 * (88689 * k ^ 4) = (100000 * 88689) * k ^ 4 := by ring
        _ ≤ 2 ^ 34 * k ^ 4 := Nat.mul_le_mul_right _ this
    calc 100000 * (a + 368 * k ^ 2 + 88320 * k ^ 4) * k ^ 3
        ≤ (2 ^ 34 * k ^ 4) * k ^ 3 := Nat.mul_le_mul_right _ (h1.trans h2)
      _ = 2 ^ 34 * k ^ 7 := by ring
  refine hstep.trans ?_
  -- `2^34·(2^t)^7 = 2^{34+7t} ≤ 2^{2^t}`
  have hrw : (2 : ℕ) ^ 34 * k ^ 7 = 2 ^ (34 + 7 * t) := by
    rw [hk, ← pow_mul, ← pow_add]
    ring_nf
  rw [hrw]
  exact Nat.pow_le_pow_right (by norm_num) (lin_le_two_pow ht7)

end SchedB

end NormalNumbers.G4
