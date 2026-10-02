/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogBlock
import NormalNumbers.GrowingLocalizedLogM
import NormalNumbers.GrowingLocalizedLogCount

/-!
# The cost is `2^{O(π(Z)^4)}`

`nine_costX_le`: `9 · 2^{3s+2} Q M ≤ 2^{60(π(Z)+2)^4}` for `P` the odd primes `≤ Z`.  This uses
`Q ≤ Z^s`, `bigM_two_le`, and `Z ≤ 17(π(Z)+1)²`.  So the block cost
`A_k + B_k ≤ 2^{60(π+2)^4 + (k+5)π}` is polynomial in `log log N` once `k ≲ π`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset NormalNumbers.Literature.VandeheyDiff

lemma oddPrimes_card_le (Z : ℕ) : (oddPrimes Z).card ≤ Z.primeCounting := by
  rw [← Nat.primesLE_card_eq_primeCounting]; exact Finset.card_filter_le _ _

lemma Z_le_nat (Z : ℕ) : Z ≤ 17 * (Z.primeCounting + 1) ^ 2 := by
  have := le_of_primeCounting Z
  exact_mod_cast this

theorem costX_nat_le (Z : ℕ) :
    2 ^ (3 * (oddPrimes Z).card + 2) * primeProd (oddPrimes Z) * bigM 2 (oddPrimes Z) ≤
      2 ^ (3 * (oddPrimes Z).card + 2 + (oddPrimes Z).card * Z +
        (oddPrimes Z).card * (Z + 1 + (oddPrimes Z).card * Z)) := by
  set P := oddPrimes Z
  set s := P.card
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ p ≠ 2 := fun p hp => mem_oddPrimes.1 hp
  have hZ2 : Z ≤ 2 ^ Z := (Nat.lt_two_pow_self).le
  have hQ : primeProd P ≤ 2 ^ (s * Z) := by
    calc primeProd P ≤ Z ^ s := Finset.prod_le_pow_card _ _ _ fun p hp => (hP p hp).2.1
      _ ≤ (2 ^ Z) ^ s := Nat.pow_le_pow_left hZ2 _
      _ = 2 ^ (s * Z) := by rw [← pow_mul, mul_comm]
  have hM : bigM 2 P ≤ 2 ^ (s * (Z + 1 + s * Z)) := by
    refine (bigM_two_le fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩).trans ?_
    calc ∏ p ∈ P, 2 ^ p * (2 * primeProd P) ≤ (2 ^ Z * (2 * 2 ^ (s * Z))) ^ s := by
          apply Finset.prod_le_pow_card
          intro p hp
          exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (hP p hp).2.1)
            (Nat.mul_le_mul_left _ hQ)
      _ = 2 ^ (s * (Z + 1 + s * Z)) := by
          rw [← pow_succ', ← pow_add, ← pow_mul, mul_comm]; ring_nf
  calc 2 ^ (3 * s + 2) * primeProd P * bigM 2 P
      ≤ 2 ^ (3 * s + 2) * 2 ^ (s * Z) * 2 ^ (s * (Z + 1 + s * Z)) := by gcongr
    _ = _ := by rw [← pow_add, ← pow_add]

theorem nine_costX_le (Z : ℕ) :
    9 * costX 2 (oddPrimes Z) ≤ (2 : ℝ) ^ (60 * (Z.primeCounting + 2) ^ 4) := by
  set s := (oddPrimes Z).card
  set a := Z.primeCounting
  have hs : s ≤ a := oddPrimes_card_le Z
  have hZ := Z_le_nat Z
  have hnat : 9 * (2 ^ (3 * s + 2) * primeProd (oddPrimes Z) * bigM 2 (oddPrimes Z)) ≤
      2 ^ (60 * (a + 2) ^ 4) := by
    refine (Nat.mul_le_mul_left 9 (costX_nat_le Z)).trans ?_
    have h9 : 9 ≤ 2 ^ 4 := by norm_num
    refine (Nat.mul_le_mul_right _ h9).trans ?_
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 : s * Z ≤ a * (17 * (a + 1) ^ 2) := Nat.mul_le_mul hs hZ
    have h2 : s * (s * Z) ≤ a * (a * (17 * (a + 1) ^ 2)) :=
      Nat.mul_le_mul hs (Nat.mul_le_mul hs hZ)
    have e : s * (Z + 1 + s * Z) = s * Z + s + s * (s * Z) := by ring
    rw [e]
    nlinarith [h1, h2, hs]
  unfold costX
  exact_mod_cast hnat

end NormalNumbers.GrowingLocalizedLog
