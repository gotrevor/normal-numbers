/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogCost

/-!
# N7: the honest `M(P)` for base 2

`bigM_two_le`: for a set `P` of odd primes with product `Q`,
`M(P) ≤ ∏_{p∈P} 2^p · 2Q`.  For each `p`, write `d = ord_p 2` and `L = ord_Q 2`.  Then `d ∣ 2L`,
and lifting the exponent gives `v_p(2^{2L} − 1) = v_p(2^d − 1) + v_p(2L/d)`, so
`p^{β'_p} ≤ (2^d − 1)(2L/d) ≤ 2^p · 2Q`.

This is cruder than the audit's `log M ≤ (log 2)Σ(p−1) + π(Y) log Y`: here
`log M ≤ (log 2)(Σ p + s) + s log Q`.  Both are polynomial in `Y`, which is all `ζ_Y` needs.
The crude eq. (4) bound `M ≤ 2^{2Q}` would be fatal.
-/

namespace NormalNumbers.GrowingLocalizedLog

open NormalNumbers.Literature.VandeheyDiff Finset

lemma pow_padicValNat_le {p n : ℕ} (hn : n ≠ 0) : p ^ padicValNat p n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

/-- One factor of `M(P)` in base 2. -/
lemma factor_two_le {p Q : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpQ : p ∣ Q) (hQ : 0 < Q) :
    p ^ padicValNat p (2 ^ (2 * orderOf ((2 : ℕ) : ZMod Q)) - 1) ≤ 2 ^ p * (2 * Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero Q := ⟨hQ.ne'⟩
  set L := orderOf ((2 : ℕ) : ZMod Q) with hLdef
  have hLQ : L ≤ Q := by
    have := orderOf_le_card_univ (x := ((2 : ℕ) : ZMod Q)); rwa [ZMod.card] at this
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · rw [hL0]; simp only [mul_zero, pow_zero, Nat.sub_self, padicValNat_zero_right]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  set d := orderOf ((2 : ℕ) : ZMod p) with hd
  -- `d ∣ 2L`
  have hpow : ((2 : ℕ) : ZMod Q) ^ L = 1 := pow_orderOf_eq_one _
  have hpowp : ((2 : ℕ) : ZMod p) ^ L = 1 := by
    have := congrArg (ZMod.castHom hpQ (ZMod p)) hpow
    rwa [map_pow, map_one, map_natCast] at this
  have hdL : d ∣ 2 * L := (orderOf_dvd_of_pow_eq_one hpowp).trans (dvd_mul_left _ _)
  have hd0 : d ≠ 0 := by
    intro h; rw [h, zero_dvd_iff] at hdL; omega
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hdp : d ≤ p := by
    have := ZMod.orderOf_dvd_card_sub_one h2ne
    have := Nat.le_of_dvd (by have := hp.two_le; omega) this; omega
  obtain ⟨n, hn⟩ := hdL
  have hn0 : n ≠ 0 := by rintro rfl; omega
  have hx : 1 < 2 ^ d := Nat.one_lt_two_pow hd0
  have hdiv : p ∣ 2 ^ d - 1 := by
    have : ((2 : ℕ) : ZMod p) ^ d = 1 := pow_orderOf_eq_one _
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hx.le]
    push_cast at this ⊢; rw [this]; simp
  have hndvd : ¬ p ∣ 2 ^ d := by
    intro h; exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hodd' : Odd p := hp.odd_of_ne_two hodd
  have hlte := padicValNat.pow_sub_pow (p := p) hodd' (y := 1) hx (by simpa using hdiv) hndvd hn0
  rw [one_pow] at hlte
  rw [hn, pow_mul, hlte, pow_add]
  have h1 : p ^ padicValNat p (2 ^ d - 1) ≤ 2 ^ p := by
    refine (pow_padicValNat_le (by omega)).trans ?_
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) hdp)
  have h2 : p ^ padicValNat p n ≤ 2 * Q := by
    refine (pow_padicValNat_le hn0).trans ?_
    have : n ≤ d * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hd0)
    omega
  exact Nat.mul_le_mul h1 h2

/-- **N7.**  `M(P) ≤ ∏_{p∈P} 2^p · 2Q` for a set of odd primes in base 2. -/
theorem bigM_two_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    bigM 2 P ≤ ∏ p ∈ P, (2 ^ p * (2 * primeProd P)) := by
  have hQ : 0 < primeProd P :=
    Finset.prod_pos fun p hp => (hP p hp).1.pos
  unfold bigM
  apply Finset.prod_le_prod' 
  intro p hp
  exact factor_two_le (hP p hp).1 (hP p hp).2 (Finset.dvd_prod_of_mem _ hp) hQ

end NormalNumbers.GrowingLocalizedLog
