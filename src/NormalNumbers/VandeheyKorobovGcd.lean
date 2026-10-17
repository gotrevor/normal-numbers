/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovOrders

/-!
# GCD structure in Vandehey's Korobov estimate

This file proves Claim 4.5 in the proof of Vandehey's Proposition 4.1.  The
prime-by-prime argument uses exact LTE except at the harmless boundary
`v₂(m) = 1`; preservation of `4` by the rounded divisor supplies the exceptional
two-adic hypothesis in every other case.
-/

namespace NormalNumbers.VandeheyKorobov

private lemma min_add_eq_min_add_min_tsub (A I M : ℕ) :
    min (A + I) M = min A M + min I (M - min A M) := by
  omega

/-- Local valuation form of **Vandehey, Claim 4.5**.  If `mbar` is the gcd of
`b^τ - 1` with `m`, has the same prime support as `m`, and preserves the factor
`4`, then the gcd after the `i`-th order shift has the claimed exact shape. -/
theorem gcd_pow_mul_sub_one_eq
    {b τ m mbar : ℕ} (hb : 2 ≤ b) (hτ : 0 < τ) (hm : m ≠ 0)
    (hbm : Nat.Coprime b m)
    (hmbar : mbar = Nat.gcd (b ^ τ - 1) m)
    (hsupp : mbar.primeFactors = m.primeFactors)
    (hfour : 4 ∣ m → 4 ∣ mbar) (i : ℕ) :
    Nat.gcd (b ^ (τ * i) - 1) m = mbar * Nat.gcd i (m / mbar) := by
  have hmbar0 : mbar ≠ 0 := by
    rw [hmbar]
    exact Nat.gcd_ne_zero_right hm
  have hmbar_dvd_m : mbar ∣ m := by
    rw [hmbar]
    exact Nat.gcd_dvd_right _ _
  by_cases hi : i = 0
  · subst i
    simp only [mul_zero, pow_zero, Nat.reduceSubDiff, Nat.gcd_zero_left]
    exact (Nat.mul_div_cancel' hmbar_dvd_m).symm
  have hpow0 : b ^ (τ * i) - 1 ≠ 0 := by
    have : 0 < τ * i := Nat.mul_pos hτ (Nat.pos_of_ne_zero hi)
    exact (Nat.sub_ne_zero_iff_lt.mpr (Nat.one_lt_pow this.ne' (by omega)))
  have hdiv0 : m / mbar ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hmbar_dvd_m)
      (Nat.pos_of_ne_zero hmbar0)
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_right hm)
    (mul_ne_zero hmbar0 (Nat.gcd_ne_zero_right hdiv0))
  intro p
  by_cases hp : p.Prime
  · have hpowτ0 : b ^ τ - 1 ≠ 0 := by
      exact Nat.sub_ne_zero_iff_lt.mpr (Nat.one_lt_pow hτ.ne' (by omega))
    have hmbarfac : mbar.factorization p =
        min ((b ^ τ - 1).factorization p) (m.factorization p) := by
      rw [hmbar, Nat.factorization_gcd hpowτ0 hm, Finsupp.inf_apply]
    have hmbarpadic : padicValNat p mbar =
        min (padicValNat p (b ^ τ - 1)) (padicValNat p m) := by
      simpa only [Nat.factorization_def _ hp] using hmbarfac
    rw [Nat.factorization_gcd hpow0 hm, Nat.factorization_mul hmbar0
      (Nat.gcd_ne_zero_right hdiv0), Nat.factorization_gcd hi hdiv0,
      Finsupp.inf_apply, Finsupp.add_apply, Finsupp.inf_apply,
      Nat.factorization_div hmbar_dvd_m]
    by_cases hpm : p ∣ m
    · have hpmbar : p ∣ mbar := by
        have hmem : p ∈ mbar.primeFactors := by
          rw [hsupp]
          exact (Nat.mem_primeFactors_of_ne_zero hm).2 ⟨hp, hpm⟩
        exact ((Nat.mem_primeFactors_of_ne_zero hmbar0).1 hmem).2
      have hpx : p ∣ b ^ τ - 1 := by
        exact hpmbar.trans (hmbar.symm ▸ Nat.gcd_dvd_left _ _)
      have hpnb : ¬ p ∣ b := by
        intro hpb
        have hpone : p ∣ 1 := by
          rw [← hbm.gcd_eq_one]
          exact Nat.dvd_gcd hpb hpm
        exact hp.not_dvd_one hpone
      have hpnbpow : ¬ p ∣ b ^ τ := fun h => hpnb (hp.dvd_of_dvd_pow h)
      by_cases hp2 : p = 2
      · subst p
        by_cases h4m : 4 ∣ m
        · have h4x : 4 ∣ b ^ τ - 1 := (hfour h4m).trans
            (hmbar.symm ▸ Nat.gcd_dvd_left _ _)
          rw [pow_mul, Nat.factorization_def _ Nat.prime_two,
            Nat.factorization_def _ Nat.prime_two,
            Nat.factorization_def _ Nat.prime_two,
            padicValNat_pow_sub_one_eq_add Nat.prime_two
              (Nat.one_lt_pow hτ.ne' (by omega)) hi hpx hpnbpow (fun _ => h4x)]
          rw [Finsupp.tsub_apply]
          simp only [Nat.factorization_def _ Nat.prime_two]
          rw [hmbarpadic]
          exact min_add_eq_min_add_min_tsub _ _ _
        · have hmfac : m.factorization 2 = 1 := by
            have hpos : 0 < m.factorization 2 :=
              Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm hpm
            have hlt : m.factorization 2 < 2 := by
              contrapose! h4m
              exact (Nat.prime_two.pow_dvd_iff_le_factorization hm).2 h4m
            omega
          have hmbarfac2 : mbar.factorization 2 = 1 := by
            have hpos : 0 < mbar.factorization 2 :=
              Nat.Prime.factorization_pos_of_dvd Nat.prime_two hmbar0 hpmbar
            have hle := (Nat.factorization_le_iff_dvd hmbar0 hm).2 hmbar_dvd_m 2
            omega
          have hleft : min ((b ^ (τ * i) - 1).factorization 2) (m.factorization 2) = 1 := by
            rw [hmfac, min_eq_right]
            exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpow0 (by
              have hbodd : Odd b := Nat.not_even_iff_odd.mp (by
                simpa only [even_iff_two_dvd] using hpnb)
              have hpodd : Odd (b ^ (τ * i)) := hbodd.pow
              have hone : Odd (1 : ℕ) := odd_one
              exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hpodd hone))
          rw [hleft, hmbarfac2, Finsupp.tsub_apply, hmfac, hmbarfac2]
          simp
      · rw [pow_mul, Nat.factorization_def _ hp, Nat.factorization_def _ hp,
          Nat.factorization_def _ hp,
          padicValNat_pow_sub_one_eq_add hp
            (Nat.one_lt_pow hτ.ne' (by omega)) hi hpx hpnbpow (fun h => (hp2 h).elim)]
        rw [Finsupp.tsub_apply]
        simp only [Nat.factorization_def _ hp]
        rw [hmbarpadic]
        exact min_add_eq_min_add_min_tsub _ _ _
    · have hpmbar : ¬ p ∣ mbar := fun h => hpm (h.trans hmbar_dvd_m)
      simp [Nat.factorization_eq_zero_of_not_dvd hpm,
        Nat.factorization_eq_zero_of_not_dvd hpmbar]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Vandehey, Claim 4.5.**  Starting from a divisor `m'` with the full prime
support of `m` (and with `4` preserved), put `τ = ord(b,m')` and
`mbar = gcd(b^τ-1,m)`.  Then the reduced denominator after the `i`-th shift is
controlled exactly by `gcd(i,m/mbar)`. -/
theorem gcd_pow_orderOf_sub_one_eq
    (b m m' : ℕ) (hb : 2 ≤ b) (hm : m ≠ 0) (hm'dvd : m' ∣ m)
    (hbm : Nat.Coprime b m)
    (hsupp : m'.primeFactors = m.primeFactors)
    (hfour : 4 ∣ m → 4 ∣ m') (i : ℕ) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    Nat.gcd (b ^ (τ * i) - 1) m = mbar * Nat.gcd i (m / mbar) := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  have hm'cop : Nat.Coprime b m' := hbm.of_dvd_right hm'dvd
  have hτ : 0 < τ := by
    dsimp [τ]
    exact orderOf_pos_iff.mpr
      ((ZMod.isUnit_iff_coprime b m').mpr hm'cop).isOfFinOrder
  have hpowgt : 1 < b ^ τ := Nat.one_lt_pow hτ.ne' (by omega)
  have hm'pow : m' ∣ b ^ τ - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpowgt.le]
    push_cast
    dsimp [τ]
    rw [pow_orderOf_eq_one]
    simp
  have hm'mbar : m' ∣ mbar := by
    dsimp [mbar]
    exact Nat.dvd_gcd hm'pow hm'dvd
  have hmbar0 : mbar ≠ 0 := by
    dsimp [mbar]
    exact Nat.gcd_ne_zero_right hm
  have hmbar_m : mbar ∣ m := by
    dsimp [mbar]
    exact Nat.gcd_dvd_right _ _
  have hmbarsupp : mbar.primeFactors = m.primeFactors := by
    apply Finset.Subset.antisymm
    · exact Nat.primeFactors_mono hmbar_m hm
    · rw [← hsupp]
      exact Nat.primeFactors_mono hm'mbar hmbar0
  have hfourbar : 4 ∣ m → 4 ∣ mbar := fun h4 => (hfour h4).trans hm'mbar
  exact gcd_pow_mul_sub_one_eq hb hτ hm hbm rfl hmbarsupp hfourbar i

/-- Claim 4.5 specialized to the supported rounded divisor from equations
(12)--(13), the form used in Proposition 4.1. -/
theorem gcd_pow_rounded_orderOf_sub_one_eq
    (b m : ℕ) (x : ℝ) (hb : 2 ≤ b) (hm : m ≠ 0)
    (hbm : Nat.Coprime b m) (hx0 : 0 ≤ x) (hx1 : x < 1) (i : ℕ) :
    let m' := roundedDivisor m x
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    Nat.gcd (b ^ (τ * i) - 1) m = mbar * Nat.gcd i (m / mbar) := by
  exact gcd_pow_orderOf_sub_one_eq b m (roundedDivisor m x) hb hm
    (roundedDivisor_dvd hm hx0 hx1) hbm
    (roundedDivisor_primeFactors hm hx0 hx1)
    (four_dvd_roundedDivisor hm x) i

end NormalNumbers.VandeheyKorobov
