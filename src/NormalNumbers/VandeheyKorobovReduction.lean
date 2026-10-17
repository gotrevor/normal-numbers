/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovBigM

/-!
# Reduction of the shifted coefficients in Vandehey's Korobov estimate

This file supplies the exact cancellation step used after Claims 4.4--4.6 in the
proof of Proposition 4.1.  Cancelling the gcd of `u` and the modulus preserves
the additive phase, and coprimality of the original coefficient with the modulus
ensures that the resulting numerator and denominator are coprime.
-/

namespace NormalNumbers.VandeheyKorobov

open Erdos438.Fourier

/-- Multiplication by a coefficient coprime to the modulus does not change the
gcd of a natural factor with that modulus. -/
lemma int_gcd_mul_natCast_eq_of_isCoprime
    (a : ℤ) (u m : ℕ) (ha : IsCoprime a (m : ℤ)) :
    Int.gcd (a * (u : ℤ)) (m : ℤ) = Nat.gcd u m := by
  have haNat : Nat.Coprime a.natAbs m := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] at ha
    simpa using ha
  rw [Int.gcd_eq_natAbs, Int.natAbs_mul]
  simp only [Int.natAbs_natCast]
  exact haNat.gcd_mul_left_cancel u

/-- Exact phase cancellation and the reduced coprimality package.  This is the
algebraic step that permits the hypothesis of Proposition 4.1 to be applied to
each shifted correlation sum. -/
theorem phase_reduce_of_isCoprime
    (a : ℤ) (u x m : ℕ) (hm : m ≠ 0) (ha : IsCoprime a (m : ℤ)) :
    let g := Nat.gcd u m
    phase m (a * (u : ℤ)) (x : ℤ) =
        phase (m / g) ((a * (u : ℤ)) / (g : ℤ)) (x : ℤ) ∧
      IsCoprime ((a * (u : ℤ)) / (g : ℤ)) ((m / g : ℕ) : ℤ) := by
  dsimp only
  let c : ℤ := a * (u : ℤ)
  let g := Nat.gcd u m
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right u (Nat.pos_of_ne_zero hm)
  have hgm : g ∣ m := by
    dsimp [g]
    exact Nat.gcd_dvd_right u m
  have hgc : (g : ℤ) ∣ c := by
    have hgu : g ∣ u := by
      dsimp [g]
      exact Nat.gcd_dvd_left u m
    obtain ⟨v, hv⟩ := hgu
    refine ⟨a * v, ?_⟩
    dsimp [c]
    rw [hv]
    push_cast
    ring
  have hgmZ : (g : ℤ) ∣ (m : ℤ) := by exact_mod_cast hgm
  have hgred : IsCoprime (c / (g : ℤ)) ((m : ℤ) / (g : ℤ)) := by
    have hcgm : Int.gcd c (m : ℤ) = g := by
      dsimp [c, g]
      exact int_gcd_mul_natCast_eq_of_isCoprime a u m ha
    have hbase := isCoprime_div_gcd_div_gcd (R := ℤ) (p := c) (q := (m : ℤ))
      (by exact_mod_cast hm)
    rw [← Int.coe_gcd, hcgm] at hbase
    exact hbase
  have hmdiv0 : m / g ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hgm) hgpos)
  constructor
  · unfold phase
    congr 1
    have hc : c / (g : ℤ) * (g : ℤ) = c := Int.ediv_mul_cancel hgc
    have hmn : m / g * g = m := Nat.div_mul_cancel hgm
    have hcC : (((c / (g : ℤ)) : ℤ) : ℂ) * g = c := by exact_mod_cast hc
    have hmC : ((m / g : ℕ) : ℂ) * g = m := by exact_mod_cast hmn
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    have hcu : a * (u : ℤ) = c := rfl
    have hgdef : Nat.gcd u m = g := rfl
    rw [hcu, hgdef]
    rw [← hcC, ← hmC]
    field_simp [hgC]
  · rw [Int.natCast_ediv]
    simpa [c] using hgred

/-- A rewrite-friendly form of `phase_reduce_of_isCoprime`: callers can supply
an independently proved exact gcd, notably Vandehey's Claim 4.5. -/
theorem phase_reduce_of_gcd_eq
    (a : ℤ) (u x m g : ℕ) (hm : m ≠ 0) (ha : IsCoprime a (m : ℤ))
    (hg : Nat.gcd u m = g) :
    phase m (a * (u : ℤ)) (x : ℤ) =
        phase (m / g) ((a * (u : ℤ)) / (g : ℤ)) (x : ℤ) ∧
      IsCoprime ((a * (u : ℤ)) / (g : ℤ)) ((m / g : ℕ) : ℤ) := by
  subst g
  exact phase_reduce_of_isCoprime a u x m hm ha

/-- Claim 4.5 fed directly into phase cancellation.  The denominator of the
`i`-th shifted correlation is exactly `m / (mbar * gcd i (m / mbar))`, and its
displayed numerator is coprime to that denominator. -/
theorem shifted_phase_reduce
    (b m m' : ℕ) (a : ℤ) (i n : ℕ) (hb : 2 ≤ b) (hm : m ≠ 0)
    (hm'dvd : m' ∣ m) (hbm : Nat.Coprime b m)
    (hsupp : m'.primeFactors = m.primeFactors)
    (hfour : 4 ∣ m → 4 ∣ m') (ha : IsCoprime a (m : ℤ)) :
    let τ := orderOf (b : ZMod m')
    let mbar := Nat.gcd (b ^ τ - 1) m
    let d := Nat.gcd i (m / mbar)
    phase m (a * ((b : ℤ) ^ (i * τ) - 1)) ((b : ℤ) ^ (n + 1)) =
        phase (m / (mbar * d))
          ((a * ((b : ℤ) ^ (i * τ) - 1)) / (mbar * d : ℕ))
          ((b : ℤ) ^ (n + 1)) ∧
      IsCoprime
        ((a * ((b : ℤ) ^ (i * τ) - 1)) / (mbar * d : ℕ))
        ((m / (mbar * d) : ℕ) : ℤ) := by
  dsimp only
  let τ := orderOf (b : ZMod m')
  let mbar := Nat.gcd (b ^ τ - 1) m
  let d := Nat.gcd i (m / mbar)
  have hg : Nat.gcd (b ^ (i * τ) - 1) m = mbar * d := by
    simpa only [τ, mbar, d, Nat.mul_comm] using
      (gcd_pow_orderOf_sub_one_eq b m m' hb hm hm'dvd hbm hsupp hfour i)
  have hred := phase_reduce_of_gcd_eq a (b ^ (i * τ) - 1) (b ^ (n + 1)) m
    (mbar * d) hm ha hg
  have hp : 1 ≤ b ^ (i * τ) := one_le_pow₀ (by omega)
  simpa [τ, mbar, d, Int.natCast_sub hp] using hred

end NormalNumbers.VandeheyKorobov
