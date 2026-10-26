/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.PrimeReservoirOrbit

/-! # Review: the quadratic collapse is specific to cutoff 4n

Moving the lower cutoff to 6n keeps all selected primes above 4n, so
the unique-denominator argument survives.  The exact finite witness below
refutes extending the 64/p exit formula to this narrower window.  This
does NOT prove nonvanishing transfers at infinitely many indices or any
disjunctivity statement.  Exit transfers still cancel in the sum R+S.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffReview

def rationalExit (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (16 : ℚ) ^ (n + 1 - j) *
    ((if Nat.Prime (8*j+1) ∧ s*n < 8*j+1 ∧ 8*j+1 ≤ s*(n+1)
      then 4 / (8*(j : ℚ)+1) else 0) -
     (if Nat.Prime (8*j+5) ∧ s*n < 8*j+5 ∧ 8*j+5 ≤ s*(n+1)
      then 1 / (8*(j : ℚ)+5) else 0))

@[blueprint (title := "Cutoff 6n has a 39/89 exit, not the cutoff-4 Euler residue")]
theorem exit_six_fourteen : rationalExit 6 14 = 2945 + 39/89 := by decide +kernel

theorem exit_six_fourteen_fract : Int.fract (rationalExit 6 14) = 39/89 := by
  decide +kernel

theorem not_same_exit_collapse :
    Int.fract (rationalExit 6 14) ≠ Int.fract (64/89 : ℚ) := by decide +kernel

/-- The numerator of the contribution when a selected prime leaves cutoff s.
Use only primes p ≡ 1 mod 4 with p/8 < p/s (i.e. the prime actually entered). -/
def exitNumerator (s p : ℕ) : ℤ :=
  (if p % 8 = 1 then 4 else -1) * 16 ^ (p / s + 1 - p / 8)

/-- New arithmetic identity to prove; derived by cubing the numerator and
Euler's criterion.  Exact probe: all 1123 applicable primes up to 20000.
For p ≡ 1 mod 6 the numerator cubed is 64^3; for p ≡ 5 mod 6 it is 1024.
This is an unproved formal node, not a kernel-certified general identity. -/
def CutoffSixCubicLaw : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 4 = 1 → p / 8 < p / 6 →
    ((exitNumerator 6 p : ℤ) : ZMod p) ^ 3 =
      if p % 6 = 1 then (64 : ZMod p)^3 else 1024

/-- p = 24k+1 subclass: a proved cubic identity. -/
theorem exit_cube_24k_one (k : ℕ) [Fact (Nat.Prime (24*k+1))] :
    ((4 : ZMod (24*k+1)) * 16^(k+1))^3 = 64^3 := by
  have he := two_pow_half_eq (p := 24*k+1) (by omega)
  rw [if_pos (by omega), show (24*k+1)/2 = 12*k by omega] at he
  have hnum : (4 : ZMod (24*k+1)) * 16^(k+1) = 64 * 2^(4*k) := by
    rw [pow_succ, show (16 : ZMod (24*k+1)) = 2^4 by norm_num, ← pow_mul]
    ring
  rw [hnum, mul_pow, ← pow_mul, show 4*k*3 = 12*k by omega, he, mul_one]

/-- A finite-prime regrouping suggested by the lane's exact recurrence:
entry plus exit for p yields 4*q_p/2^(p-1), with q_p an integer.
The infinite identity is recorded below as an unproved node. -/
def halfFermatQuotient (p : ℕ) : ℤ :=
  ((if p % 8 = 1 then 1 else -1) * (2 : ℤ)^((p-1)/2) - 1) / p

def RhoDyadicIdentity : Prop :=
  reservoirConst = ∑' p : ℕ,
    if Nat.Prime p ∧ p % 4 = 1 then
      4 * (halfFermatQuotient p : ℝ) / 2^(p-1) else 0

example : halfFermatQuotient 5 = -1 := by decide +kernel
example : halfFermatQuotient 13 = -5 := by decide +kernel
example : halfFermatQuotient 17 = 15 := by decide +kernel

#print axioms exit_six_fourteen
#print axioms not_same_exit_collapse
#print axioms exit_cube_24k_one

end NormalNumbers.PiDisjunctiveRoutes.CutoffReview
