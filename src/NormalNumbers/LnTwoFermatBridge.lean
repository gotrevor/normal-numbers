/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoPrimeWindow

/-!
# The Fermat-quotient bridge (R3): Glaisher / Z.-H. Sun congruence

Lane-2 target 3 (2026-08-29 operator brief).  Turns the provenance note in
`LnTwoPrimeWindow.lean`'s node docstring into a theorem:

  `lnTwoNum (p−1) ≡ lcmRange (p−1) · q_p(2)  (mod p)`  for odd primes `p`,

where `q_p(2) = (2^{p−1} − 1)/p mod p` is the Fermat quotient.  The
statement SHAPE is settled — probe-verified exactly for all 2261 primes
`3 ≤ p < 20000` with zero failures (`experiments/lntwo_fermat_bridge.py`),
unit pinned as `L_{p−1} mod p`.  Formalize exactly this form.

Route (per the probe's derivation): `A_{p−1}/L_{p−1} = Σ_{k=1}^{p−1}
2^{p−1−k}/k ≡ 2^{p−1}·Σ 1/(k·2^k) (mod p)`; Fermat little theorem gives
`2^{p−1} ≡ 1`, and Z.-H. Sun's congruence `Σ_{k=1}^{p−1} 1/(k·2^k) ≡
q_p(2) (mod p)` closes it.  All manipulations are exact modular
arithmetic over `ZMod p` (units: every `k ≤ p−1` and `2` are invertible).
-/

namespace NormalNumbers

/-- The Fermat quotient `q_p(2) = ((2^{p−1} − 1)/p) mod p`.  For an odd
prime `p` the division is exact (Fermat's little theorem). -/
def fermatQuotient2 (p : ℕ) : ℕ := (2 ^ (p - 1) - 1) / p % p

/-- **The Fermat-quotient bridge (Glaisher / Z.-H. Sun)**: at a
prime-adjacent index the surrogate numerator carries the Fermat quotient,
`A_{p−1} ≡ L_{p−1} · q_p(2) (mod p)`.  Probe-verified for all primes
`3 ≤ p < 20000`; statement shape frozen — formalize exactly this form. -/
theorem lnTwoNum_modEq_fermatQuotient {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    lnTwoNum (p - 1) ≡ lcmRange (p - 1) * fermatQuotient2 p [MOD p] := by
  sorry

end NormalNumbers
