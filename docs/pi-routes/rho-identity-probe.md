# Numerical identity probe for the reservoir constant

The probe found no candidate identity.  This is a numerical search result, not a proof that an identity does not exist.

```
rho = -0.2539760248571803634458533679280329700728605454770990802...
```

The constant is `reservoirConst` in `PrimeReservoirOrbit.lean`: the sum of `reservoirKick k / 16^(k+1)`.  The script evaluates that definition using exact rational arithmetic.  The proved kick bound gives a truncation error at N terms of at most `10 / ((N+1)*16^N)`.

A second implementation sums the prime regrouping

```
sum over primes p = 1 mod 4 of
    4 * (((2|p)*2^((p-1)/2) - 1)/p) / 2^(p-1).
```

Here `(2|p)` is +1 for p = 1 mod 8 and -1 for p = 5 mod 8.  Every numerator division is checked exactly.  The infinite regrouping remains the open Lean statement `RhoDyadicIdentity`; this computation does not prove it.  The two arithmetic implementations agree through the requested precision, up to 800 digits.

The search runs PSLQ at 200, 400, and 800 decimal digits, with 40 working guard digits and tolerances 10^-150, 10^-350, and 10^-750.  At each precision it tests these twelve families:

| Family | PSLQ maxcoeff parameter |
|---|---:|
| Rational relation with 1 | 10^20 |
| Linear relation with pi and 1 | 10^12 |
| Linear relation with pi, log(2), and 1 | 10^10 |
| Linear relation with pi, log(2,3,5,7), and 1 | 10^8 |
| Linear relation with pi, atan(1/2), log(2,3,5,7,17), and 1 | 10^6 |
| Linear relation with pi, pi^2, sqrt(2), sqrt(3), Catalan, zeta(3), and 1 | 10^6 |
| Polynomial relation in rho and pi of total degree at most 2 | 10^6 |
| Polynomial relation in rho of degree at most d, separately for d=2,3,4,5,6 | 10^8 |

All 36 calls returned no relation.  All stopped upon exceeding the numerical norm threshold, before their 5000-step cap; the longest took 1043 steps.  These parameters and floating-point norm estimates are not a certified exclusion of every coefficient vector in a box.

At each precision the positive control recovered the planted identity for `(7*pi - 3*log(2) + 5)/11`.  Perturbing that value by 10^-40 made the recovered identity fail the acceptance tolerance.  The measured computation time was 5.527 seconds, excluding dependency installation.

The useful conclusion is narrow: this probe supplied no simple identity to pursue.  It supplies no evidence about disjunctivity itself and no impossibility theorem for the reservoir route.

Reproduce from this repository root with `./scripts/pi_rho_identity_probe.py`.  Exact decimal interval endpoints, bases, parameters, and termination messages are in `docs/pi-routes/rho-identity-probe.json`.  Full verbose logs are in `tmp/20261026-rho-identity/`.
