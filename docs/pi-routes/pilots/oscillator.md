# Oscillator pilot

Read the shared pilot contract.  Prove or refute the frozen pilot targets
`CubicBlindAtThree` and `QuarticRejectsThree` in `RoundTwoOscillator.lean`.

The cheap algebra that must work before any search:

1. For every polynomial P of degree at most 3,
   `P(0)+P(3) = (P''+P)(1)+(P''+P)(2)`.
   Thus positive residual on [0,4] makes the left side positive.
2. The explicit rational quartic
   `P = -X^4+8X^3-8X^2-32X+65/4` has residual
   `X*(4-X)*(X-2)^2+1/4 > 0` on [0,4], but `P(0)+P(3)=-1/2`.
   This positive control matters: it distinguishes a degree obstruction from an
   instrument incapable of recognizing ANY useful polynomial.

Connect the first result to the exact certificate proposal: x=3 avoids the
one-letter binary word [1], so degree-at-most-3 cannot supply even that certificate.
The quartic excludes only x=3; it is NOT a certificate for all [1]-avoiding x,
since x=4 is another such point.  Do not claim otherwise.

After those small results, use remaining budget for the actual mechanism question:
can a word-dependent certificate do more than isolate pi into a previously known
word-containing cylinder?  A possible structural target is a positive quadrature
formula showing a fixed-degree blind interval around pi, uniform over coefficients.
State any generalization precisely before proving it.  Do not make a long detour
through the routine oscillator integration bridge.

Deliver exact theorem names, assumptions, axiom checks, and a scope judgment.
Retire the universal cubic family if proved impossible; do not retire all degrees
or assert that equivalence alone refutes the whole oscillator approach.
