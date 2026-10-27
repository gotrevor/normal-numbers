# Oscillator pilot result

Module: `src/NormalNumbers/PiDisjunctiveRoutes/RoundTwoOscillator.lean`
(not imported from the root; the parent decides integration).

## Proved (axioms: propext, Classical.choice, Quot.sound)

- `cubic_identity`: for `deg P ≤ 3`, `P(0)+P(3) = R(1)+R(2)`, `R = P''+P`.
- `cubicBlindAtThree : CubicBlindAtThree`.
- `quarticRejectsThree : QuarticRejectsThree` (positive control; rejects only x=3).
- `quarticQuadratureIdentity : QuarticQuadratureIdentity` (via the five coefficients,
  `Polynomial.as_sum_range'`, then `ring`).
- `quarticEndpointObstruction : QuarticEndpointObstruction`.

## Scope

Both 3 and 4 avoid the word `[1]`, so no oscillator certificate of degree ≤ 4
supplies `OscillatorCertificateSupply` even for `w = [1]`.  Nothing is claimed for
degree ≥ 5, nor for the oscillator approach as a whole.  The degree-5/6 search and
the uniform "blind interval around pi" question were not attempted (budget).

## Prospective Maze entry (parent to integrate)

- Route: fixed-degree (≤ 4) positive-oscillator certificates for pi digit words.
- Aliases: cubic/quartic `P''+P > 0` certificates, low-degree sine-kernel test functions.
- Crux: positive quadrature for `R` with nodes in [0,4] forces a positive combination
  of `P(0)+P(x)` at two `[1]`-avoiding points.
- Obstruction: `quarticEndpointObstruction` (degree ≤ 4); `cubicBlindAtThree`.
- Reopen: a degree ≥ 5 certificate rejecting all of `{3,4} ∪ …` avoiding points, or
  a proof that no positive quadrature of that shape exists at degree d.
