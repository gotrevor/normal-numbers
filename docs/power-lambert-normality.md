# Perfect-power Lambert constants: disjunctive and nonnormal

For integers `b>=2` and `r>=2`,

\[
S_{b,r}=\sum_{n\ge1}\frac1{b^{n^r}-1}
\]

is disjunctive in base `b` and is **not normal in base `b`**.  The theorem is
`ArithmeticDisjunctivity.powerLambert_disjunctive_not_normal` in
[`PowerLambertNonNormal.lean`](../src/NormalNumbers/PowerLambertNonNormal.lean).
The disjunctivity half comes from the [generic arithmetic theorem](arithmetic-disjunctivity.md).
The nonnormality half is `not_isNormal_powerLambert`.

Thus this arithmetic family separates arbitrary finite word occurrence from
normal word frequencies.  Its normality upgrade is refuted, rather than merely
abandoned as difficult.

## Proof of the obstruction

Remove the first eight summands, which have rational sum `q`, and write

\[
S_{b,r}=q+Y,\qquad
Y=\sum_{m\ge1}c_r(m)b^{-m},\qquad
c_r(m)=\#\{d>8:d^r\mid m\}.
\]

At `m=0` the formal coefficient is defined to be zero.  This exact regrouping is
`exists_rat_powerLambert_tail` in
[`PowerLambertTailExpansion.lean`](../src/NormalNumbers/PowerLambertTailExpansion.lean).

Counting multiples of each `d^r` and using `r>=2` gives

\[
\sum_{m<N}c_r(m)
\le N\sum_{d=9}^{\infty}\frac1{d^r}
\le N\sum_{d=9}^{\infty}\frac1{d(d-1)}
=\frac N8.
\]

The Lean proof uses finite sums and telescoping:
`prefix_tailPowerDivisorCount_bound` in
[`PowerLambertTailCoefficients.lean`](../src/NormalNumbers/PowerLambertTailCoefficients.lean),
with the helpers in `PowerLambertTailBounds.lean`.

The reusable carry estimate `orbit_sum_le_of_small_coefficients` applies to
**any** nonnegative integer coefficient sequence `f` with `f(0)=0` and prefix
sum at most `N/8`.  It proves

\[
\sum_{n<N}\{b^nY\}\le\frac{N+2}{8}.
\]

See [`SmallCoefficientMean.lean`](../src/NormalNumbers/SmallCoefficientMean.lean).
The integer head disappears modulo one; the nonnegative remaining tail bounds
the fractional part.  Summing the tails and using `b>=2` gives the displayed
geometric-series bound.

If `Y` were normal, Wall's criterion would make its radix orbit equidistributed.
Visits to `[1/2,1)` would have frequency `1/2`.  Each visit contributes at least
`1/2` to the orbit sum, whereas the displayed bound forces the visit frequency
to have upper limit at most `1/4`.  The formal contradiction is
`not_isNormal_of_orbit_sum_bound` in
[`ArithmeticMeanObstruction.lean`](../src/NormalNumbers/ArithmeticMeanObstruction.lean).
Finally, rational translation preserves normality (`isNormal_rat_mul_add`),
so `S_{b,r}=q+Y` is also nonnormal.

## Scope and controls

- The theorem covers every integer `r>=2` and every integer defining base `b>=2`.
- It does not decide normality for `r=1`, the ordinary Erdos--Borwein series.
  The finite control `linear_power_prefix_control` proves that the relevant
  coefficient sum at `N=12` is `3`, so the `N/8` premise already fails there.
- `square_tail_positive_control` proves `c_2(81)=1`: the arithmetic tail is
  nonzero after the rational head is removed.
- `GenericArithmeticNormality` states the proposed normality strengthening of
  `CoefficientSystem`.  `not_genericArithmeticNormality` refutes it with
  `powerDivisorCount 2` at base two.  The generic disjunctivity theorem remains valid.
- This result makes no assertion about simple normality, other bases of a fixed
  constant, or literature priority.  The investigation used local sources.

The Maze row **Normality upgrade for perfect-power Lambert constants** records
the refutation and links its declarations in `MazeAudit.lean`.  Read
[`MAZE.md`](../MAZE.md) before proposing an upgrade: no new technique can prove
normality for these exact constants in their defining bases.  A changed family
needs to evade the proved small-mean obstruction.  The `r=1` case remains a
different question.
