# Bounded Padé coefficient-cost test

**The finite construction gate passed.**  The eight forms with indices 8,...,15
admit an exact integer combination with logarithm coefficient 2^21, integral
constant 1453635, and weighted error budget

\[
\frac{2468804318}{30517578125}=0.080897779892224<\frac18<\frac14.
\]

`PadeCost.best_witness_equations`, `best_witness_budget`, and
`best_witness_passes` prove these claims in Lean.  This is one finite instance
of cheap synthesis.  It does not prove the all-k `PadeCheapDyadic` premise,
arbitrarily long runs, or disjunctivity of ln(2).

## Fixed test and result

The search used n=4,8,16,32, width=n, and binary exponents 0≤m≤4n.  The success
gate was sum_j |u_j|5^(-n-j)<1/4, with exact equations

\[
\sum_j u_jA_{n+j}=2^m,\qquad \sum_j u_jB_{n+j}=z\in\mathbb Z.
\]

No larger windows or exponent ranges were added after seeing the outcome.

| Starting index / width | Binary exponents | Outcome |
|---|---|---|
| 4 / 4 | 0 through 16 | All excluded; every feasible vector costs at least 0.3057 |
| 8 / 8 | 0 through 32 | m=21 and m=22 pass; all other exponents excluded |
| 16 / 16 | 0 through 64 | All excluded; every feasible vector costs at least 0.3079 |
| 32 / 32 | 0 through 128 | All excluded; every feasible vector costs at least 2.4151 |

There are 244 grid points.  Exact rational dual bounds exclude 242 of them,
regardless of coefficient magnitude.  Only the other two require optimization.
`BoundedCostExclusions`, `WindowCostLowerBounds`, and `BoundedCostResult` state
the finite results in Lean; the full table is exact Python evidence, not yet a
kernel proof of all exclusions.  The generic inequality supporting the
certificates, `weighted_dual_bound`, is proved.

The m=21 coefficient vector is

```text
[-9037, -86624, 0, -214899, -1231047, -4837440, -1, 159938]
```

The independently optimized m=22 vector has budget
4938353788/30517578125 ≈ 0.161820.  It is not optimal: simply doubling the m=21
vector gives a slightly smaller budget.  These two successes concern the same
near-integer return at adjacent binary positions; they are not two independent
sources of digit information.  No optimality claim is made for either optimizer
output.

## Why the exclusions are bounds, not failed searches

Write E_j=A_j log 2-B_j and

\[
R=\max_{n\le j<n+w}5^j|E_j|.
\]

For every feasible coefficient vector,

\[
\operatorname{dist}(2^m\log2,\mathbb Z)
\le\left|\sum_j u_jE_{n+j}\right|
\le R\sum_j|u_j|5^{-(n+j)}.
\]

The script bounds the left side from below and R from above using a 512-term
Mercator partial sum L and U=L+1/(513·2^512).  `mercator_enclosure` proves the
general enclosure used here.  Every calculation after that enclosure is rational
arithmetic.  Stored lower bounds are rounded **down** to multiples of 10^(-12).
The complete rational L,U and the reconstruction script are preserved.

This pruning uses an enclosure of ln(2) itself.  It is a certificate search
guided by actual finite orbit positions, not an independent argument forcing
new visits.  That distinction is essential when interpreting the positive result.

## Optimizer, controls, and verification

An exact unimodular column reduction solves the two integer equations and
produces an affine lattice of feasible vectors.  The coordinate weights are
5^(w-1-j), so ordinary integer L1 cost is exactly the desired weighted cost
times a common factor.  Rational LLL reduction, nearest-plane rounding, and a
bounded coordinate improvement search supply candidate vectors.  LLL has a
20-second / 10000-step cap per call; local descent has at most 20 passes and one
finite neighbor pass.  Only two seven-dimensional lattice searches were needed.

The installed SymPy 1.14 LLL raised an internal assertion on the initial basis.
The script does not suppress it: it uses a small exact-rational implementation
and checks the reduced basis, every LLL inequality, the unimodular determinant,
and the transformation identity.  SymPy remains an independent integer-matrix
checker.

Controls ran before the test:

- Positive: the pair at n=1,2, coefficients (1,1), gives coefficient 16,
  constant 11, and budget 6/25<1/4.  The optimizer recovers it, and the dual bound
  does not reject it.
- Negative: the n=5,6 modulo-five obstruction rejects dyadic synthesis.
- Delivered-witness check: a second verifier computes A_n by the central
  Delannoy binomial formula and B_n by its finite product-sum formula, independently
  of the recurrence used to generate the search.  It checks all equalities,
  budgets, dual exclusions, and grid coverage.  Altering one witness coefficient
  makes that verifier reject the report.

Reproduce with:

```sh
./scripts/ln_two_pade_cost.py --controls
./scripts/ln_two_pade_cost.py
lake build NormalNumbers.LnTwoRoutes.PadeCost
```

Output: `docs/ln-two-routes/cost-probe.json`.

## Research consequence

The original large Bezout coefficients were not an intrinsic obstacle at the
successful finite window.  The construction can pass a nontrivial cost gate.
At three other windows the chosen gate is genuinely excluded over the stated
exponent ranges, so merely increasing the Padé order is not uniformly helpful.

The outstanding work is a parameter-dependent argument producing cheap,
word-targeted combinations without first finding the desired orbit visit.
This bounded test supplies no such argument.  The Maze records the finite
positive reopening and keeps that uniform question explicit.
