# Creative pass: quadratic-twisted dual-radix rigidity

**One exploratory conjecture emerged; no proof campaign is admitted.**  The new
ingredient being considered is simultaneous exact arithmetic in two independent
bases, joined by a quadratic field.  This is not a claim that merely changing
base forces normality, and no novelty-in-print claim is made.

## The concrete structure

The binary BBP formula gives a rational-coefficient base-16 series for pi.
Pairing the Taylor terms of `atan(1/sqrt(3)) = pi/6` gives

\[
\sqrt3\,\pi
 =6\sum_{k\ge0}9^{-k}
 \left(\frac1{4k+1}-\frac1{3(4k+3)}\right)
 =\sum_{n\ge1}\frac{144n}{(4n-3)(4n-1)}9^{-n}.
\]

Thus pi and sqrt(3)*pi have rational-kick descriptions in independent bases 16
and 9.  `independent_radix_powers` verifies the base independence.  The ternary
formula is recorded as `PiTernaryIdentity`, an explicit unproved HasSum input in
this new module.  Its derivation is elementary, and the arctangent value is already
`Real.arctan_inv_sqrt_three` in mathlib.  The binary formula is proved in
`PiBBPProof.lean`; packaging the two as `PiDualData` remains an explicit input.
Completing those routine bridges is not the proposed research.

## The conjecture, stated without pi in its hypotheses

`QuadraticDualRadixRigidity` asks:

> If an irrational x is a rational-polynomial-kick BBP value in base 16, and
> sqrt(3)*x is such a value in base 9, then x is disjunctive in at least one of
> bases 16 and 9.

`pi_disjunctive_of_dualRigidity` proves the conditional transfer, given the
conjecture and `PiDualData`.  The conclusion concerns **x itself** in both bases.
We do not transfer disjunctivity through multiplication by sqrt(3).

This is an exploratory rigidity principle, not an established theorem or an
estimate known to be easier than pi disjunctivity.  The existing BBP-normality
expectation is already stronger than what the pi instance would need.  The reason
to examine this restricted class is the extra compatibility equation, not the
number of consequences of the conjecture.

## Proposed arithmetic mechanism and its first test

Let A_n be the rational binary partial sum approaching pi, and B_m the rational
ternary partial sum approaching sqrt(3)*pi.  The quadratic expression

\[
3A_n^2-B_m^2
\]

approaches zero.  Clearing denominators makes it an integer norm, with a known
conjugate factor.  The proposed leverage would be to combine restrictions from
**two forbidden-word languages** into an additional norm bound that the exact
arithmetic cannot satisfy.  This uses exact coupled approximations, rather than
assuming that a binary orbit closure is invariant under multiplication by 3.
The base-nine restriction on x must be applied to B_m/sqrt(3), not to B_m.
Thus one surrogate is rational and the other quadratic; treating the twist as
digit-preserving would be an invalid shortcut.

That word-dependent norm bound is missing.  The obvious unweighted norm does not
give it.  `scripts/pi_dual_radix_probe.py` computes exact rational values and the
cleared integer for five pairs; `NormPreflight` states the finite checked claims
in Lean without promoting the Python check to a kernel proof.
`NormBitLengthPreflight` records the finite integer-size claims.  Product
denominators over-clear the norm: `ReducedNormPreflight` records the stronger
check using the numerator after full rational cancellation.

| n, m | Raw norm, approximately | Product-cleared bits | Fully reduced numerator bits |
|---|---:|---:|---:|
| 2, 3 | 2.14e-3 | 55 | 38 |
| 4, 5 | 3.67e-5 | 126 | 87 |
| 8, 10 | 3.31e-10 | 298 | 200 |
| 16, 20 | 4.91e-20 | 630 | 455 |
| 32, 40 | 2.05e-39 | 1296 | 901 |

The probe verifies the clearing identity exactly.  Changing the coefficient 6
to 5 is a negative control: the raw expression stays above 8 in every tested
case, rather than tending numerically toward zero.  The known-answer positive
control takes Pell solutions p^2 - 3q^2 = 1 and applies the same norm computation
to A = q/p, B = 1.  All six controls return the exact cleared norm -1.
`pell_unit_norm_identity` proves the underlying equality
3(q/p)^2 - 1 = -1/p^2.  Thus the computation recognizes small unit norms when
they occur.  No pi digit census was used.
These finite results do not prove an asymptotic obstruction or rule out optimized
auxiliary forms.  They show that the naive norm is not close to the `<1` integer
contradiction it would need at these scales.

## What this pass did and did not find

There is a precise new question and a concrete compatibility relation to study.
There is still no reasoned construction of the word-dependent norm bound.
Cobham-style intuition is only an analogy: neither series makes the digits
automatic, and density of a two-parameter orbit would not settle either axis.
The earlier recognizer/path and irrationality-measure controls still apply.

The Maze parks this proposal pending a specific construction that uses forbidden
words to improve the norm budget.  Another representation, more precision in the
same norm, or formalizing the arctangent bridge does not meet that condition.
No treadmill was launched for this proposal.
