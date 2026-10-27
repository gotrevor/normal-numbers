# A higher-probability disjunctivity target

**Completed, 2026-10-27.**  The [generic arithmetic theorem](arithmetic-disjunctivity.md)
now proves disjunctivity of `sum 1/(b^(n^r)-1)` for every integer `b>=2`, `r>=1`.
`ArithmeticDisjunctivity.squareLambertBinaryDisjunctive` closes this proposal's
specific target.  Every formal gate below is discharged in
[`PowerLambertDisjunctivity.lean`](../src/NormalNumbers/PowerLambertDisjunctivity.lean).
The stronger normality target is now refuted for every `r>=2` in its defining
base: see the [normality boundary](power-lambert-normality.md) and
`ArithmeticDisjunctivity.not_isNormal_powerLambert`.
The remainder preserves the original recommendation, its then-open gates, and
the forecast made before the proof work.

Research recommendation, 2026-10-27.  Start with a successful arithmetic construction and extend it to a natural family whose coefficients it can control.  The proposed first target is

\[
S=\sum_{n\ge1}\frac1{2^{n^2}-1}.
\]

This is a Lambert series over the squares, defined without prescribing digits or choosing parameters to insert words.  It meets the broader objective of an explicit arithmetic constant.  It would not settle the digits of pi, log(2), or sqrt(2).  No claim about the literature status of this particular target is made; the present search was local.

The proposal and its gates are in [`SquareLambertProposal.lean`](../src/NormalNumbers/SquareLambertProposal.lean), namespace `NormalNumbers.SquareLambertProposal`.  `SquareLambertBinaryDisjunctive` is an **open target**, not a theorem.  Review [MAZE.md](../MAZE.md) before extending or retiring the route.

## Why this has a different risk profile

The repo already proves simultaneous disjunctivity for the ordinary Erdos--Borwein constants: `JointLambert.jointLambertDisjunctivity_unconditional`.  Its proof chooses an arithmetic progression, uses prime valuations to make all but one early coefficient integral after shifting, assigns the remaining coefficient to the desired word, and finds a prime candidate whose later carry tail is small.

For the proposed constant the expected geometric-series regrouping is

\[
S=\sum_{m\ge1}a_2(m)2^{-m},\qquad
a_2(m)=\#\{d\ge1:d^2\mid m\}
       =\prod_{p\mid m}\left(\left\lfloor\frac{v_p(m)}2\right\rfloor+1\right).
\]

The exact regrouping and factorization are recorded as `SquareLambertExpansion` and `SquareCoefficientFactorization`, still to be proved for the definitions in this module.  They give two concrete operations, recorded as `SquareLocalKill` and `SquareSingleWriter`:

- If a fresh prime has exact valuation two, it contributes a factor two to `a_2(m)`.  Using `j+1` distinct such primes makes `2^(j+1)` divide the coefficient in slot `j`.
- If `m=q^(2(A-1))*p` for distinct primes `p,q`, then `a_2(m)=A`.  One coefficient can therefore carry an arbitrary positive integer, including the even integers used by the existing word encoder.

The proved controls `square_coefficient_controls` check `a_2(18)=2`, `a_2(162)=3`, and `a_2(450)=4`.  They validate these small arithmetic examples, not infinite word supply.

## The exact reuse opportunity

The existing construction already has the needed parameter freedom:

1. Set its kill parameter `c=3`.  Its congruence `n+j ≡ P_j^(c-1) (mod P_j^c)` then gives exact valuation two at each of the distinct primes in `P_j`.
2. Set its survivor parameter to `oldA=2A-1`.  Its survivor is `q^(oldA-1)*p=q^(2(A-1))*p`.  `square_writer_parameter` verifies that parameter identity and the old parameter's lower bound.
3. Keep the existing ordinary-divisor tail estimate.  `squareDivisorCount_le_tau` and `square_tail_le_divisor_tail` are proved: the square-divisor coefficients and their tails are bounded by the ordinary divisor counterparts at every offset.

The source-level reuse is quite specific: `exists_joint_prime_candidates_rescaled` in `JointLambertRescaledPrimes.lean`, the arithmetic in `JointLambertArithmetic.lean`, and the candidate-selection proof in `JointLambertRescaledTail.lean`.  Their prime-search and tail estimates already allow arbitrary fixed `c` and survivor parameter above the stated lower bounds.  The intended adaptation therefore asks for no stronger prime-distribution estimate.

**First gate: preserve the witnesses through tail selection.**  The current final theorem exports divisor-count divisibilities, which do not imply the square-divisor divisibilities.  Its proof must retain the exact valuations, distinctness of the allocated primes, and the surviving prime cofactor.  `SquareLambertWitnessSupply` states precisely that strengthened output, including the small ordinary-divisor tail at the same offset.  Inspection of the proof suggests the data are available internally; this strengthened theorem has not been checked by Lean.  `SquareLambertWindowSupply` and `SquareLambertTransfer` separately record the subsequent coefficient and digit obligations.

That is the bounded first assignment.  If it fails, identify whether the failure is missing exported data or a genuine conflict between the valuations and tail selection before launching a larger campaign.  Numerical word searches do not test this gate.

## Relation to retired approaches

The earlier rejection of squares from the additive prime-Lambert contraction concerned divergent reciprocal prime mass and an additive coefficient interface.  This proposal uses the later multiplicative Erdos--Borwein construction and its one-coefficient word encoding.

Squares also differ from the squarefree-indexed Lambert route.  The latter has coefficients `2^omega(m)`; `Erdos257Squarefree.not_powTwoEncoding` proves that its one-coefficient encoder cannot reach every word.  The square-divisor coefficient can equal three, and the proposed prime-power writer allows every positive integer.  This addresses that specific encoding obstruction.  It does not by itself prove the carry-tail supply.

## Recommendation and confidence

Prioritize this one target, then consider `sum 1/(b^(n^r)-1)` for fixed `r>=2` if the square case succeeds.  The initial deliverable should be binary disjunctivity of the displayed constant, with all gates discharged; generality can follow.

My subjective planning estimate is about **70%** for completing that first target in a focused campaign.  This is uncalibrated and is not an estimate of novelty.  Its warrant is the explicit parameter match to a proved construction and the proved tail domination.  The remaining uncertainty is whether the strengthened witness output and all local arithmetic obligations survive a complete proof audit.  This is a materially better-grounded bet than another unsupported digit-visitation conjecture for a classical constant.
