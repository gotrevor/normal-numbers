# ln(2): three mechanism checks

The goal remains disjunctivity in any integer base.  This pass invents and tests
mechanisms, then records both mathematics and difficulty in Lean.  It does not
admit three proof campaigns merely to fill three slots.  No literature search
or novelty claim is involved.

The repo already proves the base-two Mercator identity (`hasSum_lnTwoSeries`)
and the base-nine identity (`MasterConjectures.hasSum_lnTwoNine`).  Consequently
the untwisted two-base description is available without a new series proof.
It does not supply a word-dependent estimate overcoming the norm/denominator
obstacle from the pi dual-radix screen, so it is not counted as a new route.
Fermat-quotient checksums, generic kick floors, Stoneham summands, and the old
dyadic-separation reformulations were also excluded by the Maze.

All new statements are in `src/NormalNumbers/LnTwoRoutes/Screen.lean`.
The reproducible exact-arithmetic probe is `scripts/ln_two_route_screen.py`;
its output is `probe.json`.  A defined proposition is an explicit unproved
statement, even when its mathematical justification is elementary.

## 1. Euler acceleration: exploit arbitrarily fast polynomial kick decay

Put

\[
B_m(n)=\frac{m!}{n(n+1)\cdots(n+m)},\qquad
H_m^- =\sum_{j=1}^m\frac{(-1)^{j-1}}j.
\]

`AcceleratedLogIdentity` states

\[
\log 2=H_m^-+(-1)^m\sum_{n\ge1}\frac{B_m(n)}{2^n}.
\]

The justification is the beta integral followed by polynomial division of
u^m/(1+u).  It is recorded as an unproved analytic input, with 99% confidence.
The attraction is real: the kick can decay as n^(-m-1), at any fixed order m.
The rational shift H_m^- must stay in the analysis.  Increasing m also changes
its denominator and the carry phases; rapid decay alone does not supply visits.

**Discriminating control.**  Define

\[
F_m(n)=\sum_{j=0}^{m-1}(-1)^jB_j(n),\qquad
r_m(n)=2F_m(n)-F_m(n+1).
\]

Then r_m(n)=1/n-(-1)^m B_m(n).  For every positive m it is positive, agrees
with 1/n through an arbitrarily chosen finite asymptotic order, and its weighted
sum is the rational H_m^-.  These all-order analytic claims are explicitly
stated in `FiniteJetRationalControls`, not asserted to have kernel proofs.
`binary_coboundary_sum` and `clone_partial_sum` prove the exact finite telescoping
identity.  `rational_clone_not_disjunctive` proves that each proposed rational
limit is nondisjunctive.  The exact probe checks 240 finite identities and bounds
at m=1,...,10 and n=1,...,24; the wrong coboundary coefficient breaks the control.

**Scope.**  Rational controls do not refute an irrational-or-disjunctive
dichotomy, nor a theorem using the exact reciprocal kick together with ln(2)'s
irrationality.  They explain why matching a finite asymptotic expansion does not
itself distinguish the desired orbit from a rational one.

**Disposition: parked.**  `AcceleratedWindowSupply` is the remaining visit
condition, not evidence that it is easier.  Reopen with a bound using the exact
forcing and rational shift, including its denominator cost.  Another order of
acceleration or a proof of the classical identity alone does not qualify.

## 2. Padé synthesis: make the logarithm coefficient exactly dyadic

**Bounded follow-up completed:** [cost-test.md](cost-test.md) records an exact
optimized witness with budget below 1/8 and finite dual exclusions.  The large
Bezout witnesses described below are the initial screen, not the final cost result.

Let A_n,B_n be the rational recurrence `padePair`, initialized by (1,0),(3,2):

\[
(n+1)V_{n+1}=3(2n+1)V_n-nV_{n-1}.
\]

The positive small forms E_n=A_n log 2-B_n are the classical logarithmic Padé
forms.  `PadeErrorEnvelope` states the integral representation's consequence
0<E_n≤5^(-n), as an unproved classical input.  `PadeWronskian` records
A_n B_(n+1)-A_(n+1)B_n=2/(n+1), likewise unproved here; the exact recurrence
probe checks 165 instances.

The proposed mechanism is to choose integer coefficients u_j satisfying

\[
\sum_j u_jA_{n+j}=2^s,\qquad \sum_j u_jB_{n+j}\in\mathbb Z.
\]

Then the corresponding sum of errors locates 2^s log 2 modulo one.  This is
`DyadicSynthesis`.  A successful construction would also control the size and
sign of the error to select a requested word.  `PadeWindowSupply` records that
unproved requirement.  Its appearance in Lean is not a proof strategy by itself.

**A concrete obstruction, proved.**  The pair at n=5,6 is

\[
(A_5,B_5)=(1683,34997/30),\quad
(A_6,B_6)=(8989,62307/10).
\]

If uB_5+vB_6 is integral, reduction modulo five forces
5 | (1683u+8989v).  Thus that coefficient can never be a power of two,
although gcd(1683,8989)=1.  This is `pade_five_six_no_dyadic`, with
`pade_five_six_data` checking its connection to the recurrence.  The small pair
n=1,2 is a positive control: -4(A_1,B_1)+(A_2,B_2)=(1,1).

**Finite screen.**  For starting indices 1≤n≤79:

| Number of consecutive forms | Starts permitting a dyadic coefficient and integral constant |
|---|---|
| 2 | 1, 2 |
| 3 | 1, 2, 4 |
| 5 | 1, 2, 3, 4, 6 |
| 10 | 1 through 10 |

Every rejection has an exact odd-prime certificate, not a bounded unsuccessful
search.  Writing D for the common denominator and C_j=D B_(n+j), the certificate
checks p|D and A_(n+j)≡c C_j (mod p) for an odd prime p.  An integral constant
then forces the logarithm coefficient to be divisible by p.  Every accepted
case has an actual integer witness, constructed using Bezout identities.
`no_dyadic_of_prime_certificate` proves the general certificate implication.
`PadeGridProbe` freezes the complete table, and `PadeShortWindowProbe` records
three rejection ranges in Lean; these are
finite Python evidence, not a general theorem about all starting indices.

**The wider-block control matters.**  The windows n,...,2n-1 are feasible at
n=4,8,16,32 (`PadeWideWindowProbe`).  Thus short-block failure does not eliminate
the synthesis idea.  However the returned Bezout witnesses all fail the crude
error-budget gate: sum |u_j|5^(-n-j)>1 (`PadeWideBudgetProbe`).  These witnesses were not optimized;
their failure says nothing about the minimum possible cost.

**Disposition: the bounded cost gate passed; the uniform question remains open.**
The follow-up proves one cheap coefficient witness.  `PadeCheapDyadic` asks for
arbitrarily small such budgets.  With the error envelope it would give close
integer returns, a weaker target than all words.  A discriminating follow-up
did find substantially cheaper witnesses and finite lower bounds.
More first occurrences of digit words, or additional wide-block feasibility
alone, would not advance this crux.  No long proof campaign was launched.

## 3. Localized logarithms: transfer words before the approximation expires

`localizedLog P` retains the terms 1/(n 2^n) whose prime factors are at most P.
The repo already has normality machinery for such constants, conditional on
its stated Vandehey input.  Since every index through P is retained,
`LocalizedShadow` states the elementary bound

\[
0\le\log2-\operatorname{localizedLog}(P)
\le\frac{2^{-P}}{P+1}.
\]

It remains an unproved input in this module.  After n binary shifts its error
budget is 2^(n-P)/(P+1).  The new question would be a word visit with enough
interior margin before that budget becomes large.  `LocalizedWindowSupply`
records the quantifiers, including the necessary coupling between P and n.

**Control.**  `normal_tail_hidden` proves that y/2^K is normal whenever y is
normal.  `normal_tail_bound` bounds it by 2^(-K) for 0≤y≤1, while
`zero_not_disjunctive` excludes the limiting number zero.  K can be any chosen
schedule, so fast convergence of normal approximants alone cannot supply the
missing timing bound.  This does not refute a bound specific to localized logs.

**Disposition: parked.**  Reopen with an actual uniform word-visit estimate
that fits the shadow budget.  Normality for each fixed prime cutoff, an
arbitrarily large shared prefix, or soft diagonalization is insufficient.

## What this pass earns

There is no proof of ln(2) disjunctivity, and none of the missing visit estimates
has been proved.  The Padé coefficient-cost problem now has a finite passing
witness and finite exclusion certificates in [cost-test.md](cost-test.md).
No parameter-uniform construction has been found.
The other two avenues are parked with explicit controls and reopening conditions.
