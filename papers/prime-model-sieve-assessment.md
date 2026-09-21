# Sieve bottleneck assessment

Ren / Codex, 2026-09-20.  Paper-level assessment, not a Lean theorem.

## Verdict

The radical shortcut removes real work from the KMT route, but it does not
remove its fundamental-sieve input.  Prior successful laps established useful
probability and arithmetic components, not that input.  The installed
`Mathlib/NumberTheory/SelbergSieve.lean` proves upper-sieve machinery and a
quadratic-form identity; it does not provide the required lower asymptotic.
Targeted external searches found no ready-to-import proof of that lower result;
this is not a claim that none exists anywhere.

There is, however, a smaller sufficient target: **a specialized lower Brun
sieve**.  The two-sided requirement in earlier notes was stronger than needed.
Below is an explicit finite-set construction and coarse quantitative estimate.
Recommendation: prove this core next; do not launch more peripheral assembly
laps first.  Confidence in the paper route: 85%; formal effort remains uncertain.

## Lower probabilities suffice

For finite normalized nonnegative laws mu,nu and retained set B, let
`dB=sum_{i in B} max(mu(i)-nu(i),0)` and `tau=mu(B complement)`.
Normalization gives equal positive and negative discrepancy masses, hence

    sum_i |nu(i)-mu(i)| = 2 sum_i max(mu(i)-nu(i),0) <= 2(dB+tau).

Thus lower atom estimates `nu(i)>=(1-eta)*mu(i)-e(i)`, eta,e>=0, give
`L1 <= 2tau+2eta+2sum_B e(i)`.  The bounded-phase difference obeys the same
bound.  No upper estimate on nu inside B is necessary.  Upper estimates alone
would not suffice: nu could put all its mass outside B.

This is a deduction for our normalized joint residue/radical law, not an
assertion that Mathlib's upper sieve becomes a lower sieve for free.

## Concrete lower-weight construction

Let U be a finite set of primes <=y, y>=exp(2), k>=1, and 0<=g(p)<1.
Write V=product_U(1-g(p)).  Assume the following explicit tail-product bound
for 1<=t<=y, with K>=1:

    product_{p in U,p>t} (1-g(p))^(-1)
      <= K * (log y / log(max(2,t)))^k.

The earlier standard interval-dimension condition implies this after replacing
its K0 by `(3/2)^k*K0`: use upper endpoint 2y and log y>=2.  Consequently
log K=O(k) in the intended application.  This dimension estimate still needs
formalization; no new prime-distribution conjecture is assumed.

Put a=log K, alpha=1-1/(20k), J=floor(s/4), and assume
`s>=max(80k,40a+4)`.  For each j>=1 set
`Y_j=y` if j<=J, otherwise `Y_j=y^(alpha^(j-J))`.
For E subset U, list its primes in decreasing order p1>...>pr.  Define

    lambda(E)=(-1)^r if p_(2j)<=Y_j for every 2j<=r; otherwise 0.

These are finite, explicit coefficients in {-1,0,1}.

**Pointwise minorant.**  Group omitted subsets by their first failed even
prefix F.  Its length is even.  Summing signs over all smaller remaining
elements of a fixed bad-prime set gives either 0 or 1.  The omitted total is
therefore nonnegative, proving
`sum_{E subset bad} lambda(E) <= indicator(bad empty)`.
This finite cancellation identity is the first formal target.

**Support.**  The first 2J+1 factors cost at most that many log y units.
Each subsequent pair costs at most 2alpha^ell.  Hence

    log(product E)/log y <= 2J+1+2alpha/(1-alpha)
      = 2J+40k-1 <= s.

So every supported divisor is <=y^s, with coefficient absolute value <=1.

## Relative-error calculation

Grouping omitted model terms by the same first failed even prefix gives an
exact nonnegative defect `V-sum_E lambda(E)*product_E g(p)`.
For a failed prefix of length 2(J+ell), all its primes exceed Y_(J+ell).
The remaining smaller-prime factors give a product at most V(Y_(J+ell)),
where V(t)=product_{p<=t}(1-g(p)).  Put b=-k log alpha<=1/10.
The dimension condition bounds that product ratio by exp(a+b ell), and the
sum of local densities above the cutoff by a+b ell.  These remain valid when
the cutoff falls below 2, using max(2,t).  Elementary symmetric sums are at
most the corresponding power sum divided by the factorial.  Therefore

    relative defect <= sum_{ell>=1}
      exp(a+b ell)*(a+b ell)^(2(J+ell))/(2(J+ell))!.

Our threshold ensures J>=10a.  With n=2(J+ell) and
c=(a+b ell)/n, we have 0<=c<=1/20.  Using n!>=(n/e)^n, each summand is
at most `(c*exp(1+c))^n <= (1/4)^n`.  Thus

    relative defect <= 16^(-J)/15 <= 2 exp(-s/2).

This is the analytic acceptance condition, not merely existence of a pointwise
minorant.  Degenerate lower weights can be valid and yet have negative model
main term; the regression suite includes that failure case.

## Match to the frozen target

Use the inclusive cutoff y=x^epsilon and level R=x^(1/4), so
s=log R/log y=1/(4epsilon).  The lower relative error is then at most
`2 exp(-1/(8epsilon))`, which is no larger than
`2 exp(-1/(8k^2 epsilon))` for k>=1.  The small-s regime is absorbed by the
trivial phase bound with an explicit constant, since the threshold is O(k)
when log K=O(k).  Unlike a black-box O_k statement, these estimates expose
the k-dependence required by the frozen selected-prime theorem.

The already-proved CRT count supplies each remainder.  Further assembly still
needs the radical-state predicate equivalence, retained-state cardinality,
the sum of sieve remainders, interval dimension estimate, phase decay and
constant bookkeeping.  The **weight construction plus its relative-error
bound** is the next decisive milestone; none of those other components should
be substituted for it in a success report.

## Evidence and sources

The incumbent `prime_model_certificate.py test` now has 43 passing CLI tests.
New `brun-lower` controls exhaust every bad subset for a small explicit prime
set.  For primes2,3,5,7 and even cutoffs3,2, the largest supported divisor is42,
V=8/35, and the lower model sum is23/105: relative deficit1/24.  These exact
finite controls do not prove the general construction or the uniform estimates.

[Koukoulopoulos, Chapter19](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)
provides the classical ordered-prime cutoff approach and its lower-sieve
interpretation.  The deliberately coarse parameters and error-budget comparison
above were worked out for this application; no historical novelty is claimed.
[Matomaki-Teravainen, Lemma9.1](https://arxiv.org/html/2301.07679#S9)
remains the stronger paper-level black-box alternative already audited.

An ordinary single Bonferroni truncation is not a substitute: a fixed degree
limits support, but total local density can grow with log log y, so its relative
error is not uniformly small.  The shrinking ordered-prime cutoffs are essential
to the proposed proof, and should be the focus of the next review/formalization.
