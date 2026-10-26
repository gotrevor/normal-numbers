# Backward BBP cancellation: a specific arithmetic feature, with no digit bridge yet

The task was to attack the whole exact BBP recurrence under a missing-word assumption.  The finding in this pass is an identity suggested by running its rational forcing backward.  It has a paper derivation and exact finite evidence.  The infinite identity is **not yet proved in Lean**, and no implication for disjunctivity has been established.

All declarations below are in `src/NormalNumbers/PiDisjunctiveRoutes/BBPBackward.lean`, namespace `NormalNumbers.PiDisjunctiveRoutes.BBPBackward`.

## The identity

Extend the BBP rational kick to negative integers:

\[
B(x)=\frac4{8x+1}-\frac2{8x+4}-\frac1{8x+5}-\frac1{8x+6}.
\]

`kick_cast` connects this definition to the existing real `bbpKick`.  The usual real series is \(\sum_{n\ge0}16^{-n}B(n)=\pi\).  The proposed backward identity is

\[
\boxed{\sum_{k\ge1}16^kB(-k)=0\quad\text{in }\mathbb Q_2.}
\]

This is `backward_hasSum_zero`, frozen with one explicit `sorry` and confidence 99% in its paper argument.  It is not a statement that the real backward sum converges.  Powers of 16 grow in the real metric and shrink in the 2-adic metric.

The proved `kick_factored` identity is

\[
B(x)=\frac{120x^2+151x+47}{(8x+1)(2x+1)(8x+5)(4x+3)}.
\]

At integer arguments all four displayed denominator factors are odd.  Thus the backward summands become small 2-adically.  Their sum being exactly zero is the extra cancellation.

## Paper derivation of zero

Use the power series at zero of

\[
G'(u)=\frac{16u+16u^2+32u^3-64u^6}{1-16u^8}
     =\frac{8u}{1-2u+2u^2}+\frac{8u}{1-2u^2}.
\]

The cleared polynomial identity is proved as `generating_identity`.  Integrate termwise with constant term zero, and group the terms by blocks of eight.  At \(u=1\), block \(k\) is exactly \(16^kB(-k)\).

In \(\mathbb Q_2(i)\), put \(P(u)=1-2u+2u^2=(1-(1+i)u)(1-(1-i)u)\).  A primitive with zero constant term is

\[
2\log P(u)-2\log(1-2u^2)
 +2i\bigl[\log(1-(1+i)u)-\log(1-(1-i)u)\bigr].
\]

These logarithmic series converge at \(u=1\): \(|1+i|_2=|1-i|_2=2^{-1/2}<1\), and the other nonconstant arguments also have norm below one.  Their values there are logarithms of \(1,-1,-i,i\), respectively.  Each vanishes because its argument is a root of unity.  This gives zero.

The missing formal proof is the convergent logarithm/power-series argument in the ramified extension.  No theorem downstream uses the frozen identity as if it were proved.

## Exact evidence and controls

Run `scripts/pi_bbp_backward_probe.py`.  Its checked-in output is `docs/pi-routes/bbp-backward-probe.json`.  All arithmetic uses exact rational fractions.

For \(S_N=\sum_{k=1}^N16^kB(-k)\), every cutoff \(1\le N\le256\) satisfies the stronger pattern

\[
v_2(S_N)=4N+4+v_2(N).
\]

This is recorded separately as the **open** proposition `BackwardValuation`; the logarithm argument above only establishes the proposed infinite sum identity, not this exact valuation formula.  At \(N=256\), the observed valuation is 1036.

Changing the first numerator coefficient from 4 to 5 gives valuation exactly 4 at every tested cutoff.  The first three genuine partial sums and the first altered term are also independently verified in Lean by `backward_first`, `backward_second`, `backward_third`, and `changed_coefficient_first`.

A known-answer telescoping control uses

\[
C(n)=F(n)-F(n+1)/16.
\]

The **proved** identities `backward_coboundary` and `forward_coboundary` give

\[
\sum_{k=1}^N16^kC(-k)=16^NF(-N)-F(0),\qquad
\sum_{n=0}^{N-1}16^{-n}C(n)=F(0)-16^{-N}F(N).
\]

For \(F\equiv1\), the forward real limit is 1 and the backward 2-adic limit is −1.  The probe checks the exact finite identity \(16^N-1\) before investigating BBP.  Thus backward zero is not automatic for a rational telescoping forcing.

## What this changes, and the next decision

This supplies a specific arithmetic feature of the exact BBP formula, absent from the changed-coefficient control.  It does not supply the requested contradiction from a missing word.  In particular, 2-adic cancellation is not an estimate for the real fractional part of the head \(H_n=16^n\piPartial(n)\).

The next research test is whether the backward identity imposes an additional quantitative restriction on **the genuine head inside a real missing-word set**, retaining the exact forcing.  A useful lemma must connect these two conditions; merely proving the 2-adic identity or the valuation conjecture would not do that.  No such lemma is supplied here.  Do not launch a long formalization of 2-adic logarithms on the assumption that it advances disjunctivity.

No internet or novelty search was performed.  This is a finding in this investigation, not a claim of priority.
