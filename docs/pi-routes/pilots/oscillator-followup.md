# Prepared follow-up: sharp degree threshold and the fixed-degree barrier

The first pilot proves the exact quartic obstruction.  The parent has found the
matching positive endpoint control, without using computed pi digits:

`P=X^5-8X^4+4X^3+64X^2-8X-511/4`.

`P''+P=X*(X-2)^4+1/4`, positive on [0,4].
`P(0)+P(3)=-1/2` and `P(0)+P(4)=-63/2`.

`QuinticEndpointControl` and the polynomial itself are in
`RoundTwoPilotTargets.lean`; the independent exact check is in
`scripts/pi_pilot_preflight.py`.  They are not yet Lean theorems.

## Next bounded proof task

1. Prove the quintic control.
2. Classify [1]-avoiding x in [3,4] as precisely {3,4}, with the canonical binary
   expansion convention.  Use the existing digit reconstruction lemmas.
3. Prove a word-[1] oscillator certificate exists in degree 5 and none exists in
   degree <=4.  State the actual certificate and its minimum degree, not just
   endpoint inequalities.  This is a sharp calibration result, not a new fact
   about pi's digits.

The subsequent structural question is `FixedDegreeBlindInterval`: for each fixed
degree there is an open neighborhood of pi on which EVERY positive-oscillator
polynomial of that degree has positive endpoint functional.  A possible proof
normalizes Q=P''+P, uses compactness of its nonnegative fixed-degree cone and
positivity of the sine integral, then bounds the inverse operator and P'.
This is only a proposed proof, not a settled conclusion.  If established, combining
it with nondisjunctive rationals in every interval would rule out any one fixed
degree for all words.  It would not rule out a degree growing with the word.

Do not quietly expand the first pilot to this task.  A fresh short lap can handle
the sharp degree-5 calibration after the first pilot is reviewed.
