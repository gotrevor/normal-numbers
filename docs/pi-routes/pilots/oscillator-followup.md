# Prepared follow-up: sharp degree threshold and the fixed-degree barrier

Completed: `minimumDegreeWordOne` in the `RoundTwoOscillatorSharp.lean` module
proves the sharp threshold.  See `oscillator-sharp-result.md`.
This brief is historical; the broader route is retired under `Pi route 5` in the
Maze.  Do not relaunch this calibration or the structural question below as a new
pi-disjunctivity route without meeting that row's reopening requirement.

The first pilot proves the exact quartic obstruction.  The parent has found the
matching positive endpoint control, without using computed pi digits:

`P=X^5-8X^4+4X^3+64X^2-8X-511/4`.

`P''+P=X*(X-2)^4+1/4`, positive on [0,4].
`P(0)+P(3)=-1/2` and `P(0)+P(4)=-63/2`.

`QuinticEndpointControl` and the polynomial itself are in
`RoundTwoPilotTargets.lean`; the independent exact check is in
`scripts/pi_pilot_preflight.py`.  They are not yet Lean theorems.

## Next bounded proof task

This follow-up overrides the first-pilot operational settings: one Opus/low lap,
80,000 legacy context tokens (including inherited context), a 35-minute supervisor
setting, and a compiling checkpoint after about 25 minutes.  The parent owns the
final host build and normal commit hooks.  Do not start a worker commit or wait on
a full-repository build; leave the two deliverable files for parent review.
Write only `src/NormalNumbers/PiDisjunctiveRoutes/RoundTwoOscillatorSharp.lean`
and `docs/pi-routes/pilots/oscillator-sharp-result.md`.  Import the existing
`RoundTwoOscillator` module.  No changes to frozen targets, shared Maze files,
dependencies, or other workers' files; no further agents or treadmills.

1. Prove the quintic control.
2. Classify [1]-avoiding x in [3,4] as precisely {3,4}, with the canonical binary
   expansion convention.  Use the existing digit reconstruction lemmas.
3. Prove a word-[1] oscillator certificate exists in degree 5 and none exists in
   degree <=4.  State the actual certificate and its minimum degree, not just
   endpoint inequalities.  This is a sharp calibration result, not a new fact
   about pi's digits.  The frozen targets are `QuinticEndpointControl`,
   `WordOneAvoidanceClassification`, `QuinticWordOneCertificate`, and
   `MinimumDegreeWordOne`.  Inspect types and `#print axioms` of delivered proofs.

Do not spend this lap on the structural question below.  If the classification
stalls, deliver the quintic algebra and a precise missing lemma.

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
