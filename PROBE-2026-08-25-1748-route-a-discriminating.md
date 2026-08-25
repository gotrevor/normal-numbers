# Discriminating test: `q = phi` is indistinguishable from rational `q`

Route A rests on one sentence: **the conjugate place never feeds back**, so
Vandehey's finiteness was a certificate rather than part of the dynamics.  If that
is right, the real-place dynamics at `q = phi` should look like the real-place
dynamics at a rational `q`, where the theorem is proved.  This is that test, built
on the positive control from `PROBE-2026-08-25-*-feedback-adversary.md`.

The null is not "zero difference" -- different `q` differ for trivial reasons
(determinant, denominator).  So the null is built from **rational-vs-rational**
pairs, and the question is where phi-vs-rational falls inside it.

Observables: pooled real-place distortion distribution, emission rate, excursion
tail.  7 runs x 350 digits per case.

| pair | KS |
|---|---|
| rational null, `2` vs `3` | 0.1930 |
| rational null, `2` vs `5/2` | 0.2183 |
| rational null, `2` vs `7/3` | 0.2088 |
| rational null, `3` vs `5/2` | 0.1206 |
| rational null, `3` vs `7/3` | 0.0997 |
| rational null, `5/2` vs `7/3` | 0.0845 |
| **TEST** `phi` vs `2` | 0.2467 |
| **TEST** `phi` vs `3` | 0.1610 |
| **TEST** `phi` vs `5/2` | 0.0830 |
| **TEST** `phi` vs `7/3` | 0.0818 |

Null range `[0.0845, 0.2183]`, mean **0.1541**.  Phi range `[0.0818, 0.2467]`,
mean **0.1431**.  Emission rate: phi `1.040`, rationals `[1.014, 1.046]`.

**`phi` is on average CLOSER to the rationals than the rationals are to each
other.**  The single exceedance is `phi vs 2` (0.2467 against a null max of
0.2183), and `q = 2` is the null's own outlier -- it is the most distant member in
three of its own six null pairs.  Nothing here separates the quadratic case from
the proved case.

## What this supports, and what it does not

Supports: Route A's load-bearing claim.  The arithmetic that makes the quadratic
case hard -- infinite unit group, states dense in `R`, entries drifting at the
conjugate place to `10^644` over 600 digits -- leaves **no detectable signature in
the real-place dynamics** across distortion, emission rate and excursion tail.
That is exactly the "the conjugate place was a certificate, not a variable the
transducer consults" thesis, tested rather than asserted.

Does not: indistinguishability under these observables is not absence of feedback.
These are coarse one-dimensional summaries, and a feedback mechanism that lives in,
say, the joint law of (state, next output digit) would pass all of them.  It also
remains numerics at horizons of a few hundred digits.

Method caveat, stated because the numbers invite the wrong test: KS on samples
pooled across a run is not an independent-sample KS -- within-run autocorrelation
makes the tabulated critical values inapplicable.  The comparison is valid only
because the null is constructed the same way from the same pipeline; read the table
as phi-inside-null, never as a p-value.

## Where the code lives

Scratchpad (a treadmill owns the repo): `discriminate.py`, alongside
`feedback_adv.py`, `scaling.py`, `control.py`, `adversarial.py`, `adv_null.py`.
Move all six into `probes/` when the campaign is between laps.
