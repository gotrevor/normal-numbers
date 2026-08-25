# Adversarial probe: sparse enormous partial quotients do NOT break Route A

**Verdict: A3 survives the natural adversary.**  The gap the green probe left open
was that it sampled Gauss-typical (almost-every) input, while Route A needs merging
along ARBITRARY CF-normal input.  This probe attacks exactly that gap and fails to
break anything.

Probe: `adversarial.py` + `adv_null.py` (see "Where the code lives" below), built on
`probes/transducer_window.py`.

## The adversary, and why it is the right one

CF-normality pins the limiting frequency of every FIXED finite word.  It therefore
says nothing whatsoever about digits occurring with density zero.  So a CF-normal
`x` may carry a sparse sequence of enormous partial quotients, and those are
precisely the "unbounded-rank excursion events" the attack map named as the reason
uniform merging might fail (its 35% wall).  Density-zero injection leaves every
fixed word's limiting frequency untouched, so the perturbed stream is still
CF-normal: a legal input that a.e.-sampling structurally cannot produce.

Three schedules, all density zero, injected into a Gauss-typical stream:

| schedule | positions | injected digit |
|---|---|---|
| `squares` | `n = k^2` | `10^6` |
| `powers`  | `n = 2^k` | `10^6 .. 10^18` |
| `brutal`  | `n = 2^k` | `10^(3k)`, super-exponential |

## (W) The window is untouched

6 runs x 400 digits.  Distortion is `-log10(|det| / max|entry|^2)` at the real place.

| schedule | median | 1st half | 2nd half | worst | steps to recover below 2 |
|---|---|---|---|---|---|
| none | 0.940 | 0.995 | 0.892 | 6.69 | 1.0 |
| squares | 1.023 | 1.061 | 0.973 | 7.23 | 1.0 |
| powers | 0.960 | 0.940 | 1.005 | 7.86 | 2.0 |
| brutal | 1.011 | 1.007 | 1.039 | 9.35 | 2.2 |

A `10^(3k)` partial quotient buys the adversary about 2.7 extra units of worst-case
distortion and **1.2 extra steps of recovery**.  The median does not move and there
is no drift between halves.  The renormalisation absorbs the excursion essentially
immediately -- which is the window lemma (A2) doing exactly the job Route A assigns
it, under the worst input the adversary is allowed to construct.

## (M) Merging is untouched -- and the naive yardstick is wrong

First pass, single seed, looked like a hit: `powers` 0.1600 and `brutal` 0.1733
against a tabulated 5% two-sample critical value of 0.1570.  That reading is wrong,
for a reason worth keeping: the statistic is the **max over 6 pairwise comparisons**,
so the per-pair critical value is not its null distribution.  The right instrument is
an empirical null built from the UNPERTURBED schedule across seeds.

Worst pairwise KS, 4 starts x 120 streams x 130 steps, five seeds each:

| schedule | seed 101 | 202 | 303 | 404 | 505 | mean | max |
|---|---|---|---|---|---|---|---|
| none | .1500 | .1083 | .0917 | .2000 | .1583 | **.1417** | .2000 |
| squares | .1250 | .1167 | .1917 | .1667 | .1500 | .1500 | .1917 |
| powers | .1000 | .1500 | .1083 | .1417 | .2000 | .1400 | .2000 |
| brutal | .1083 | .1083 | .1500 | .1917 | .1417 | .1400 | .1917 |

The unperturbed null reaches 0.2000 on its own.  Injected means are
`+0.008 / -0.002 / -0.002` against a null mean of 0.1417; seeds exceeding the
null max: `0/5`, `1/5`, `0/5`.  **No elevation at all.**  The single-seed
"DISTINGUISHABLE" verdicts were noise, and the null's own spread is what a
0.16-0.17 reading looks like when nothing is happening.

## What this moves

- The attack map's 35% wall was specifically about excursion events being
  unbounded-rank while CF-normality only controls fixed-rank cylinder frequencies.
  The natural construction exploiting that gap does not dent either A2 or A3.
  That is direct evidence against the stated failure mode, so the wall estimate
  should come down.
- It does **not** show A3 holds for arbitrary CF-normal input.  This is one family of
  adversaries -- sparse, huge, uncorrelated with the state.  A cleverer adversary
  would correlate the injection with the transducer's current position in `W`
  (feedback rather than a fixed schedule), which is the next thing to try and is
  still cheap.  And it remains numerics: A2 and A3 are unproved.

## Method notes worth carrying

- **A max over `k` comparisons needs an empirical null, not the per-comparison
  critical value.**  Both false positives here came from that substitution, and both
  looked like exactly the result the adversary was built to find.
- Recovery time, not worst-case magnitude, is the informative statistic for a window
  lemma.  A big excursion that resolves in 2 steps is the renormalisation working;
  a small one that persists would be the real danger sign.

## Where the code lives

The probe scripts were written outside the repo (scratchpad) because a treadmill was
running here and `git add -A` from a box lap would have swept them mid-write.  They
should be moved to `probes/` and committed when the campaign is between laps:
`adversarial.py` (injection schedules, window + Doeblin under injection) and
`adv_null.py` (the empirical-null replication).
