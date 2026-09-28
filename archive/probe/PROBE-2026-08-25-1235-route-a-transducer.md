# Route A probe: the phi*x CF transducer has a compact real-place window and mixes

**Verdict: GREEN. Write the blueprint.**  Both of the attack map's crux risks for
Route A survived a direct computational test on Gauss-distributed CF input.  The
mechanism the program depends on is visibly present.

Probe: `probes/transducer_window.py` (exact `Z[phi]` arithmetic, self-testing).
Question: Vandehey 2017 Sec.7 problem 1 -- `x` CF-normal, `q, r` quadratic
irrational, `q != 0`, is `qx + r` CF-normal?  Simplest instances `x -> phi*x`
and `x -> phi*x + phi`.  Program: `papers/vandehey-2017-open-problem-attack-map.md` Sec.3.

## What Route A claims, and what was measured

Vandehey's own theorem (`q, r` rational) rides on the transducer's state set being
FINITE: entries are integers bounded by `|det| = D`.  Over `Z[phi]` that certificate
dies -- Dirichlet gives infinitely many units, and `Z[phi]` is dense in `R`.  Route A's
bet is that finiteness was only a certificate, never part of the dynamics: the
emission rule reads ONLY the real embedding, which evolves autonomously, so the
conjugate place may drift while the real place recurs to a compact window `W` of
bounded-distortion Moebius maps.  Crux risks, in the attack map's own order:
(i) uniform merging on `W`, (ii) the window lemma.

### (ii) The window lemma -- HOLDS, and the two places split exactly as predicted

Distortion is `-log10( |det| / max|entry|^2 )` at the real place, scale-invariant:
`0` = non-degenerate, large = collapsing toward singular, i.e. leaving any compact
bounded-distortion window.

| | first-half median | second-half median | worst |
|---|---|---|---|
| `x -> phi*x`, 8 runs x 600 digits | 1.038 | 0.976 | 8.79 |
| `x -> phi*x + phi`, 6 runs x 500 digits | ~1.0 | ~1.0 | 7.52 |

**No drift between halves.**  Real-place entries stay `O(1)` (`log10 max|entry|` in
`0.14 .. 0.85`) after 600 input digits, while the conjugate place reaches `10^644`.
That split IS the compact-fiber thesis, made directly visible: the state runs off to
infinity at the conjugate place and stays bounded at the real one.  The quadratic
shift `r = phi` behaves identically to `r = 0`, so nothing here is special to the
`det`-a-unit case.

### (i) Merging -- HOLDS, in its correct (Doeblin) form

Excursion tail, pooled over 2994 post-emission states:

| t | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| `P(distortion > t)` | .494 | .172 | .056 | .021 | .0087 | .0017 | 0 |
| ratio to previous | | .348 | .324 | .383 | .406 | .192 | |

A near-constant ratio is **exponential decay** (`P ~ e^{-2.3t}`), not a heavy tail.
This speaks directly to the attack map's worry that excursion events are
unbounded-rank: they are exponentially rare.

Doeblin test -- four initial states (`phi*x`, `phi*x + phi`, `phi*x + 3`, and the
genuinely different `(phi x + 1)/(x + phi)`), 200 independent input streams each,
state distribution compared pairwise by Kolmogorov-Smirnov:

| horizon | 20 steps | 60 | 240 (4 seeds) |
|---|---|---|---|
| worst pairwise KS | 0.205 | 0.105 | 0.180 / 0.090 / 0.115 / 0.110 |
| 5% critical | 0.136 | 0.136 | 0.136 |

Distinguishable at 20 steps (not yet mixed), indistinguishable from ~60 steps on.
The single 0.180 is an outlier: three further seeds at the same horizon give
0.090 / 0.115 / 0.110.  **The chain on `W` forgets its initial state.**

## Two corrections worth carrying forward

- **Fixed-precision floats silently refute this program.**  The real-place value of
  `p + q*phi` is a near-total cancellation of two huge integers -- that is exactly
  what "real place bounded, conjugate place drifting" means.  At 400 input digits the
  entries reach `10^200` while their real embedding stays `O(1)`, so 60-digit mpmath
  measured pure rounding noise: emission stalled after ~60 digits (output/input 0.18)
  and distortion appeared to diverge linearly -- a textbook "state drifts, program
  dead" false negative.  Every sign, floor and comparison in the probe is exact
  integer arithmetic in `Z[phi]`; the corrected emission rate is 0.87.
- **"Do two coupled trajectories become equal?" is the wrong merging test** and cannot
  succeed here for structural reasons.  With `M_n = L_n . M_0 . P_n` (`L_n` emitted,
  `P_n` ingested, `P_n` shared), equality forces `(L^B)^-1 L^A = M_0^B (M_0^A)^-1`:
  the two starts must differ by an element of the emission subgroup.  Integer shifts
  do -- they coincided within 1-2 steps, 8/8 runs -- and generic elements of
  `GL_2(Z[phi])` do not.  That measures the subgroup, not the dynamics.  Vandehey
  needs a Doeblin condition on the chain, which is the test reported above.

## What this does and does not license

It licenses: the mechanism Route A rests on is present in the actual dynamical
system, so the next step is the blueprint, not more simulation.  Prior on
`P(program closes it)` should go up from the attack map's ~50%.

It does not license any claim that the theorem is true.  This is numerical evidence
about `phi` on random input, at horizons of a few hundred digits.  In particular
Route A must still prove the tightness step Vandehey skipped in Lemma 3.2
(attack map Sec.6.1), and uniform merging must hold along ARBITRARY CF-normal input,
not merely almost-every input -- the probe samples the latter, and the gap between
them is precisely where the attack map put its 35% wall.
