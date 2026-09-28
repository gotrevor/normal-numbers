# Feedback adversary: A3 holds; and the rational case is the control this program needed

Two results, one of which is a correction to a claim I nearly put in the blueprint.

## 1. A3 (merging) survives a maximally informed adversary

The schedule adversary injected huge partial quotients at `n = 2^k`, blind to the
transducer.  This one WATCHES.  Legality is unchanged -- the stream must stay
CF-normal, so injections occupy a density-zero position set -- but the budget is
now `ceil(sqrt(n))` (more generous than `2^k`) and the adversary chooses WHERE and
WHICH, which is the whole point.

For A3 it sees **all four initial states** evolving on its own stream and each step
keeps the candidate digit maximising the spread of their state coordinates: it is
actively fighting the merging it is trying to prevent, with more information than
the theorem ever has to survive.

Worst pairwise KS, 4 starts x 90 streams x 110 steps:

| seed | passive | greedy adversary |
|---|---|---|
| 11 | 0.1778 | 0.1222 |
| 22 | 0.1000 | 0.1444 |
| 33 | 0.1778 | 0.1667 |
| **mean** | **0.1519** | **0.1444** |

The adversary lands **below** the passive null.  It spends all 11 injections every
run and buys nothing.  A3 is robust to the strongest attack available in this class.

## 2. The A2 reading I nearly shipped, and the control that killed it

Under the greedy adversary the worst real-place distortion jumped from 7.97 to
36.81, and a scaling sweep looked decisive:

| adversary's digit | 10^3 | 10^6 | 10^12 | 10^18 | 10^30 | 10^48 |
|---|---|---|---|---|---|---|
| worst distortion | 7.64 | 12.21 | 24.21 | 36.81 | 61.41 | 96.21 |
| `2*log10(digit)` | 6 | 12 | 24 | 36 | 60 | 96 |
| median / p99 / recovery | flat | flat | flat | flat | flat | flat |

Perfect linear tracking, with median, p99 and return time all unmoved.  The reading
writes itself: no fixed compact `W` contains every post-emission state over
admissible input, so **A2 as stated is false and must be restated as recurrence**.

That reading is wrong.  Running the identical adversary against **rational `q`**,
where Vandehey's theorem is PROVED and his states satisfy `|entry| <= D`:

| case | 10^6 | 10^18 | 10^36 |
|---|---|---|---|
| `q = phi` (the open case) | 12.81 | 36.81 | 72.21 |
| `q = 2` | 12.90 | 36.90 | 72.90 |
| `q = 3` | 13.43 | 37.43 | 73.43 |
| `q = 5/2` | 15.00 | 39.00 | 75.00 |

**The proved case does exactly the same thing.**  So this distortion functional is
not measuring the quantity Vandehey bounds -- his state is evidently a reduced or
canonical representative in a sense mine is not -- and a phenomenon that occurs in
the rational case cannot be an obstruction to the quadratic one, because there the
theorem is true.  Claim retracted before it reached the blueprint.

What survives from Sec.2 is narrower and still useful: median, p99 and recovery
time are flat under every adversary tried, at both `q = phi` and rational `q`.

## 3. The reusable instrument: rational `q` is a positive control

This is the part worth carrying into the whole program.  **Route A's rational case
is a known-answer control, and every measurement should be run against it.**

- A proposed obstruction that also appears at `q = 2` is not an obstruction.  The
  theorem is true there, so whatever the measurement shows is compatible with the
  conclusion, and the finding is about the instrument.
- A measurement that separates `q = phi` from `q = 2` is the only kind that can
  bear on the open problem at all.
- Nothing in the green probe or the schedule-adversary probe was run this way.
  Their positive results are unaffected -- a mechanism being PRESENT at `q = phi`
  is not weakened by also being present at `q = 2` -- but any future NEGATIVE
  result needs the control before it is believed.

Recording the near-miss honestly: the scaling sweep produced a clean, quantitative,
mechanistically plausible result that confirmed the exact hypothesis the probe was
built to test, and it was an artifact.  The tell was available in advance -- the
functional was never validated against a case with a known answer.

## Where the code lives

Scratchpad, because a treadmill owns this repo: `feedback_adv.py` (the greedy
window and merging adversaries), `scaling.py` (the digit-size sweep), `control.py`
(the rational-`q` control).  To be moved into `probes/` with `adversarial.py` and
`adv_null.py` when the campaign is between laps.
