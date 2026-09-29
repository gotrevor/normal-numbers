# Probe, lap 91: the stall clock, the width walk, and the queue

**Date** 2026-09-29 · exact arithmetic, no floating-point in any decision · script kept at
`scratch/` shape below (reproducible from this file alone).

## What was simulated

Exactly the repo's transducer (`VandeheyS7Run`): state `s : MapState`, one input digit per step,
`t = s ∘ readMap a`, emit the unique digit `b` with `t((0,1)) ⊆ I_b` when one exists (the
`emitStep` witness `u = [[t.c − b·t.a, t.d − b·t.b], [t.a, t.b]]`), else stall.

* **Arithmetic.** State entries in `ℤ[φ]` as integer pairs `u + vφ`; every comparison is the exact
  sign of `A + B√5` (`A = 2u+v`, `B = v`: equal signs decide it, opposite signs decide by
  `A² − 5B²`).  The emission digit is found by exact binary search for `⌊d/n⌋`.  No decision in the
  run depends on a floating-point value.
* **Input.** Digits drawn i.i.d. from the Gauss digit law (`a = ⌊1/u⌋`, `u = 2^t − 1`,
  `t` uniform) — a generic CF-normal-style input.  The run's state depends only on the digits.
* **Maps.** `Φ : z ↦ z/φ` (i.e. multiplication by `φ⁻¹`, entries `(1,0,0,φ)`), `Φ : z ↦ (z+1)/3`
  (rational: Vandehey Thm 1.1's regime), `Φ : z ↦ φz/(z+φ)`.

## Faithfulness check (the reason to believe the rest)

For `z ↦ z/φ` with 400 input digits the emitted word was compared, digit for digit, with the true
continued fraction of `x/φ` computed independently at 2000 decimal digits:

```
input digits : [2, 141, 1, 4, 3, 6, 2, 8, 11, 2, 2, 7, 2, 3, 1, 15, 1, 3, 2, 9, ...]
emitted      : [3, 4, 24, 1, 1, 8, 6, 1, 19, 59, 1, 2, 1, 4, 17, 1, 2, 1, 4, 2, ...]
true CF(x/φ) : [3, 4, 24, 1, 1, 8, 6, 1, 19, 59, 1, 2, 1, 4, 17, 1, 2, 1, 4, 2, ...]
```

agreement on all 120 digits checked; 398 emissions from 400 reads.  **The simulated transducer is
the real one, and its output is the image's continued fraction.**

## Finding 1 — the clock deficit stops (the crux at `[]`, measured green)

| map | reads | emissions | stalls | longest stall run |
|---|---|---|---|---|
| `z/φ` | 18000 | 17993 | **7** | 2 |
| `(z+1)/3` | 18000 | 17981 | 19 | 2 |
| `φz/(z+φ)` | 16000 | 15927 | 73 | 7 |
| `z/φ`, seed 1 | 12000 | 11938 | 62 | — |
| `z/φ`, seed 2 | 12000 | 11800 | 200 | — |

Stall counts grow far slower than linearly (they are flat over long stretches), so
`runClock p / p → 1`: by S7-CO that is the crux at the empty word, and by S7-SB it is the statement
"stalls have density zero".  Route A's clock coordinate is the one that comes out TRUE.

## Finding 2 — the width is a null-recurrent random walk, not a floor

`slack := log (1/width)`, `width = |det Φ| / (d·(c+d))` (exact, from the entries):

```
seed 1  n:  1000  2000  3000  4000  5000  6000  7000  8000  9000 10000 11000 12000
slack:        25   137   227   329   292   285   191   295   364   590   564   522
seed 2        38    51    13    17   119   181   167   242   272   226   213   299
```

Non-monotone, returns near `0` (seed 2 hits `4`), grows like `≍ √n` (`slack/√n ≈ 2.7`–`4.8` at
`n = 12000`, while `slack/n ≈ 0.03` and falling).  **The same behaviour appears for the RATIONAL
map `(z+1)/3`** (slack `≈ 580` at `n = 18000`) — the case where CF-normality of the image is a
theorem.  So this is not the `ℤ[φ]` obstruction; it is what these coordinates always do.

Consequences, both recorded in the kernel (S7-WQ):

* `WidthAfford` is FALSE on such a run: a null-recurrent walk occupies any bounded set with density
  zero, so for every floor `η` the narrow times have frequency `→ 1`, not `≤ δ`.
* `MeanSlack` (`Σ_{m<q} slack m ≤ A·q`) is FALSE too: `slack ≍ √m` sums to `≍ q^{3/2}`.
* And the crux `BlockForgetRun`, whose sum runs over the WIDE times only, is then vacuous
  (`crux_sum_le_of_wide_sparse`).  Non-vacuity of the crux and satisfiability of the width debt are
  the same requirement.

## The mechanism (why all of this is one picture)

The transducer is throttled to at most one emission per read, while the number of output digits the
read makes determinable is `1` on average and occasionally `2` or more.  The excess is a **queue**
of known-but-unemitted output digits; the queue is a mean-zero random walk (both sides have the
same Lévy constant), hence null-recurrent, of size `≍ √n`.  Then

* `slack ≈ 2Λ · queue`, so `slack ≍ √n` — Finding 2;
* a stall is exactly a time when the queue is EMPTY and the read determines nothing, so stalls are
  the walk's returns to `0`: infinitely many, density zero — Finding 1;
* a narrow state cannot straddle a cylinder boundary except rarely, and a straddle is what a stall
  is (S7-SS), so the narrowness is the REASON the clock keeps time.

## What it changed in the proof (lap 91)

* `VandeheyS7WidthDensity` (S7-WQ): the incompatibility, in the kernel.
* `VandeheyS7ArchWidthFree` (S7-AW): the architecture re-derived with the width filter DELETED —
  `BlockForgetAll` (the crux summed over all times) alone gives `IsCFNormal (Φ.mob x)`.
* `VandeheyS7NoReduction` (S7-NR): the signed crux is the headline restated, so the crux's only
  surplus is the absolute values, i.e. LOCAL agreement of the window statistics.

## Reproduction

The script is four short functions: `ℤ[φ]` mul/add/sign, `comp`, `emit_digit`, and the run loop;
`width` from `|det|/(d(c+d))` with `Decimal` precision set to the coefficients' digit count (the
coefficients are huge and nearly cancelling — unit drift — so a fixed precision silently returns
zero, which is the one trap in re-running this).
