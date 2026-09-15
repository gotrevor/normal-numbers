# Probe: how many row-balanced functions are there really?

**Date**: 2026-09-15 (objective R, lap 164) · exhaustive enumeration, `0/1`-valued functions.

## Why

`card_pairs_le_of_determining` bounds a family of samplers by `(2M+1)^{2|Sdet|}`, and for
row-balanced samplers the determining set used is `skel` (via `MDF`), of size `K(s+1)^{K−1}`.
`balanced_strictly_stronger` shows balance is *strictly* stronger than `MDF`, so the bound may
be loose.  `balance_not_determined_by_axes` already killed the obvious fix (shrink `skel` to the
axis skeleton).  This probe measures how loose the bound actually is.

## Method

Enumerate every `0/1`-valued function on `(Fin K → Fin (s+1))` satisfying the mixed-difference
condition on every unit cube (for `0/1` values, balance and `MDF` coincide: the level sets are
`ρ` and `1 − ρ`).  Free variables: the `|skel|` values on the skeleton; the rest are forced by
the recursion, and an assignment survives iff every forced value lands in `{0,1}`.

## Result

| `K` | `s` | `#points` | `|skel|` | `2^{|skel|}` (the bound) | true count | `log₂` true |
|---|---|---|---|---|---|---|
| 2 | 1 | 4 | 3 | 8 | 6 | 2.58 |
| 2 | 2 | 9 | 5 | 32 | 14 | 3.81 |
| 2 | 3 | 16 | 7 | 128 | 30 | 4.91 |
| 2 | 4 | 25 | 9 | 512 | 62 | 5.95 |
| 3 | 1 | 8 | 7 | 128 | 70 | 6.13 |
| 3 | 2 | 27 | 19 | 524288 | 15914 | 13.96 |

At `K = 2` the count is exactly `2^{s+2} − 2` — as it must be, since
`ignores_coord_of_balanced_two` makes a balanced function a function of one coordinate
(`2·2^{s+1}` of those, the two constants double-counted).

## Verdict

The `skel` bound is loose by a **constant factor in the exponent**, not structurally: at
`K = 3, s = 2` the true exponent is `13.96` against the bound's `19` (ratio `0.73`), and the
`K = 2` column shows the gap does not close as `s` grows.  A constant-factor improvement in the
exponent would shift the schedule's coefficient `(2dmax+1)^{2E}` but not the density rate
`dmin^{−H/2}`, which is set by `union_card_le`, not by the family count.

**So: no sharpening of the density rate is available from counting balanced families.**  Recorded
as refuted; do not retry.  The two positive results from the attempt stand as theorems
(`balanced_strictly_stronger`, `balance_not_determined_by_axes`).
