# HANDOFF elliott 2026-09-25 lap 47 — leaf 2 opened: the crude Euler-product bound

Branch `wip/elliott-port`.  `lake build NormalNumbers.ElliottEulerBound` green (9565 jobs).

The dilated crux closed last lap (`dilatedCMLogElliott`, trust triple).  The **only** open
obligation between here and `Erdos67b.NonasymptoticLogElliott` is
`ElliottLadder.nonasymptotic_of_affineCM` (`ElliottLadder.lean:297`), i.e. DIRECTION item 3.

This lap landed its step (a): `NormalNumbers.ElliottEulerBound.sum_Icc_le_euler_product`, the crude
Euler-product upper bound for a nonnegative multiplicative function.  See `PENDING_WORK.md`
(2026-09-25 lap 47) for the route and the ordered next steps.

## Open `sorry`s in scope (1)

| # | obligation | file:line |
|---|---|---|
| 1 | `nonasymptotic_of_affineCM` (leaf 2, Hall) | `ElliottLadder.lean:297` |

## NEXT (lap 48)

Turn the exponential bound into `C · log Y · exp(-Σ_Y)` via Mertens; that settles Case A's
`log W ≥ θ log X` regime.  Then Hall.
settles Case A's `log W ≥ θ log X` regime.  Then Hall.
