# HANDOFF elliott 2026-09-25 lap 51 — Case A's thick-window regime is closed

Branch `wip/elliott-port`.  `lake build NormalNumbers.ElliottCaseA` green (9566 jobs).
DIRECTION item 2 (the dilated crux) closed at lap 46; this is item 3.

The only open `sorry` in scope remains `ElliottLadder.nonasymptotic_of_affineCM`
(`ElliottLadder.lean:297`).  Laps 47–51 built its Case A end to end:

| lap | brick |
|---|---|
| 47 | `ElliottEulerBound.sum_Icc_le_euler_product` — crude Euler product, primorial-power route |
| 48 | `sum_Icc_le_exp_prime_sum` — `∑_{m≤Y} f m ≤ exp(1 + ∑_{p≤Y} f p)` |
| 49 | `sum_Icc_le_log_mul_exp_neg_defect` — Mertens ⟹ `≤ e^{1+B} log Y e^{-Σ_Y}` |
| 50 | `ElliottCaseA.normDivArith` + pointwise bound + affine-form transfer |
| 51 | `norm_elliottLogCorrelation_le_caseA`, `exists_caseA_threshold` |

All trust triple.  Details and the threshold choreography: `PENDING_WORK.md` laps 47–51.

## NEXT (lap 52)

**Hall's inequality** — the thin-window regime `log W < θ log X`, the hard core of leaf 2.
`∑_{m ≤ Y} h(m) ≪ (Y/log Y) ∏_{p≤Y}(1 + h(p)/p + …)` for nonnegative multiplicative `h ≤ 1`;
partial summation over `O(log W)` dyadic blocks then gives the thin-window bound.
