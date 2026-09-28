# HANDOFF twopoint lap 2 — asynchrony probe negative; growing-`w` leaf stated and certified weaker

## Crux
`twoPointWeightedAvg_all` (`TwoPointBet.lean`), still `sorry`.

## Advances this lap

**(a) The asynchrony question, answered NEGATIVELY (probe).**
`probes/twopoint_async_2026_09_24.py` (stdlib only, hand-computed known-answer checks on `ω`),
output at `probes/twopoint_async_2026_09_24-out-b3-1e6.txt`.  For `b = 3`, `ζ = e(1/3)`, all
ordered pairs from `{2,3,5,7,11,13}`, `N ≤ 10⁶`:

    |E_{n<N} ζ^{ω(pn+1)−ω(qn+1)}|   decays MONOTONICALLY for every pair,
    fastest pairs ≈ 10⁻³ at N = 10⁶, slowest ((5,11), (3,13), (7,13)) ≈ 3–4·10⁻²,
    slow-pair rate ≈ N^{−1/4} over the last decade.

No pair stalls; no pair's near-extremal times are late.  So the logical room lap 1 opened —
asynchronous near-extremal times letting the fixed-`w` average vanish while pairs correlate — is
**not realised arithmetically**.  Lap 1's refutation of the *worry's argument* stands; lap 2 says
the escape it exposed is not the route.  Truth of the leaf rests on genuine per-pair decay
(i.e. the leaf is TRUE); ease of the leaf must come from averaging, not from asynchrony.

**(b) The growing-`w` re-plumb, stated and certified a weakening (Lean, sorry-free).**
`src/NormalNumbers/TwoPointGrowing.lean`:
- `TwoPointWeightedAvgGrowing b t` : `∃ w → ∞, E_N[twoPointAvgSum b t (w N) N] → 0`.
- `AvgShapeGrowing`, and `twoPointWeightedAvgGrowing_iff_avgShapeGrowing` (`Iff.rfl`).
- **`avgShapeGrowing_of_avgShape`** — the full diagonal extraction (`stair`/`ramp` majorants +
  `Nat.findGreatest` cutoff index), proved, no `sorry`.
- `twoPointWeightedAvgGrowing_of_twoPointWeightedAvg` — axioms `[propext, Classical.choice,
  Quot.sound]`.  So attacking the growing leaf cannot smuggle in extra strength.

## The crux as it now stands
Two obligations remain for the re-plumb to be a real route, and they are the next laps:
1. **`KataiQuantAvg`** — the quantitative Kátai/BSZ inequality with `w = w(N) → ∞`:
   `|E_{n≤N} f(n)a(n)|² ≲ (Σ_{p≤w} 1/p)^{-1} + avg_{p≠q≤w} |E_{n≤N/max(p,q)} a(pn) conj a(qn)|`.
   Ingredients live in `PairDecoupleAvg.lean` (pair-average plumbing) and
   `PairDecoupleMertens.lean` (the `Σ 1/p` lower bound).  This is Cauchy–Schwarz +
   Turán–Kubilius; no new mathematics, real Lean work.
2. Re-wire C1 onto `TwoPointWeightedAvgGrowing` via 1, then attack the growing leaf.

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%** (raised from 80% by the probe: every pair visibly
  decays, so the leaf follows from a statement that is itself empirically solid).
- PROVABLE with known techniques: **22%**.  The growing-`w` regime is the only place with room;
  whether MRT/large-sieve-in-the-multiplier reaches natural (not logarithmic) density is exactly
  the open frontier.

## Next (lap 3)
State `KataiQuantAvg` in a new `src/NormalNumbers/TwoPointKataiQuant.lean` and prove the
Cauchy–Schwarz half; leave the Turán–Kubilius half as a named sub-`sorry` IN `src/`.
