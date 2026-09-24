# HANDOFF twopoint — SESSION WRAP (laps 1–10), 2026-09-24

Branch `wip/twopoint-avg`.  HEAD at wrap: see `git log -1` (lap-10 handoff commit).
Working tree clean; every lap committed green (`lake build` verified by pre-commit hook).

## What this run was, and what it found

Kickoff (`KICKOFF-2026-09-24-twopoint-bet.md`) asked to (1) decide Ren's fixed-`w` worry about
`twoPointWeightedAvg_all`, (2) attempt the growing-`w` re-plumb, (3) probe for a refutation, and
declared "a refutation or an equivalence with a named open problem" a success.

**The run found something better and worse than the worry: the route's cited Kátai hypothesis
overstates the literature, and the correct inequality is now proved in kernel.**

### The finding
`KataiOrthogonalityAvg` (`PairDecoupleAvg.lean`, cited as the true averaged BSZ/Kátai criterion)
normalises the pair term by `π(w)²`.  The actual Cauchy–Schwarz normalises it by
`L(w)² = (Σ_{p≤w} 1/p)²`, because the **diagonal** `p = q` of the inner square contributes
`Σ_{p≤w} ⌊N/p⌋ = N·L(w)`.  And `π(w)/L(w)² → ∞`.  So the averaged criterion, with `ε` quantified
before `w`, does not supply what the proof consumes.

### Kernel-checked, all `[propext, Classical.choice, Quot.sound]`, all sorry-free
| File | Content |
|---|---|
| `TwoPointWorry.lean` | lap 1 — `avgShape_not_imply_pairwise`: the fixed-`w` quantifier order does NOT entail per-pair decorrelation (asynchronous near-extremal times).  Ren's worry refuted **as an argument**. |
| `TwoPointGrowing.lean` | lap 2/3 — `avgShapeGrowingSlow_of_avgShape`: full diagonal extraction producing a SLOW cutoff (`w(N)² ≤ N`).  The re-plumb is a certified weakening. |
| `TwoPointKataiQuant.lean` | lap 3 — the growing-`w` swing `conjC1_of_delange_kataiQuant_twoPointSlowGrowing`. |
| `TwoPointKataiSharp.lean` | lap 4 — `tendsto_kataiPrimeRecip` (Mertens divergence, in kernel); `KataiQuantSharp`; `avgShape_hubTable_pairSum_atTop`. |
| `TwoPointKataiGap.lean` | lap 5 — `L(w) ≤ (K+1) + √(π(w)/K)` for every `K` (split + Cauchy–Schwarz on `Σ_{n>K} 1/n² ≤ 1/K`), hence `π(w)/L(w)² → ∞`; `avgShape_not_imply_kataiBudget`.  **No PNT, no Mertens, no Chebyshev.** |
| `TwoPointHonestChain.lean` | lap 6 — `conjC1_of_delange_kataiQuantSharp_pairSumSmall`: C1 on hypotheses matching the literature, one open leaf `TwoPointPairSumSmall`. |
| `TwoPointKataiCS.lean` | lap 7 — `katai_cauchySchwarz`, the decisive step, with its true constants. |
| `TwoPointTuranKubilius.lean` | lap 8 — exact moments; `turanKubilius_raw/turanKubilius/turanKubilius_abs`. |
| `TwoPointKataiRearrange.lean` | lap 9 — `sum_kataiOmega_mul_complex` (exact); `kataiMultiplicativeError` (`≤ 2N`). |
| `TwoPointKataiAssemble.lean` | lap 10 — **`katai_master`**: the Kátai/BSZ inequality, end-to-end in kernel. |

Probe: `probes/twopoint_async_2026_09_24.py` + output at `-out-b3-1e6.txt` (hand-checked known
answers).  Every pair's two-point correlation decays monotonically, `≈ N^{-1/4}` for the slowest;
the arithmetic table is **not** asynchronous, so lap 1's logical room is not the route.

## Rules honoured
`twoPointWeightedAvg_all` never deleted, renamed or weakened.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs.  All
new code in `src/NormalNumbers/TwoPoint*.lean`, imports added to `src/NormalNumbers.lean`.
`src/` sorry count unchanged from session start (the bet's `sorry` is the only one I own; the
others are pre-existing and designated).

## Confidence at wrap
- `twoPointWeightedAvg_all` TRUE: **88%**.
- It suffices for C1 via a correctly-cited Kátai step: **5%**.
- The finding (that `KataiOrthogonalityAvg` overstates BSZ/Kátai): **95%**.

## Next session — start here
**Lap 11, highest value:** restate the honest chain directly on `kataiPairGram`.  `katai_master`
is a *theorem*, not a hypothesis, so deriving `ConjC1` from Delange + `katai_master` + a leaf
phrased on the truncated Gram sum would leave C1 resting on Delange plus **one** open leaf with
the entire Kátai step kernel-checked.  The one gap to handle: `katai_master`'s pair term is the
truncated Gram sum (`m ≤ min(⌊N/p⌋,⌊N/q⌋)`), while `KataiQuantSharp`/`TwoPointHonestChain` use
the full-range `pairSum`; prefer restating the leaf over bridging the ranges.

**For an altitude/review lap:** the finding affects more than this bet.  Every theorem in the
repo routed through `KataiOrthogonalityAvg` — `conjC1_of_delange_kataiAvg_pairDecorrAvg`,
`conjC1_of_delange_kataiAvg_twoPointWeightedAvg`, `conjC1_of_delange_kataiAvg_pairDecorrLarge`,
`conjC1_of_delange_kataiAvg_pairShiftCorrAvg` — carries a hypothesis that is not a known theorem.
Those statements are correct as conditionals and were not edited (kickoff rules), but the
*citation* of `KataiOrthogonalityAvg` as literature should be revisited by whoever owns
`PairDecoupleAvg.lean` and the README/STATUS claims about it.
