# HANDOFF — entropy lap 22 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `89f49d3`.  `lake build` green, **8961 jobs**.  New module
`src/NormalNumbers/G4EntropyLevels.lean`, sorry-free, trust triple.  Preserved declarations
re-checked.

## What was proved

Lap 20 showed a quantized sampler's fate depends only on the density of its windows.  The last
concrete freedom was to keep the schedule's times and read *more* digits at each.  Closed:

| declaration | statement |
|---|---|
| `LevelBudget mm` | `2^{i+3}·H_i·mm i ≤ 2·d_min(i)` — the inequality `key_size` proves for `mm = kk` |
| `card_isSampledAt_le` | under the budget, density of the sampled positions is still `≤ 1/4` |
| `not_qForces_normal_of_levels` | hence no satisfiable hypothesis about the sample forces normality, at any budgeted level |
| `levelBudget_of_le_pow` | the budget admits every `mm i ≤ B^K`, `B = K²(K+N)+1` — levels up to `K^{3K}` |
| `not_qForces_normal_at_pow` | the statement at `mm i = B^K` |

Exported in usable form along the way: `two_mul_succ_le_gridB` (`2(K²+1) ≤ B` at the schedule's
scales) and `pow_sq_gridB_mul_le` (`(B²)^K·K ≤ Q·D₀`), the size chain that was previously buried
inside `key_size`.

## Which bottleneck moved

The freezing modulus `Q·D₀ = (U+K+N+2)!·K·U` sits so far above the sample's alphabet that the
windows can be widened by a factor `K^{3K}/(K/4)` and the read set still covers at most a
quarter of every prefix.  Brief §6's positive branch now has **no remaining degree of freedom
inside the quantized world**: not the grid translations (lap 10), not more grids (11), not more
scales (12–13), not any admissible scale (14), not any digit-local statistic (16–18), not any
quantization level (20, 22).  Outside the quantized world, a single unquantized orbit value
already forces normality (19) and the sample never determines one (21).

## Next bounded test

Nothing inside the expedition's interface is open.  Candidates, all of them new objectives
rather than laps:

1. A sampler whose datum is an unbounded-precision functional of `{2^r x}` — the repo's
   `G4Jackson` / `G4SeparatingTest` bump layer is the instance; lap 19 says such data can force
   normality, so the question becomes whether the *arithmetic* (the exponential sums the
   expedition already controls) survives without the quantizer.
2. Quantitative precision at the schedule (lap 21 item 1): from `≠` to an explicit `2^{-t}`
   separation.  Needs a local gap lemma for `sampledPosAt`, which `G4EntropyPositions` nearly
   has.
3. **Altitude.**  `DIRECTION.md` and `STATUS.md` still name `T_E` as the open objective and are
   now seven laps behind.  They are owned by review laps; grind laps must not edit them.
