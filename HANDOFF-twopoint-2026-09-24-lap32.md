# HANDOFF twopoint — lap 32: depth is not a resource

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointDepthInvariance.lean` (sorry-free,
trust-triple), import added to `src/NormalNumbers.lean`.

## The advance
Routing lap 31's equivalence and the repo's fixed-depth equivalence through the crux as a hub
gives two structural facts that close off tuning strategies **in kernel**:

| result | content |
|---|---|
| `multiElliottGrowing_schedule_invariant` | any two admissible depth schedules state the SAME problem — `K(M) ≍ log_b log M` buys nothing over `K(M)=M` |
| **`multiElliottWeighted_iff_growing`** | a fixed-depth *weighted* `2K₀`-point correlation ⟺ a growing-depth *unweighted* one |
| `multiElliottWeighted_iff_growing_id`, `twoPointWeighted_iff_growing_id` | hypothesis-free instances; in particular the `K₀=1` two-point weighted leaf already equals the full unbounded-length unweighted correlation |

**Reading.**  The `peelWeight` is worth *exactly* an unbounded number of linear forms.  One cannot
drop it for a genuinely easier statement, and one cannot shorten the correlation by choosing a
cleverer depth.  Length is not the resource; cancellation in the large primes is (lap 30).

New escape hatches closed (do NOT re-open):
* "choose a cheaper depth schedule" — refuted, `multiElliottGrowing_schedule_invariant`;
* "drop the weight to get an easier leaf" — refuted, `multiElliottWeighted_iff_growing`.

## Run to date
* lap 28 `92ede26` — `DelangeKernelTail` unconditional for `‖z−1‖<1`.
* lap 29 `ab283df` — the peel weight drops at growing depth.
* lap 30 `2d4d2c3` — exact CRT counts (`card_hit_eq`) for the `2K` forms.
* lap 31 `6775ae3` — the weight-free reduction is an EQUIVALENCE (kickoff success criterion).
* lap 32 (this) — depth invariance; weight ⟺ unbounded depth.

## Next
1. The prime-cut split of `MultiElliottGrowing` (small-prime factor `→0` by `card_hit_eq` +
   Mertens; large-prime remainder named).  Value is in naming the remainder — lap 30 records that
   the triangle inequality cannot close it.
2. `DelangeKernelMean` for `‖z−1‖<1` — the last dischargeable piece of the 🟡 `DelangeMean` axiom.
   Route: Rankin/Levin–Fainleib comparison of `Σ_{n≤N} h_z(n)/n` with `Π_{p≤N}(1+(z−1)/p)`
   (`prod_delangeLocal_tendsto_zero` is already a theorem).  Genuinely analytic, multi-lap.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Route depth measured and pinned at three surfaces (weighted fixed, weighted growing,
  unweighted growing) which are now machine-checked to agree.
