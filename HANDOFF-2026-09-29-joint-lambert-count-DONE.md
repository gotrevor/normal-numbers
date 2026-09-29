# Handoff — 2026-09-29 — joint Lambert quantitative COUNT: **DONE**

Branch `proof/joint-lambert-unconditional`, baseline `e2828b32`.  Objective:
`KICKOFF-2026-09-29-joint-lambert-count.md`.  **Target met.**

## What is proved

Both ratified headlines, in `src/NormalNumbers/JointLambertQuantitative.lean`, with their
full dependency chains, `#print axioms`-clean (`propext, Classical.choice, Quot.sound`):

* `jointWords_quantitative` — for every finite `S` of bases `≥ 2` and every fixed valid
  nonempty word in each base, `A(N) ≥ N exp(-C (log log N)² log log log N)` for **every**
  `N ≥ N0`, unconditionally;
* `jointWords_power_count` — for every **fixed** `ε > 0`, eventually `A(N) ≥ N^(1-ε)`.

The count itself is frozen in `JointLambertQuantitativeStatement.lean` (`jointWordCount`,
classical decidability, offset convention: `n` is the offset and the first requested digit
is `n+1`), with the boundary controls `∅ ⇒ N`, `N=0 ⇒ 0`, `≤ N`, monotone.

Permanent audit: `scripts/check-joint-lambert-count.sh`.  It checks, in order, that every
pre-existing `JointLambert*.lean` is byte-identical to `e2828b32`; that `lake build` is
green; the exact ratified headline types; the `{2,4}` specialization of both; the boundary
controls; and the transitive axioms of both headlines plus the whole new chain.  It fails
loudly on `sorryAx`.

## The route, module by module (new modules only)

| module | content |
|---|---|
| `JointLambertQuantitativeStatement` | `jointWordCount`, controls, witness and good-set bridges |
| `JointLambertCountPrimes` | §1 prime supply at **every** large chosen `X`, `P` fixed before `B,u` |
| `JointLambertCountSchedule` | `countK = ⌈4 log₂ log X⌉`, schedule feasibility |
| `JointLambertCountCandidates` | `≥ M/(4 log X)` prime candidate indices at every height |
| `JointLambertCountTail` | near/middle/far three-range bound; `countJ`, `far_cost_le` |
| `JointLambertCountMarkov` | Markov at a fixed threshold, keeping the `Finset` cardinality |
| `JointLambertCountRate` | the sharp `(log log N)² log log log N` rate |
| `JointLambertCountAssembly` | `binTail_eq_three_range`, `exists_candidate_data_at_height`, the window comparison, `exists_good_starts_at_height`, the §5 all-`N` transfer |
| `JointLambertQuantitative` | `iteratedLog_rate_le_eps_log` and both headlines |

## Four mathematical findings against the note's plan

1. **The far range does not need `τ(n) ≤ 2√n`.**  `τ(n) ≤ n` suffices at the split point.
2. **`J` is better chosen adaptively.**  `countJ k Y₀ X = k³ + 2S` with `2^S > (Y₀+1)(X+1)`
   makes the far cost an unconditional `O(X^{-2})`, uniform in `k`.  The note's fixed
   `J = ⌊(log₂X)²⌋` works but is neither necessary nor the easiest to verify.
3. **Feasibility and rate need different bounds on `log B`.**  Feasibility can afford the
   crude `O_c(k³)`; the rate must use the sharp `O_c(k² log k)`.  That separation is
   precisely what turns `(log log N)³` into `(log log N)² log log log N`.
4. **`B³ ≤ X` is a factor two short.**  The bracket of `three_range_tail_le` carries `2H`
   with `H ≍ √(2QX)`, and `M ≍ X/B`; at the cube both are `X^{2/3}`, so `H = o(M)` fails.
   Repair, free of new analysis: run `eventually_schedule_feasible` at the inflated pool
   exponent `4c+4`, which gives `B¹² ≤ X` (`eventually_modulus_pow_twelve_le`), whence
   `sqrt_window_mul_le`.

A fifth, recorded earlier in the campaign: the middle cost needs no logarithms, since
`(c+1)^{k²}2^{-k³} = ((c+1)2^{-k})^{k²} ≤ 2^{-k}` as soon as `2(c+1) ≤ 2^k`.

## State

HEAD on `proof/joint-lambert-unconditional`; working tree clean; full `lake build` green;
the audit script passes.  Nothing in `wip/`; no `sorry` was relocated at any point.

Not in scope and untouched: AGP (its pre-existing gaps in `JointLambertAGPRange.lean`
remain, deliberately), full normality, Vandehey (owned by the main checkout).
