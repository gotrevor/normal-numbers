# Handoff — 2026-09-29 — joint Lambert quantitative COUNT

Branch `proof/joint-lambert-unconditional`, baseline `e2828b32`.  Objective:
`KICKOFF-2026-09-29-joint-lambert-count.md`.  Full `lake build` green at every commit
below.  Every pre-existing `JointLambert*.lean` is untouched; all work is in new modules
plus root imports.

## Status, honestly

**Proved foundations (before this campaign).**  The qualitative theorem
`jointWords_unconditional`; the gcd/non-coprime divisor average
(`sum_tau_progression_le_gcd`, `_noncoprime`, `jointA_tau_le`); the small prime pool
(`eventually_small_prime_pool`, `exists_prime_allocation_small_pool`) — at `23b3f2d2`.

**Proved this campaign.**  Every *estimate* of the counting route §§1–5.  See the table.

**NOT proved.**  The headline `jointWords_quantitative` itself.  One `sorry` remains, in
`src/NormalNumbers/JointLambertQuantitative.lean`, and it is the **assembly**: wiring the
CRT construction (`exists_joint_progression`, `exists_prime_allocation_small_pool`, the
encoder margin `δ`, `floor_digit_of_common_offset`) to the five estimates below and to
`jointWordCount_ge_of_subset`.  `jointWords_power_count` is fully derived and has no hole of
its own.

## What landed, module by module

| module | theorem | content |
|---|---|---|
| `JointLambertQuantitativeStatement` | `jointWordCount` + controls | frozen count; `∅ ⇒ N`, `N=0 ⇒ 0`, `≤ N`, monotone, witness bridge, **good-set cardinality bridge** |
| `JointLambertQuantitative` | `iteratedLog_rate_le_eps_log` | §5's `o(log N)`: `C(log log N)² log log log N ≤ ε log N` eventually |
| | `jointWords_power_count` | **derived**, no hole; `ε > 1` covered by the same inequality |
| `JointLambertCountPrimes` | `exists_prime_supply_every_height` | §1: `π(X;B,u) ≥ X/(2φ(B) log X)` at **every** large chosen `X`, `P` before `B,u`; side conditions are inequalities in `B,X` alone |
| `JointLambertCountSchedule` | `countK`, `eventually_countK_le` | `k = ⌈4 log₂ log X⌉ ≤ 6 log log X` |
| | `eventually_cube_log_le_sqrt` | `A(log L)³ ≤ θ√L` eventually, by comparing squares |
| | `eventually_schedule_feasible` | §3: **both** side conditions hold for `B ≤ (2k³)^(1+ck²)` |
| `JointLambertCountCandidates` | `candidate_count_ge` | `M/(4 log X) ≤ N`; the `+1` in `M` is paid by the factor `2`, not by `log X` |
| | `exists_candidate_indices_every_height` | §1+§3 combined: `≥ M/(4 log X)` prime candidate indices at every large `X` |
| `JointLambertCountTail` | `sum_half_Ico_le` | `∑_{[k,J)}(1/2)^j ≤ 2(1/2)^k` |
| | `near_middle_tail_le` | §4 near+middle: `≤ W(2(1/2)^k + τ(A)·2(1/2)^L)` |
| | `far_tail_le` | §4 far, **without** `τ(n) ≤ 2√n` |
| | `three_range_tail_le` | the three ranges assembled |
| `JointLambertCountMarkov` | `card_bad_le`, `card_good_ge`, `card_good_ge_half` | Markov at the FIXED threshold, keeping the `Finset` cardinality |
| `JointLambertCountRate` | `eventually_rate_le` | §5's sharp rate: `(1+ck²+a)log(2k³) + log(8 log N) + 2 ≤ C(log log N)² log log log N` |

All `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).

## Two mathematical findings

1. **The far range does not need `τ(n) ≤ 2√n`.**  The note reaches for it to get
   `(√Y+√J)2^{-J}`.  At `J = ⌊(log₂ X)²⌋` one has `2^J = X^{log₂ X}`, which dwarfs
   `Y = 2QX`, so the crude `τ(n) ≤ n` (already frozen as `tsum_tau_div_le`) suffices.  One
   whole estimate leaves the dependency chain.
2. **Feasibility and rate want different bounds on `log B`.**  `eventually_schedule_feasible`
   can afford the wasteful `log B = O_c(k³)` — it only has to beat `√log X`.  The *rate*
   lemma must use the sharp `O_c(k² log k)`, and that is precisely what turns
   `(log log N)³` into `(log log N)² log log log N`.  Keeping the two separate made both
   proofs short; conflating them is what made the older route look harder than it is.

## Exact next boundary

The remaining obligation is mechanical but not small: the §3 arithmetic assembly.  In order:

1. Fix `c = ∏_{b∈S} b`, and `a, r, δ` from `evenEncoding`, exactly as
   `jointWords_unconditional` does (that proof is the template — reread its first 60 lines).
2. At a chosen large `X`: `k = countK X`, `L = k³`; take `P` from
   `exists_candidate_indices_every_height`, then the pool from
   `exists_prime_allocation_small_pool` avoiding `P`, then `R, A, B, Q` from
   `exists_joint_progression`.  Check `B ≤ (2k³)^(1+ck²)` by `jointB_le` with `L := k³`.
3. Feed `three_range_tail_le` with `H = ⌈√Y⌉`, `Y = 2QX`, `J = ⌊(log₂ X)²⌋`; check
   `k < L < J` eventually and `n_m + j ≤ Y`.  Show the resulting bound is
   `≤ θ · (M/(4 log X)) / 2` with `θ = 2δ` — this needs `jointA_tau_le` for `τ(A)` and the
   two limits `(log X)²2^{-k} → 0`, `(log X)²(a+1)(c+1)^{k²}2^{-k³} → 0`.
4. `card_good_ge_half` on the candidate `Finset`; map `m ↦ Qp - r - 1` into offsets
   (injective since `A > 0`); `floor_digit_of_common_offset` reads the words.
5. All-`N`: `k_N = countK N`, `D_N = 2(2k_N³)^(a-1)`, `X = ⌊N/D_N⌋`; then
   `eventually_rate_le` converts `X/(8B log X) ≥ N exp(-C…)`.

Nothing above is believed to be blocked; step 3's two limits are the only remaining
analytic work, and both are of the same shape as `eventually_cube_log_le_sqrt`.

Not in scope and untouched: AGP, full normality, Vandehey (owned by the main checkout).
