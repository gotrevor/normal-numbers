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

**NOT proved.**  Exactly ONE `sorry` remains in the whole chain:
`exists_good_starts_at_height` in `src/NormalNumbers/JointLambertCountAssembly.lean`
(the chosen-height theorem, steps 1–4 of the note's §§3–4).  Everything else is proved:
`JointLambertQuantitative.lean` is sorry-free, both headlines are derived, and the §5
all-`N` transfer `exists_joint_small_tail_count` is proved.

Verify with `#print axioms NormalNumbers.JointLambert.jointWords_quantitative`: the only
non-standard axiom is `sorryAx`, traceable to that single declaration.

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

## Progress after the first handoff draft

Landed since: `exists_good_starts_at_height` introduced as the single named crux; both
headlines and the §5 transfer proved from it; `countK_le_countK` (monotone above
`log X ≥ 1` — the threshold is load-bearing, `Real.log` is not monotone through `0`);
`countD`/`countD_pos` (positivity needs `1 ≤ countK X`, since `2·(2·0³)^(a-1) = 0`);
`eventually_polylog_le`; `eventually_height_ge` (`⌊N/D_N⌋ → ∞`, `D_N` polylogarithmic);
`eventually_near_cost_small`, `eventually_middle_cost_small`, `pow_two_countK_ge`,
`eventually_countK_ge`; `progression_le_window`, `le_sqrt_succ_sq`,
`progression_window_le_sq`.

A third mathematical finding: the middle cost needs no logarithms.
`(c+1)^{k²}(1/2)^{k³} = ((c+1)2^{-k})^{k²} ≤ 2^{-k²} ≤ 2^{-k}` as soon as `2(c+1) ≤ 2^k`,
so the middle cost is literally `(a+1)` times the near cost.  The note's route through
`O_a(1) + 2 log log X + k² log(c+1) − k³ log 2 → −∞` is correct but unnecessary.

## Exact next boundary

The one remaining obligation is `exists_good_starts_at_height`, the chosen-height theorem.
The qualitative single-witness analogue is `exists_joint_small_tail_rescaled`
(`JointLambertRescaledTail.lean`, ~330 lines) — that proof is the structural template, with
the schedule `X = 2^(4k¹²)` replaced by a caller-chosen `X` and `k = countK X`, and the
final witness extraction replaced by `card_good_ge_half`.  In order:

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

Nothing above is believed to be blocked, and no analytic work remains: steps 3 and 5's
limits are all proved (`eventually_near_cost_small`, `eventually_middle_cost_small`,
`eventually_rate_le`, `eventually_height_ge`), and step 3's window bounds are
`progression_window_le_sq`.  What is left is the arithmetic wiring, of roughly the size of
`exists_joint_small_tail_rescaled`.

A useful further decomposition, if the single proof proves unwieldy: split
`exists_good_starts_at_height` into (a) a CRT-plus-candidate-`Finset` statement at height
`X` carrying `B ≤ (2k³)^(1+ck²)`, `Q ≤ (2k³)^(a-1)`, the divisor data and
`|T| ≥ M/(4 log X)`, and (b) a statement that the total three-range tail over that `T` is at
most `δ · |T|`.  Then (a) + (b) + `card_good_ge_half` is the theorem.

Not in scope and untouched: AGP, full normality, Vandehey (owned by the main checkout).

## Checkpoint, end of lap

Branch `proof/joint-lambert-unconditional`, HEAD `b60dc7e3`, baseline `e2828b32`.
Working tree clean; full `lake build` green; nothing uncommitted.  Fourteen green commits
this lap, every one build-verified by the pre-commit hook.

`box done` NOT run: the target is not met.  One disclosed `sorry` stands on the crux, which
is the correct checkpoint state, not a completion.
