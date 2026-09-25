# HANDOFF twopoint — lap 65, 2026-09-25: **the pin is UNCONDITIONAL — `peelBudget_id`**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9303 jobs**).  All new declarations
`#print axioms`-clean.  **No `sorry`.**  New file only: `src/NormalNumbers/TwoPointC3Budget.lean`;
no frozen file touched.

## The advance

Lap 64's rung 3 made the crux equivalent to the growing-depth *unweighted* surface **under** a peel
budget, and showed no CONSTANT schedule satisfies it.  That left an obvious hole: is the budget
satisfiable at all?  It is, and the hypothesis is now discharged:

    tailLarge_le_log :  2 ≤ b →  tailLarge P b m ≤ log₂(m+1) + 1        (the mirror of rung 2)
    peelBudget_id    :  2 ≤ b →  PeelBudget P b h (fun N => N)          (unconditional)
    addCharTail_iff_plain_id :
        crux  ↔  (1/N) ∑_{n<N} e(jn/Q)·e(h·depthPeel P b N n) → 0        (no hypothesis)

So C3 now has the exact analogue of C1's `twoPointWeighted_iff_growing_id`: **the crux is
equivalent to a growing-depth unweighted correlation, unconditionally**, while `no_constant_depth_budget`
(rung 3) forbids every fixed depth.  The two facts together say the depth resource is binary — it
must grow, and any growing depth states the same problem.

### Ingredients

* `tailLarge_le_log` — the *upper* bound matching rung 2's lower bound, uniform in `P` and `b ≥ 2`.
  Built from three in-tree assets nothing in C3 had consumed: `card_primeFactors_le_log`,
  `log_add_le` (`log₂(m+i+1) ≤ log₂(m+1)+i`) and `tsum_majorant`
  (`∑_{i≥0}(A+i)2^{−(i+1)} = A+1`), all in `PrimeLambertTail.lean`.  Majorising `b^{−(i+1)}` by
  `2^{−(i+1)}` makes the bound `b`-free.
* `tendsto_linear_div_two_pow` — `(2N+2)/2^N → 0` as the terms of a convergent series
  (`summable_pow_mul_geometric_of_norm_lt_one`, then `Summable.tendsto_atTop_zero`).
* The budget at `K(N) = N` is then `≤ b^{−N}(log₂(2N+1)+1) ≤ (2N+2)/2^N`.

## Ladder state — rungs 0–3 complete, rung 3 now hypothesis-free

| rung | statement | commit |
|---|---|---|
| 0 | `isRichSubpoly_of_weylTailAlmostAll` | `6978dd5` |
| 1 | `addCharTail_depthOne` | `29a4d7d` (lap 61) |
| 2 | `tendsto_mean_tailLarge_atTop` | `81606d2` |
| 3 | `addCharTail_iff_depthWeighted`, `no_constant_depth_budget`, `addCharTail_iff_plain_of_budget` | `f7f8d1c` |
| 3′ | `peelBudget_id`, `addCharTail_iff_plain_id`, `tailLarge_le_log` | this lap |

## NEXT SESSION

1. **TT2025 §5.2 — the alternating-sum / Gowers trick.**  The only directive item untouched, and
   the literature's actual route from growing depth to PAIRWISE correlations.  `depthPeel` is now
   the right vocabulary: the first target is the *combinatorial cancellation identity*
   `∑_{ε∈{0,1}^K} (−1)^{|ε|}·(first K terms of the tail at n + ⟨ε,v⟩) = 0` for `p_ε = p₀+∑ε_iv_i`
   all prime.  Read `papers/tao-teravainen-2025-quantitative-correlations.txt` §5.2 first.
2. **The adjacent unconditional item** `SwingC3Signed.lean` names and nobody did:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0` (one-term bound into the proved `norm_primeFactor_sq_le`,
   then `mertens_lower`).
3. **Harden rung 0**: derive `ScalesDense` from a log-density hypothesis on the exceptional set.
4. Sharper schedule: `peelBudget` for `K(N) ≈ log_b log log N` — `tailLarge_le_log` already gives
   the mean bound, so this is now a one-lap arithmetic exercise if anything needs the slow rate.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` (every scale) TRUE 97%; provable with known techniques 8%.
- `WeylTailAlmostAll` from 2026 literature 70%; ⇒ `IsRichSubpoly` **in the kernel**.
- Depth resource fully characterised (no fixed depth; all growing depths equivalent): **certain**.
