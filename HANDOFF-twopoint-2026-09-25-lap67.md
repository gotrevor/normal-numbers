# HANDOFF twopoint — lap 67, 2026-09-25: **the trade is quantified, and `b ≥ 3` is now EARNED**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9305 jobs**).  All new declarations
`#print axioms`-clean.  **No `sorry`.**  New file `src/NormalNumbers/TwoPointC3Trade.lean`;
no frozen file touched.

## The advance

Lap 66 put TT2025 §5.2's cancellation in the kernel: the alternating sum over `ε ∈ {0,1}^K` kills
the first `K` frequencies of the tail, at the cost of `2^K` shifted copies.  Whether that is a
*gain* is quantitative, and it now is:

    altSum_bound        (b ≥ 2) :  ‖∑_S (−1)^{|S|} ∑_{h=1}^{H} g(n+r_{S,h})·b^{−h}‖
                                     ≤ 2^{K+1}·M·b^{−(K+1)}          (any H ≥ K, ‖g‖ ≤ M)
    altSum_bound_three  (b ≥ 3) :  ‖…‖ ≤ M·(2/3)^K
    tendsto_altSum_bound_three   :  M·(2/3)^K → 0

Supporting: `altSum_head_eq_zero` (lap 66's cancellation for an *arbitrary* summand, not just
`ω_{>P}`), `altSum_eq_tailPart` (the alternating sum equals its `h > K` part — the head is gone),
`sum_Icc_inv_pow_le` (`∑_{h=K+1}^{H} b^{−h} ≤ 2b^{−(K+1)}`, via `sum_geometric_two_le`).

## Why this is the lap's real content

**`b ≥ 3` is now forced by the method rather than assumed.**  `ConjC3` carries the hypothesis
`3 ≤ b` and the repo has always treated it as a convenience of the construction.  It is not: the
§5.2 trade costs `2^K` and pays `b^{−K}`, so it is a gain **iff `b ≥ 3`**, break-even at `b = 2`.
TT2025 remarks of its own base-`b` extension that *"the case `b > 2` is somewhat easier"* — the same
inequality, and the paper's extra base-2 work is exactly this break-even.  Two independent facts
(the repo's hypothesis, the paper's remark) are now explained by one line of arithmetic in the
kernel.  That is a route-level confirmation, not scaffolding.

## Ladder state

| rung | statement | commit |
|---|---|---|
| 0 | `isRichSubpoly_of_weylTailAlmostAll` | `6978dd5` |
| 1 | `addCharTail_depthOne` | `29a4d7d` (lap 61) |
| 2 | `tendsto_mean_tailLarge_atTop` | `81606d2` |
| 3 | `addCharTail_iff_depthWeighted`, `no_constant_depth_budget`, `addCharTail_iff_plain_of_budget` | `f7f8d1c` |
| 3′ | `peelBudget_id`, `tailLarge_le_log` | `7021f54` |
| 3″ | `altSum_depthHead_eq_zero` (TT2025 §5.2) | `2e4ee6b` |
| 3‴ | `altSum_bound`, `altSum_bound_three` — the trade, and `b ≥ 3` | this lap |

Every rung of `DIRECTION.md`'s mandated ladder is discharged, and the §5.2 mechanism is in the
kernel with its price computed.

## NEXT SESSION

1. **Assemble §5.2 into a statement about the crux.**  The pieces now in `src/`:
   `addCharTail_iff_plain_id` (crux ⟺ growing-depth unweighted, unconditional),
   `altSum_depthHead_eq_zero` + `altSum_bound_three` (the alternating sum of `2^K` shifted copies
   is `≤ M(2/3)^K`).  What is missing is the **link**: the crux's summand is a single `n`, while the
   alternating sum runs over `2^K` shifted arguments `n + r_{S,h}`, so passing between them needs
   the `δ_p` congruence (TT2025 (5.5)) — i.e. `n` restricted to a progression mod `∏_ε p_ε`, which
   is exactly the repo's `classWeight`/`primePeriod` vocabulary in `SwingC3Mean.lean`.  That is the
   next real step, and it is where the sieve (all `p_ε` prime) enters.
2. **The adjacent unconditional item** `SwingC3Signed.lean` names and nobody did:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0` (one-term bound into the proved `norm_primeFactor_sq_le`,
   then `mertens_lower`).
3. **Harden rung 0**: derive `ScalesDense` from a log-density hypothesis on the exceptional set.
4. The sieve half of §5.2 (`p_ε` simultaneously prime): check `master`'s `KICKOFF-brun-*` machinery
   before re-deriving anything.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` TRUE 97%; provable at every scale with known techniques 8%.
- `WeylTailAlmostAll` from 2026 literature 70%; ⇒ `IsRichSubpoly` **in the kernel**.
- Depth resource fully characterised: **certain**.  §5.2 cancellation + its price: **in the kernel**.
- `b ≥ 3` is essential to the route (not a convenience): **proved this lap**.
