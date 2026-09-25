# HANDOFF twopoint — lap 64, 2026-09-25: **RUNG 3 LANDED — the pin, and the ladder is complete**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9302 jobs**).  All new declarations
`#print axioms`-clean.  **No `sorry` anywhere in the new file.**  New file only:
`src/NormalNumbers/TwoPointC3Pin.lean`; no frozen file touched.

## The advance

`DIRECTION.md` rung 3 — the pin, C3's analogue of `multiElliottWeighted_iff_growing` — is done.
The exact peel identity is now in the kernel:

    tailLarge_eq_depthPeel_add :
      tailLarge P b n = depthPeel P b K n + (b^K)⁻¹ · tailLarge P b (n+K)
      depthPeel P b K n = ∑_{i<K} ω_{>P}(n+i+1)·b^{−(i+1)}

(the C3 analogue of `pairTail_eq_digitTrunc_add`; proof is `Summable.sum_add_tsum_nat_add` plus a
reindex `n+(i+K)+1 = (n+K)+i+1`).  From it, three theorems:

1. **`addCharTail_iff_depthWeighted`** — at *every* fixed depth `K`, the crux **is** the `K`-point
   weighted correlation `∏_{i<K} z_i^{ω_{>P}(n+i+1)}` twisted by the additive character and one
   unit-modulus weight `tailPeelWeight`.  Unconditional, no hypothesis on `K`: **depth is free,
   the weight is the whole content** — exactly C1's `pairDecorr_iff_multiElliottWeighted`.
2. **`no_constant_depth_budget`** — the peel budget
   `PeelBudget P b h K : (1/N)∑_{n<N} b^{−K(N)}·tailLarge P b (n+K(N)) → 0`
   **fails for every constant schedule**, because of rung 2.  (The shift by `K₀` costs at most the
   first `K₀` terms, so the shifted mean also diverges.)  So no fixed depth may drop the weight.
3. **`addCharTail_iff_plain_of_budget`** — under the budget, the crux and the growing-depth
   *unweighted* surface are equivalent.  The two surfaces differ by `≤ 16|h|·(budget)` pointwise
   (`norm_ee_sub_ee_le`, in-tree), so `squeeze_zero_norm` closes it.

Together 1–3 are the pin: **the only admissible unweighted surfaces are those whose depth grows,
and all of them state the same problem as the crux.**  "Truncate the tail at a fixed depth" is
closed off in the kernel, for C3, just as `TwoPointDepthInvariance` closed off "pick a better
depth / drop the weight" for C1.

## The ladder, complete

| rung | statement | status |
|---|---|---|
| 0 | `isRichSubpoly_of_weylTailAlmostAll` — bad scales absorbed, new rung `IsRichSubpoly` | **DONE** lap 62 `6978dd5` |
| 1 | `addCharTail_depthOne` — the depth-1 peel, unconditional | **DONE** lap 61 `29a4d7d` |
| 2 | `tendsto_mean_tailLarge_atTop` — the wall: no fixed depth | **DONE** lap 63 `81606d2` |
| 3 | `addCharTail_iff_depthWeighted`, `no_constant_depth_budget`, `addCharTail_iff_plain_of_budget` | **DONE** this lap |

## NEXT SESSION

The four mandated rungs are discharged.  What remains, in value order:

1. **TT2025 §5.2 — the alternating-sum / Gowers trick**, the one item of the directive not yet
   touched, and the literature's actual method for reducing a growing-depth combination to
   PAIRWISE correlations: choose `p_ε = p₀ + ε₁v₁ + ⋯ + ε_Kv_K` all prime and alternate over
   `ε ∈ {0,1}^K` so the first `K` terms of `∑_h ω(n+h)b^{−h}` cancel identically.  Read
   `papers/tao-teravainen-2025-quantitative-correlations.txt` §5.2 and formalise the *cancellation
   identity* first (it is combinatorial, not analytic): with rung 3's `depthPeel` now in place, the
   target is `∑_{ε} (−1)^{|ε|} depthPeel P b K (n + ⟨ε,v⟩) = 0` up to the tail.
2. **The adjacent unconditional item** `SwingC3Signed.lean` names and nobody did:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0` via the one-term bound
   `Sig_p ≥ ‖1 − e(h·b^{p−1}/(b^p−1))‖²` into the proved `norm_primeFactor_sq_le`, then
   `mertens_lower` (the right shape for it, unlike rung 2).
3. **Harden rung 0**: derive `ScalesDense` from a logarithmic-density hypothesis on the exceptional
   set, so the input is literally TT2025's `log dens E ≪ L^{−c}`.
4. **Supply a growing schedule for rung 3**: prove `PeelBudget` for `K(N) = ⌈log_b log log N⌉`
   (needs the upper bound `(1/N)∑ tailLarge(n+K) ≲ log log N`, the mirror of rung 2's lower bound
   — the double count is already there, only the `⌊N/p⌋ ≤ N/p` direction is needed).  That would
   turn rung 3's conditional into an unconditional equivalence.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` (every scale) TRUE 97%; provable with known techniques 8%.
- `WeylTailAlmostAll` provable from 2026 literature 70%; ⇒ `IsRichSubpoly` **in the kernel**.
- No fixed-depth route to the crux exists, weighted or not: **certain** (rungs 2 + 3).
- Item 4 above (`PeelBudget` for a concrete growing schedule) reachable next lap: **75%**.
