# HANDOFF c3-mrt lap 1 — the crux is an Elliott correlation with `log log N` points

Worktree `~/src/nn-c3mrt`, branch `wip/c3-mrt`.  Kickoff `KICKOFF-2026-09-24-c3-mrt.md`
(ratified 2026-09-24, newer than `DIRECTION.md`'s 2026-09-23 Theorem-C′ directive; the
C3/MRT moonshot is this run's assigned scope).

## The crux

`weylLambertTwist_holds` in `src/NormalNumbers/SwingC3Leaf.lean` (unchanged, still the one
named `sorry` carrying `ConjC3`).

## This lap's advance

**The route-decisive discovery: truncate VERTICALLY, not horizontally.**

Every prior lap truncated `tailLarge P b n = ∑_{i≥0} ω_{>P}(n+i+1)/b^{i+1}` at a *prime*
cutoff `K` (`tailTrunc`), buying `∏_{P<p≤K} p`-periodicity but paying discarded mass
`≍ N ∑_{K<p} 1/p` — the impossible window `log N ≪ K ≪ N` that `SwingC3Leaf`'s docstring
records as missing.  Truncating instead at *digit depth* `D` costs, **pointwise**,

    tailLarge P b n − tailDepth P b D n ≤ (log₂(n+1) + D + 1) / ((b−2) b^D)
    (`C3MrtShape.tailLarge_sub_tailDepth_le`, `…_le_of_lt` uniform on n < N)

only *logarithmic* in `n`.  So depth `D ≍ log_b log N` is already free, and the required
correlation length collapses from `N` to `log log N`.

### New, all axiom-clean, no `sorry` in either new module

`src/NormalNumbers/C3MrtShape.lean`
* `tailLarge_sub_tailDepth_le` / `_le_of_lt` / `_nonneg` — the vertical price.
* `ee_tailDepth_eq_prod` — the depth-`D` phase is **exactly**
  `∏_{i<D} ζ_i^{ω_{>P}(n+i+1)}`, `ζ_i = e(h/b^{i+1})`: the machine-checked identification of
  the C3 crux as an Elliott-type correlation of the multiplicative functions `ζ_i^{ω_{>P}}`.
* `depthSchedule b N = 2(⌊log_b(log₂N+1)⌋+1)`, `sq_log_le_pow_depthSchedule`,
  `depthSchedule_err_le` (error `≤ 3/(log₂N+1)` along the schedule).
* `DepthElliott b` — the named reduction target.
* **`weylLambertTwist_of_depthElliott : DepthElliott b → WeylLambertTwist b`**, axioms
  `[propext, Classical.choice, Quot.sound]`.

`src/NormalNumbers/C3MrtRungOne.lean`
* **`depthAvg_one_tendsto`** — rung `D = 1` of `DepthElliott` is **PROVED**, in natural
  density, no MRT, no log averaging: it is exactly the repo's own Leaf-B Delange slot
  `DelangeSlot.twisted_omegaLarge_mean_tendsto_zero` (itself axiom-clean).  Wiring lemmas
  `omegaLarge_eq_delange`, `norm_depthRoot`, `sum_range_shift_eq_sum_Icc`.

## Kickoff items, answered

1. **Correlation shape — decided.**  `K`-point, with `K = D_N = O(log log N)` consecutive
   shifts `n+1,…,n+D`.  **The twist `e(jn/Q)` supplies no cancellation**: the hypothesis
   `0 < j < Q` is not load-bearing, and no CRT/periodicity argument in `Q` can close the leaf.
   Cancellation is entirely non-pretentiousness of `ζ_0^{ω_{>P}}` (`∑_p (1−Re ζ_0)/p = ∞`),
   predicting decay `(log N)^{−a}` with
       `a(b,h) = ∑_{i≥1} (1 − cos(2π h / b^i)) < ∞`,
   finite because `1 − cos(2πh/b^i) ≍ b^{−2i}` — consistent with the probe's measured
   `a ≈ 1.3–3.7` and with `a ≈ 1.9` for `h = 1` at small `b`.
2. **`K = 1` in natural density — DONE**, and it did not even need Delange re-proved: it was
   already in the repo.
3. **What `K ≥ 2` needs — stated precisely.**  `DepthElliott` is *not* a fixed-`D` statement,
   and provably cannot be reduced to one: for fixed `D` the discarded phase
   `h ∑_{i≥D} ω_{>P}(n+i+1)/b^{i+1}` has typical size `≍ log log N / b^D → ∞`, and its
   *fluctuation* is `≍ √(log log N)/b^D → ∞` too, so the deep tail is neither negligible nor
   an asymptotically constant rotation.  Hence the requirement is **Elliott's conjecture
   uniform in the number of points `k`, with `k ≍ log log N`**.  Tao's
   `Erdos67b.unitCircleLogElliott` (`k = 2`, log density) and Tao–Teräväinen (odd `k`, log
   density) are fixed-`k`; that uniformity in `k` is the whole remaining obstruction.

## Confidence

* leaf TRUE: high (≈ 95%).  Two independent numerics agree on `(log N)^{−a}`, and the
  predicted `a(b,h) = ∑_{i≥1}(1−cos(2πh/b^i))` now has a mechanism, not just a fit.
* leaf PROVABLE with known techniques: low (≈ 15%).  Fixed-`k` Elliott is not enough (proved
  heuristically above, not yet in Lean); uniform-in-`k` Elliott is open.

## NEXT (attack order)

1. **Narrow the `k`-uniformity.**  Try to prove `DepthElliott` from fixed-`D` correlations
   **plus** a second-moment/variance estimate on the deep tail
   `θ_D(n) = h ∑_{i≥D} ω_{>P}(n+i+1)/b^{i+1}`.  The heuristic above says the fluctuation is
   `√(log log N) b^{-D}`; if a *Turán–Kubilius over the D-window* bound gives
   `‖θ_D − μ‖_{L²} ≪ √(log log N)/b^D`, then the honest conclusion is a *quantitative* trade:
   the fixed-`D` correlation must decay faster than `√(log log N)/b^D`.  Formalise that trade
   as a Prop — it may be reachable, since the `D = 1` rung has a *power of log* decay
   (Selberg–Delange), which beats `√(log log N)` comfortably.  **This is the crux now.**
2. Prove rung `D = 2` unconditionally if `lean-proofs-latest`'s `unitCircleLogElliott` can be
   instantiated at the two shifts `n+1, n+2` with `ζ_0^{ω_{>P}}, ζ_1^{ω_{>P}}` — log density
   only, so it gives the log-averaged variant of rung 2, not the natural-density one.
3. Extend the numerics: measure the fitted `a` against `∑_{i≥1}(1−cos(2πh/b^i))` directly
   (stdlib-only probe in `probes/`), which is a sharp falsifiable test of the mechanism.
