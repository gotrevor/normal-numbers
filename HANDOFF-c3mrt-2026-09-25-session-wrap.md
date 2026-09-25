# HANDOFF c3-mrt 2026-09-25 — session wrap (laps 1–6)

**Worktree** `~/src/nn-c3mrt`  **Branch** `wip/c3-mrt`  **HEAD** `5c9e15a`
**Working tree clean.**  `lake build` green (9257 jobs) at every commit.
Kickoff: `KICKOFF-2026-09-24-c3-mrt.md` (ratified 2026-09-24; newer than `DIRECTION.md`'s
2026-09-23 Theorem-C′ directive, so the C3/MRT moonshot was this run's assigned scope).
Per-lap detail: `HANDOFF-c3mrt-2026-09-25-lap1.md` (lap 1 + addenda for laps 2–6).

## The crux (unchanged, still the one named `sorry` carrying `ConjC3`)

`weylLambertTwist_holds` in `src/NormalNumbers/SwingC3Leaf.lean`.  Not weakened, renamed or
touched.  No existing statement anywhere was changed; this session is pure addition (5 new
modules, all in `src/`, none imported by the `NormalNumbers` root).

## Headline result of the session

`ConjC3` is now reduced, **axiom-clean and `sorry`-free**, to a single quantitative Elliott
correlation with only `O(log log log N)` points and a generous constant budget:

    QuantDepthElliott b
      → weylLambertTwist_of_quantDepthElliott          (C3MrtSchedule)
      → weylLambertTwist_of_depthElliottLL             (O(log log log N) points)
      → weylLambertTwist_of_schedule                   (any schedule with LL(N)/b^{D_N} → 0)
      → WeylLambertTwist b
      → conjC3_of_weylLambertTwist                     → ConjC3

and the base rung `D = 1` of that correlation is **PROVED** (`depthAvg_one_tendsto`).

## New modules (all axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`)

| module | content |
|---|---|
| `C3MrtShape.lean` | vertical (digit-depth) truncation + its pointwise price; `ee_tailDepth_eq_prod`; `DepthElliott`; `weylLambertTwist_of_depthElliott` |
| `C3MrtRungOne.lean` | `depthAvg_one_tendsto` — rung `D = 1`, natural density, from the repo's own `DelangeSlot` |
| `C3MrtMean.lean` | deep tail on average (Mertens); `weylLambertTwist_of_schedule` |
| `C3MrtSchedule.lean` | the explicit `log log log` schedule; `QuantDepthElliott` |
| `C3MrtElliottForm.lean` | multiplicativity, unimodularity, non-pretentiousness certificate |
| `C3MrtOmegaBridge.lean` | `z^ω = z^Ω ⋆ g`, `g` on the powerful numbers |

## The four real advances

1. **Vertical, not horizontal truncation** (lap 1).  All prior laps cut at a *prime* cutoff `K`,
   paying `≍ N ∑_{p>K}1/p` and forcing the impossible `log N ≪ K ≪ N`.  Cutting at *digit
   depth* `D` costs only `(log₂(n+1)+D+1)/((b−2)b^D)` pointwise.  Correlation length `N → log log N`.
2. **Deep tail on AVERAGE** (lap 2).  Only the mean discarded phase is spent, and the mean of `ω`
   is `log log`, not `log` (`sum_range_deep_le`, via the repo's `sum_omegaTail_AP_le'`).  Depth
   requirement `log log N → log log log N`.  At `b = 3` that is `D_N ≤ 4` for all `N < 2^(2^81)`.
3. **The target is a legitimate Elliott instance** (laps 4–5), certified: the `f_i = ζ_i^{ω_{>P}}`
   are multiplicative and unimodular, and `f_0` is non-pretentious against every finite-valued
   twist missing `ζ_0⁻¹`, in particular the principal character mod any `q`.
4. **The `ω → Ω` bridge** (lap 6).  `z^ω = z^Ω ⋆ g` with `g` supported exactly on the powerful
   numbers, `g(d) = (z−z²)^{ω(d)}`.  This is what reconnects the kickoff's MRT bet: it turns a
   correlation of the merely-multiplicative `ζ^ω` into an absolutely convergent sum of
   correlations of the **completely multiplicative** `ζ^Ω` along **linear forms**, which is
   exactly `Erdos67b.NonasymptoticLogElliott`'s shape.

## Kickoff items — all three answered

1. **Shape decided.**  `D`-point with `D ≍ log log log N` consecutive shifts.  **The twist
   `e(jn/Q)` supplies no cancellation**; `0 < j < Q` is not load-bearing.  Cancellation is
   non-pretentiousness of `ζ_0^{ω_{>P}}`, predicting `(log N)^{−a}` with
   `a(b,h) = ∑_{i≥1}(1 − cos(2πh/b^i)) < ∞` — matching the probe's measured `a ≈ 1.3–3.7`.
2. **`K = 1` in natural density: DONE** (and it needed no new analysis — it was already in the
   repo as the Leaf-B Delange slot).
3. **What `K ≥ 2` needs: stated precisely** as `QuantDepthElliott`, with the proof that a
   *qualitative fixed-`k`* Elliott provably cannot suffice (for fixed `D` the discarded phase has
   mean `≍ log log N/b^D → ∞` and fluctuation `≍ √(log log N)/b^D → ∞`, so the deep tail is
   neither negligible nor an asymptotically constant rotation — and no diagonal argument escapes,
   since `P` is fixed before `N`).

## Refuted, recorded — DO NOT RETRY

* **Smooth/rough sieve (Kubilius) split.**  Discarded rough factor costs `log(log N/log y)`,
  `o(1)` only for `y = N^{1−o(1)}`, where sieve independence dies.  The Chowla obstruction itself.
* **Self-similar recursion** `T(n) = (ω_{>P}(n+1)+T(n+1))/b`.  Iterating it *is* the depth
  truncation; the scale-`t/b` object reappears as its own shift, so no contraction.
* **Growing `P`.**  `rotationRouteC_of_weyl` (`SwingC3ContGlue.lean:276`) gets `P` from
  `exists_rotationCover_core`, so `P` depends only on the target word `(α,len)`, never on `N`.
* **Tao's `unitCircleLogElliott` applied directly.**  It is the `f(n)·conj f(n+h)` form (one
  function) and needs `IsCompletelyMultiplicativeOnPositive`.  Lap 6's bridge is the fix.

## NEXT — resume here

1. **`tsum_powerfulWeight_div_lt_top`**: `∑_{d powerful} |z−z²|^{ω(d)}/d < ∞`, via the Euler
   product `∏_p (1 + |z−z²|∑_{k≥2}p^{-k}) ≤ ∏_p(1 + 2/(p(p−1)))`; `|z−z²| ≤ 2` for `‖z‖ = 1`.
   Bounded work, no open mathematics.
2. **The substitution/reindexing lemma**: correlation of `ζ_i^ω` along `n+1+i` = absolutely
   convergent sum, over powerful tuples `(d_i)` and classes `n ≡ a (mod lcm d_i)`, of
   correlations of `ζ_i^Ω` along the linear forms `(L/d_i)k + (a+1+i)/d_i`.  Truncate at `d_i ≤ Y`
   using (1).
3. Then instantiate `Erdos67b.NonasymptoticLogElliott` at `D = 2` (needs its
   `pretentiousDistSqToTwist` non-pretentiousness hypothesis for `ζ^Ω`, which is the EASIER case
   of lap 5's certificate since `ζ^Ω(p) = ζ` is again constant).  Yields the **log-averaged
   `D = 2` rung** — a kickoff success criterion, not the full crux.
4. Optional, modest: **Turán–Kubilius halving** — centring `ω_i` at its mean makes the residual
   SD `≍ √(log log N)/b^D`, dropping the required depth by a factor 2.  Does not remove the wall.

## Confidence

* leaf TRUE: ≈ 95%.  The predicted exponent `∑_{i≥1}(1−cos(2πh/b^i))` now has a mechanism, not a fit.
* leaf PROVABLE with known techniques, in natural density: ≈ 15%.  Needs quantitative Elliott.
* **log-averaged `D = 2` rung reachable from the dependency via lap 6's bridge: ≈ 55%.**
