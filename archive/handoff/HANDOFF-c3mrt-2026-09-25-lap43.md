# HANDOFF c3-mrt lap 43 — the `K`-fold truncation telescope is PROVED

**Branch** `wip/c3-mrt` · both targets green (`lake build` 9257; `lake build
NormalNumbers.C3MrtBudget` 8979 — the tip now imports the new module).

## What landed: `src/NormalNumbers/C3MrtMultiTrunc.lean` (sorry-free, trust triple)

Step 2 of the `K`-fold assembly, **complete** (lap 42 did its quantitative heart; this is the
telescope itself).

* `truncA` / `truncB` — the two accumulated tail constants, by the transparent recursions
  `truncA (J+1) = bridgeTail z_J Y + sqfWPartial z_J Y · truncA J`,
  `truncB (J+1) = bridgeTail z_J Y + sqfWMass z_J · truncB J`.
* `multi_truncation_telescope` — **the lap's product**.  All `J` moduli of
  `sum_pow_omega_multi_eq` cut at `Y`, error `≤ α·truncA J + β·truncB J`.
* `multi_truncation_bound` — the top-level instantiation at `S = range N`, `α = K`,
  `β = (1+log N)·K^{K²}`, fed by `joint_multi_harmonic_mass`.
* `truncB_tendsto` — `truncB z Y J → 0` as `Y → ∞` at every fixed depth, uniformly in `N`.
  This is the ε-chase enabler for step 4.

## The structural idea (the reason the induction closes)

The divergence trap of the naive iteration (`∏_{j>m} sqfWPartial ≍ Y^{(K-m-1)/2}` against
`bridgeTail ≍ Y^{-1/2}`) is avoided by carrying a **two-term block-mass invariant** on `(F, S)`
through the induction:

    ∑_{n ∈ S, ∀ s<r, g_s ∣ n + (J-r) + s + 1} ‖F n‖  ≤  α / g_0  +  β / ∏_{s<r} g_s .

Peeling the last shift with modulus `e` sends `(α, β) ↦ (α, β/e)` — the head term `α/g_0` is
untouched (it pairs with `sqfWPartial`, an `N`-independent constant) while the `β` term keeps
the full product weight and therefore pairs with the CONVERGENT `sqfWMass`.  The already-peeled
moduli form a CONSECUTIVE block, which is exactly the hypothesis `joint_multi_harmonic_mass`
wants, and the `r`-instance of the invariant for the peeled set is the `(r+1)`-instance for the
old set (append `e` at the top of the block).  `α`, `β`, `F` and `S` are therefore all
quantified INSIDE the induction.

## `K`-fold assembly scoreboard

| step | status |
|---|---|
| 1. `inner_sum_multi_forms` | DONE lap 41 |
| 2. `multi_truncation_bound` | **DONE lap 43** |
| 3. `prod_div_lcm_le`/`tuple_mass_le` over `Finset.univ` | partly paid (lap 42 `joint_class_range`) |
| 4. per-tuple rung bound + ε-chase | not started — **next** |
| 5. widen the budget | DONE lap 40 |

## NEXT

Step 4, mirroring laps 29–33 at `K = 2`: for each tuple `d` with all `d_i ≤ Y`, bound the inner
`K`-point correlation by the rung (`inner_sum_multi_forms` puts it in linear-form shape,
`multi_forms_det` gives nondegeneracy), then ε-chase — `Y` from `ε` via `truncB_tendsto` and
`bridgeTail_tendsto`, then `N → ∞` — landing in `weylLambertTwist_of_kfold_bound`'s shape
`‖depthAvg‖ ≤ A₀·D^{D²}·b^{κD}·η N`.  Note the `α·truncA K` term is `N`-independent, so it dies
under `1/log N` with no `Y`-condition at all; only the `β`-term needs `truncB` small.

Lap-40 refutations still stand (see `-session-wrap-laps40-42.md`); nothing was retried.
