# HANDOFF c3-mrt 2026-09-25 lap53 — the additive twist costs only `Q`

**New file** `src/NormalNumbers/C3MrtTwist.lean` (imports `C3MrtBudget`; the new chain tip:
`lake build NormalNumbers.C3MrtTwist`).  Sorry-free, 5 declarations, all
`[propext, Classical.choice, Quot.sound]`.  `lake build` also green (9257 jobs).

## The gap this closes

Lap 52 finished the `K`-fold assembly: `rung_multi_correlation` bounds the log-averaged,
**untwisted** `K`-point correlation.  `weylLambertTwist_of_kfold_bound` wants a bound on
`depthAvg b P Q j h D N`, which carries the **additive twist** `e(jn/Q)`.  Three gaps separate
them.  This lap kills the first outright.

**Insight.**  `e(jn/Q)` is `Q`-periodic, hence *constant* on each residue class mod `Q`, and `Q`
is quantified BEFORE `N` in `QuantDepthElliott` — so splitting `range N` into its `Q` classes
factors the twist out completely at the cost of the triangle inequality and an
`N`-independent factor `Q`:

* `ee_add_intCast`, `ee_twist_mod` — the periodicity, and class-constancy of the twist.
* `norm_sum_twist_le` — `‖∑_{n<N} e(jn/Q) F n‖ ≤ ∑_{r<Q} ‖∑_{n≡r} F n‖`
  (`Finset.sum_fiberwise_of_maps_to`).
* `class_sum_reindex` — `n = Qm + r` (`Finset.sum_nbij'`; note `omega` cannot see `%`/`/` with a
  VARIABLE modulus, so `Nat.div_add_mod` / `Nat.mul_add_div` / `Nat.mul_add_mod` are used by
  hand).
* `norm_depthAvg_le_progressions` — the payload:
  `‖depthAvg b P Q j h D N‖ ≤ (∑_{r<Q} ‖∑_{m : Qm+r<N} ∏_{i<D} ζ_i^{ω_{>P}(Qm+r+i+1)}‖)/N`.

**Why this matters structurally.**  The inner sums are correlations of `ζ_i^{ω_{>P}}` along the
`D` linear forms `Q·X + (r+i+1)`, whose pairwise determinants are `Q·(i'−i) ≠ 0`.  Those are
*exactly* the objects `KPointLogElliott D` governs.  **No new analytic input is needed for the
twist** — it was never a source of difficulty, only of bookkeeping.  (`C3MrtShape`'s docstring
"Why the twist is not the source of cancellation" argued this heuristically; it is now proved.)

## The two gaps that remain

1. **log-average → natural average.**  `rung_multi_correlation` is log-weighted
   (`(n+1)^{-1}`), `depthAvg` is natural (`1/N`).  This is a genuine open problem in the
   Chowla/Elliott circle, not bookkeeping, and it is now the route's outermost obstruction.
2. **`Ω` vs `ω_{>P}`.**  `rung_multi_correlation` uses `omegaNat` (all primes);
   `norm_depthAvg_le_progressions` produces `omegaLarge P` (primes `> P`).  `P` is FIXED before
   `N`, so the small-prime factor is a bounded multiplicative perturbation — a finite Euler
   product's worth of bookkeeping, not an analytic input.  Expect this to be closeable.

## NEXT

Attack gap 2 (`Ω` vs `ω_{>P}`) — it is the closeable one, and closing it leaves the ledger with
*exactly one* structural gap (log vs natural density) plus the decay class of lap 40.  Concretely:
`ζ^{ω_{>P}(n)} = ζ^{Ω(n)} · ζ^{-ω_{≤P}(n)}`, and `ζ^{-ω_{≤P}}` is a `∏_{p≤P} p^{...}`-periodic-ish
factor; the clean route is to note that `ζ^{ω_{>P}}` is itself completely multiplicative on
integers coprime-ish to `P!` and re-run the rung with `z_i^{ω_{>P}}` in place of `z_i^{Ω}` — i.e.
generalise `rung_multi_of_named_inputs` from `zOmInt` to an arbitrary unimodular completely
multiplicative `f` whose non-pretentiousness certificate is supplied (the archimedean laps 18–21
already prove it for `ζ^{ω_{>P}}`: `pretentiousDistSq_ge_class_sum` sums over `p > P`).
