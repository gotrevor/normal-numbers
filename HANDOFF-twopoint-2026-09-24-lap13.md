# HANDOFF twopoint lap 13 — how much cancellation the leaf demands

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramBudget.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

Lap 12 reduced `ConjC1` to: `twoPointGramSum b t (w N) N = o(N·L(w N)²)`.  This lap measures the
distance between that target and the trivial bound.

* `norm_twoPointTruncSum_le` / `min_div_le` / **`twoPointGramSum_le`** —
  `twoPointGramSum b t w N ≤ N · M(w)` where `M(w) = Σ_{p≠q≤w} 1/max(p,q)`.
* `offdiag_sq`, `maxRecipSum_ge` — restricting to pairs with both primes `> z`:
  `M(w) ≥ z·D² − D`, `D = L(w) − L(z)`.
* **`tendsto_maxRecipSum_div_sq`** — `M(w)/L(w)² → ∞`.
  Proof uses only Mertens divergence (`tendsto_kataiPrimeRecip`), no prime counting: eventually
  `D ≥ L/2`, so `M(w)/L(w)² ≥ z/4 − 1` for every fixed `z`.

**Verdict.**  The saving the leaf demands over the trivial bound is an *unbounded* factor, i.e.
`sup_w M(w)/L(w)² = ∞`.  So averaging over multipliers buys nothing by itself: the leaf requires
genuine two-point cancellation for essentially every pair `(p,q)` with both primes large, at a
strength that grows with `w`.  Quantitatively, since `M(w) ≍ 2Σ_{p≤w} π(p)/p` while the budget is
`L(w)² ≍ (log log w)²`, the per-pair saving needed is `≍ L(w)²/M(w) → 0`, i.e. a `1/(#pairs)`-type
saving — strictly more than `o(1)` decorrelation per pair.

This sharpens Ren's original worry into a proved statement about the honest chain: it is NOT that
the fixed-`w` quantifier order fails to entail per-pair decorrelation (lap 1 refuted that as an
argument), it is that the **budget** in the honest Kátai inequality is `L(w)²` while the trivial
mass is `M(w) ≫ L(w)²` by an unbounded factor.

## Next attack (lap 14)

Two directions, both now precisely statable:
1. **Toward an equivalence with a named open problem.**  Show that `twoPointGramSum` small forces
   per-pair `o(1)` decorrelation for a positive proportion of pairs (a Markov/pigeonhole step on
   the pair sum), then name the resulting statement: natural-density two-point Elliott for `ζ^ω`
   along the forms `pm+1`, `qm+1` with a bounded weight — open (Tao 2016 gives only log density,
   unweighted, and only as a single-pair statement at `λ`-type correlations).
2. **Toward a proof.**  The `N`-uniformity is free (the truncated ranges are `min(N/p,N/q)`), so
   an MRT-style entropy decrement over the growing dilation set `{p ≤ w(N)}` is the only known
   mechanism that gains with `w`.  Formalising the entropy-decrement inequality is a multi-lap
   prerequisite; the first brick would be the `ℓ²` Cauchy–Schwarz that turns
   `Σ_{p≤w} ‖E_m a(pm) conj a(qm)‖` into a Gowers-type box norm over the dilation set.

Direction 1 is the cheaper and is what the kickoff calls a success ("equivalence with a named
open problem"); direction 2 is the real bet.  Lap 14 should do the Markov step of direction 1.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80% (down from 85 — the required saving is now known to be
  unbounded, which makes the truth of the leaf depend on genuine Elliott-strength cancellation).
- Provable with known techniques: 10%.
