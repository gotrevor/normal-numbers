# HANDOFF twopoint lap 19 — the per-pair target, and a correction

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramSufficient.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Correction to laps 17–18 (recorded in the file's header too)

Those handoffs said "both Cauchy–Schwarz routes are refuted".  That overstates what is proved:

* lap 13 refutes *trivial per-pair estimates*, not a route.
* laps 17–18 refute the *fourth-moment presentation* as an estimation strategy (it demands an
  evaluation to vanishing relative error), not every possible bound on `kataiPairGramSq`.

Neither rules out a direct argument.  Read "refuted" in those two handoffs as "refuted as an
estimation strategy".  The mathematics in them is unaffected — every statement there is exact.

## Advance on the crux

The positive counterpart, using `M(w) ≤ 2π(w)` from lap 18:

* **`twoPointGramSum_le_of_uniform`** — if `‖T_{p,q}(N)‖ ≤ δ·N/max(p,q)` for all `p ≠ q ≤ w`
  (a uniform *relative* saving `δ` over the trivial bound), then
  `twoPointGramSum b t w N ≤ 2δ·N·π(w)`.
* **`gramBudget_of_uniform_saving`** — hence `δ ≤ ε·L(w)²/(2π(w))` delivers the leaf's budget
  `twoPointGramSum ≤ ε·N·L(w)²`.

**The target, stated precisely.**  The leaf follows from: for every `ε > 0` there is a slowly
growing `w(N)` with, for all primes `p ≠ q ≤ w(N)`,

    ‖ Σ_{m ≤ min(N/p, N/q)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W_{p,q}(m) ‖
        ≤  (ε L(w)²/(2π(w))) · N / max(p,q) .

The saving is measured in the **size of the primes** (`L(w)²/π(w)`), not in `N`; `N`-uniformity
is free.  Since `w(N)` may grow arbitrarily slowly, the demanded saving can be made as weak as
`L(w)²/π(w)` for any `w → ∞` — for instance `w(N) = log log N` makes it a fixed-small-primes
statement with saving `≍ (log log w)² log w / w`.  This is the shape in which Elliott-type input
would arrive and is the concrete goal for any future analytic lap.

## State of the bet at lap 19

- Kernel chain: `conjC1_of_delange_twoPointGram` = Delange + one arithmetic leaf (laps 11–12).
- Kátai/BSZ inequality: proved end-to-end (`katai_master`, `katai_mean_sq`).
- Leaf placement: not equivalent to fixed-pair Elliott in either direction (laps 13–14).
- Leaf pricing: trivial estimates insufficient (13); fourth-moment presentation demands exact
  evaluation (17–18); a uniform per-pair relative saving `L(w)²/π(w)` suffices (19).

## Next attack (lap 20)

Attack the per-pair target for the easiest pairs.  For a *fixed* pair `(p,q)` the statement is a
weighted two-point correlation along `pm+1`, `qm+1`; the required saving is a constant (depending
on `w`), so for the smallest primes the target is qualitative decorrelation with an explicit
constant.  The concrete first brick: `p = 2, q = 3` with `b = 3`, bounding
`‖Σ_m ζ^{ω(2m+1)} conj ζ^{ω(3m+1)} W(m)‖` by `θ·N/3` for some explicit `θ < 1` — even a small
explicit gain, proved in kernel for one pair, would be the first arithmetic (rather than
structural) progress on the leaf and would show the target is not vacuous.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 5% (revised up slightly from
  lap 18's 3%, since the per-pair target is weaker than fixed-pair Elliott).
