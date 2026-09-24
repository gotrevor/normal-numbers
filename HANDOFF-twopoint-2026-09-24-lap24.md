# HANDOFF twopoint lap 24 (REVIEW LAP) — 2026-09-24

Branch `wip/twopoint-avg`.  Full build 🟢 green (9282 jobs).  New file
`src/NormalNumbers/TwoPointGramDiagonal.lean`, all declarations
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## The crux, as of this lap

`PairDecorr b t` for ONE fixed pair of distinct primes:
`E_{m≤M} e(t(omegaTail_b(pm) − omegaTail_b(qm))) → 0`.  It is now the ONLY non-Delange input to
`ConjC1`.

## The advance

**The diagonal correction.**  The growing-`w` leaf
`twoPointGramSum b t (w N) N = o(N·L(w N)²)` has `w` *existentially* quantified, so it must hold at
only ONE cutoff per `N`.  Diagonalising, fixed-pair `o(N)` decorrelation already closes it:

* `exists_slow_cutoff` — if `F w · → 0` for each fixed `w ≥ 2`, then `F (w N) N → 0` along some
  `w(N) → ∞` with `w(N)² ≤ N`.  **No uniformity in `w` is needed.**
* `gramRatio_tendsto_of_fixedPair` — at a fixed cutoff the Kátai ratio is a finite sum of `o(N)`
  terms over a positive constant `L(w)² ≥ 1/4`.
* `twoPointPairGramSmall_of_fixedPair` — fixed-pair `o(N)` ⇒ the leaf.
* `truncSum_div_tendsto_of_twoPointWeighted` — the bridge from the ratified per-pair statement.

Cashed as three Kátai-free reductions of C1:

| theorem | hypotheses |
|---|---|
| `conjC1_of_delange_pairwiseTwoPoint` | Delange + per-pair `TwoPointWeighted` |
| `conjC1_of_delange_twoPointElliott_weightDecouple` | Delange + `TwoPointElliott` + `WeightDecouple` |
| **`conjC1_of_delange_pairDecorr`** | Delange + `PairDecorr` |

The last one is `conjC1_of_delange_katai` (`SwingC1Weyl.lean`) **with the cited
`KataiOrthogonality` hypothesis deleted** — the Kátai/BSZ step is `katai_mean_sq`, a theorem of
laps 11–12 applied along the diagonal cutoff.  That is the sharpest unconditional reduction of C1
the development has.

**The correction this makes.**  `HANDOFF-…-SESSION-WRAP-2.md` records "per-pair decorrelation does
not imply the leaf (the budget is too small)".  False.  `tendsto_maxRecipSum_div_sq`
(`M(w)/L(w)² → ∞`) bounds the *trivial-bound strategy* from below, not the leaf.  Consequence: the
eleven laps 13–23 were producing a **uniform-in-`(p,q,w)`** saving `δ ≍ L(w)²/π(w)`, which is
sufficient and far from necessary — and *stronger* than the fixed-pair `o(1)` the diagonal route
consumes.  Those files stay in `src/` (sorry-free, the pricing is real) but are off-path.

## Where the route actually bottoms out

`pairDecorr_iff_twoPointWeighted` makes the fixed-pair crux a **natural-density two-point Elliott
correlation** for `ζ^ω` along `pm+1`, `qm+1`, twisted by `peelWeight`.  Tao 2016 gives exactly this
in *logarithmic* average; natural density is open.  So:

* the leaf is **no harder** than Elliott-2pt at natural density (`twoPointPairGramSmall_of_fixedPair`);
* it is **strictly weaker** — it inherits only `o(N·L(w N)²)` per pair, which is vacuous, so no
  per-pair information comes back out;
* and no route between the two is known: every uniform route is priced and refuted.

## Next session — start here

1. **The finite `K`-peel (elementary, and every route needs it).**  `omegaTail b n = O(log n)`, so
   iterating `phase_shiftPairTail_peel` `K = K(M) ≈ log_b log M` times leaves a remainder
   `O(b^{-K} log(pM)) = o(1)` uniformly in `m ≤ M`, giving
   `e(t(omegaTail(pm) − omegaTail(qm))) = e(Σ_{j=1}^{K}(t/b^j)(ω(pm+j) − ω(qm+j))) + o(1)`.
   Not yet in `src/`.
2. **Then the sieve/variance read.**  Prime factors in `(J, z]` with `K < J`: the events `p ∣ pm+j`
   are jointly CRT-independent across `j`, variance `≍ log log z → ∞`, small-prime phase mean
   `(log z/log J)^{-c}`, `c = Σ_j (1 − cos(2πt/b^j)) > 0`.  The obstruction is `ω_{>z}`: unbounded
   for `z = M^{o(1)}`, and `∈ {0,1}` for `z = √M` but then the small part is not CRT-tractable.
   Formalising either horn — small-prime part alone with a rate, or the implication naming the open
   two-point problem — is a successful lap.
3. **The 🟡 debt:** `DelangeMean` (Selberg–Delange for `ζ^ω`), the only *proven* input C1 cites.

`DIRECTION.md` → CURRENT DIRECTIVE is set for this branch and outranks this file.
`PENDING_WORK.md` top section carries the attack path.  `STATUS.md` header + axiom ledger refreshed.

**Rules honoured.**  `twoPointWeightedAvg_all` untouched.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs.  All new
code in `src/NormalNumbers/TwoPoint*.lean`; `src/` sorry count unchanged.

## Confidence at lap 24
- `twoPointWeightedAvg_all` TRUE: **90%** (the variance heuristic for the `K`-peel is strong).
- `PairDecorr` (fixed pair) TRUE: **92%**; provable with known techniques: **8%**.
- The C1 route is Elliott-equivalent in practice (no route strictly between): **75%**.
