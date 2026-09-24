# HANDOFF twopoint lap 14 — the leaf's per-pair content, and its two-sided placement

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramMarkov.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

* `twoPointGramSum_eq_prod`, **`card_badPairs_mul_le`** — Markov on the pair sum:
  `#{(p,q) : p≠q ≤ w, ‖T_{p,q}(N)‖ ≥ ηN} · ηN ≤ twoPointGramSum b t w N`.
* **`card_badPairs_div_tendsto`** — under the leaf, for every fixed `η > 0`,
  `#{η-correlated pairs} / L(w N)² → 0`.

## The placement this settles (the kickoff's question 1, answered on the honest chain)

Together with lap 13 the leaf is now pinned on both sides:

* **Not implied by per-pair decorrelation** (lap 13, `tendsto_maxRecipSum_div_sq`): the trivial
  mass `N·M(w)` exceeds the Kátai budget `N·L(w)²` by an unbounded factor, so qualitative
  decorrelation of each of the `π(w)²` pairs is not enough — the leaf needs savings whose total
  beats `L(w)²`.
* **Does not imply per-pair decorrelation** (this lap, the remark in the file header): the
  individual-term bound a fixed pair inherits is `T_{p,q}(N) = o(N·L(w N)²)`, and `L(w N) → ∞`,
  so it is weaker than `o(N)` — vacuous.  No single-pair Elliott statement follows.

So the leaf is **not equivalent to natural-density two-point Elliott for a fixed pair** in either
direction.  It is an averaged statement over a dilation set growing with `N` — an MRT-shaped
problem (average over a growing family), not a Tao-2016-shaped one (one correlation, log
density).  This is the sharpest literature placement this run has reached, and it is a *negative*
answer to the kickoff's hoped-for "equivalence with a named open problem": no such equivalence
holds with the fixed-pair Elliott statement.  What remains open is whether the MRT method
(entropy decrement over the dilation set) can be pushed from shift-averages to dilation-averages.

## Next attack (lap 15)

The remaining route to a proof is the dilation-average analogue of MRT.  The first formalisable
brick, independent of the entropy machinery:

**`gram_le_boxNorm`** — bound `Σ_{p≠q≤w} ‖Σ_m a(pm) conj a(qm)‖` by an `ℓ²`/box-norm quantity
over the dilation set, i.e. Cauchy–Schwarz in the pair index followed by expanding the square:
`(Σ_{p≠q} ‖·‖)² ≤ π(w)² Σ_{p,q} ‖Σ_m a(pm) conj a(qm)‖²`, and the right side is a fourth-moment
of the dilation family, `Σ_{m,m'} |Σ_p a(pm) conj a(pm')|²`.  That fourth moment is where the
entropy-decrement/large-sieve input would enter, and it is a clean Lean target (the `csGram`
machinery of `TwoPointKataiCS.lean` already has the expansion lemma `sum_sq_superposition`).
Note the `π(w)²` cost of that Cauchy–Schwarz has to be paid back — worth checking, in Lean,
whether the budget survives it before investing in the fourth moment.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 8% (down: the MRT method
  averages over shifts, and no published argument averages over dilations in this way).
