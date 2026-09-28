# HANDOFF twopoint lap 12 — the remaining leaf, unfolded arithmetically

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramArith.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

Lap 11 left `ConjC1` resting on Delange + `TwoPointPairGramSmall b t`, a statement about the
abstract Gram sum `kataiPairGram` of `a = ζ^{ω_tail}`.  This lap identifies that object:

* `csGram_kataiTrunc` — `csGram (kataiTrunc a N) (N+1) p q = Σ_{m ≤ min(⌊N/p⌋,⌊N/q⌋)} a(pm) conj a(qm)`
  (the two truncations intersect to the min-range; everything outside vanishes).
* `kataiPairGram_eq` — **`kataiPairGram (ζ^{ω_tail}) w N = twoPointGramSum b t w N`**, where

      twoPointGramSum b t w N
        = Σ_{p ≠ q ≤ w} ‖ Σ_{m ≤ min(⌊N/p⌋,⌊N/q⌋)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} · W_{p,q}(m) ‖ ,

  the same `twoPointFactor · peelWeight` integrand as the ratified leaf, on truncated ranges.
* `twoPointPairGramSmall_iff` and `conjC1_of_delange_twoPointGram` — C1 from Delange plus a leaf
  stated entirely in arithmetic terms, no abstract Gram object left in the statement.

So the open problem is now readable against the literature:
**`Σ_{p≠q≤w(N)} |Σ_{m ≤ min(N/p,N/q)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W(m)| = o(N·L(w(N))²)`**
with `w(N) → ∞`, `w(N)² ≤ N`.  Tao 2016 is the single-pair, `W ≡ 1`, log-density case.

## The size question this exposes (next lap's first probe)

Trivially `‖twoPointTruncSum b p q t N‖ ≤ min(N/p, N/q) ≤ N/max(p,q)`, so the trivial bound on
the pair sum is `N·Σ_{p≠q≤w} 1/max(p,q) = 2N·Σ_{p≤w} π(p)/p`, which is **much larger** than
`N·L(w)²`.  So the leaf needs genuine cancellation in essentially every pair, not just on
average — the saving required per pair is a factor `≍ L(w)²/(Σ_p π(p)/p)`.  Worth quantifying
in Lean next (a lemma `twoPointGramSum_trivial_le` plus the divergence of `Σ_p π(p)/p` relative
to `L(w)²`), because if the required saving is a fixed power of `N/max(p,q)` per pair, the leaf
is at Tao-2016 strength per pair and the equivalence-with-an-open-problem verdict is essentially
forced; if a `log`-power saving suffices on average, MRT-style entropy decrement has room.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `TwoPointPairGramSmall` / `twoPointGramSum` leaf TRUE: 85%; provable with known techniques: 15%.
