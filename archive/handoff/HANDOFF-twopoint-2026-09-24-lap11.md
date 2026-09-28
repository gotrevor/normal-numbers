# HANDOFF twopoint lap 11 — the Kátai step stops being a hypothesis

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointGramChain.lean`, sorry-free,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` for both headline declarations.

## The crux, and this lap's advance on it

Crux: C1 for `G4_b` needs a Kátai/BSZ decoupling step plus a decorrelation leaf.  Through lap 10
the decoupling step was still carried as a *hypothesis* (`KataiQuantSharp`) even though
`katai_master` had been proved, because `katai_master` lives in the raw `Σ_{n ∈ Ioc 0 N}` /
`√((N+1)(NL+G))` shape and the swing consumes a mean-square bound.

This lap closes that gap.

* `katai_normalise` (plain reals, atom-clean): from `L·A·N ≤ √((N+1)(NL+G)) + 2N + N√(2L) + 2L`,
  with `L ≥ 1/2`, `L ≤ N`, `N ≥ 4`, derive `A ≤ 8√2·L^{-1/2} + √2·√(G/(NL²))`, hence
  `A² ≤ 256·(1/L + G/(NL²))`.
* `katai_mean_sq` — **the Kátai step in mean-square form, a THEOREM**:
  for `w ≥ 2`, `w² ≤ N`, unimodular `a`, unimodular multiplicative `f`,
  `‖E_{n<N} f(n)a(n)‖² ≤ 256·(1/L(w) + kataiPairGram a w N /(N·L(w)²))`.
  Supporting: `norm_sum_range_le` (the `range N` ↔ `Ioc 0 N` transfer, cost `2`),
  `card_primesLe_le` (`π(w) ≤ w−1`, giving `katai_master`'s `2π(w) ≤ N` from `w² ≤ N`),
  `kataiPrimeRecip_ge_half`, `kataiPrimeRecip_le_self`.
* `PairGramSmallGrowing` / `TwoPointPairGramSmall` — the single remaining open leaf.
* `tendsto_fullMean_of_gram`, `shiftIndep_of_pairGramSmall`, and
  **`conjC1_of_delange_pairGramSmall`**: `ConjC1` from Delange's theorem plus that one leaf.
  No `KataiQuantSharp`, no `KataiOrthogonalityAvg`, nothing cited-but-unproved in the Kátai step.

So C1 now rests on: Delange (genuine literature) + `TwoPointPairGramSmall` (open).  Every other
link is kernel-checked.

## Next attack (lap 12)

1. **Identify `kataiPairGram` arithmetically.**  Unfold `csGram (kataiTrunc a N) (N+1) p q` for
   `a = n ↦ phase(t·ω_tail(b, n))` into the two-point form
   `Σ_{m ≤ min(N/p, N/q)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W(m)` — i.e. the lemma matching
   `twoPointPairSum_eq` but for the truncated ranges.  That makes the leaf readable as the same
   arithmetic object the ratified `twoPointWeightedAvg_all` measures, with the honest
   normalisation `N·L(w)²`.
2. Then attack the leaf itself: the target is `o(N L(w)²)` for the Gram mass with `w = w(N) → ∞`.
   That is where an MRT/entropy-decrement or large-sieve-in-the-multiplier argument has room,
   because the dilation range grows with `N`.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88% (unchanged).
- `TwoPointPairGramSmall` TRUE: 85%; provable with known techniques: 15%.
- The lap-10 finding (that `KataiOrthogonalityAvg` overstates BSZ/Kátai): 95% (unchanged); this
  lap makes it moot for the honest chain, which no longer cites it.
