# HANDOFF twopoint lap 3 — the growing-`w` re-plumb is BUILT and axiom-clean

## Crux
`twoPointWeightedAvg_all` (`TwoPointBet.lean`), still `sorry`.  Kickoff item 2 (the real bet) is
now **done as a re-plumb**: C1 has an alternative route whose open leaf lives in the growing-
dilation regime.

## Advance this lap — `src/NormalNumbers/TwoPointKataiQuant.lean` (+ upgraded `TwoPointGrowing`)

**`KataiQuant`** — the quantitative Kátai/BSZ inequality, stated uniformly in `(w, N)`:

    ‖E_{n<N} f(n) a(n)‖²  ≤  C · ( 1/log log w  +  pairAvg a w N ),   2 ≤ w,  w² ≤ N,

for `|a| ≤ 1`, `|f| ≤ 1` multiplicative on coprimes.  Cited exactly as `KataiOrthogonalityAvg`
is.  Uniformity in `(w,N)` is the whole point: it may be run along a diagonal.

**`TwoPointWeightedAvgSlowGrowing b t`** — `∃ w → ∞ with (w N)² ≤ N` and
`twoPointAvgSum b t (w N) N → 0`.  The new open leaf.

Proved, all `sorry`-free, all `[propext, Classical.choice, Quot.sound]`:
- `avgShapeGrowingSlow_of_avgShape` — diagonal extraction, upgraded so the stair also dominates
  `(W k)²`; hence the cutoff is slow enough for `KataiQuant`.  So the ratified leaf implies the
  new one: **the re-plumb is a weakening, machine-certified.**
- `tendsto_fullMean_of_kataiQuant` — the inequality run along the diagonal.
- `shiftIndep_of_kataiQuant`, **`conjC1_of_delange_kataiQuant_twoPointSlowGrowing`** — the full
  swing: `ConjC1` from Delange + `KataiQuant` + the growing-`w` leaf.
- `conjC1_of_delange_kataiQuant_twoPointWeightedAvg` — the ratified headline still feeds it.

## Where the crux now sits
Two named obligations, both in `src/`, neither faked:
1. **`KataiQuant`** (a `Prop` hypothesis, not a `sorry`) — Cauchy–Schwarz + Turán–Kubilius.  No
   new mathematics; substantial Lean.  Ingredients: `PairDecoupleMertens.sum_inv_primesBelow_le_logLog`
   (needs the matching LOWER bound `Σ_{p≤w} 1/p ≫ log log w`), `PairDecoupleAvg` pair plumbing.
2. **`TwoPointWeightedAvgSlowGrowing`** — the leaf to attack.  This is where MRT-style averaging
   and the large sieve in the multiplier have room; a fixed finite pair set gave them none.

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%** (unchanged; lap 2's probe is the evidence).
- PROVABLE with known techniques: **25%** (up from 22%: the growing-`w` route now exists in
  Lean, so a proof of the growing leaf suffices and no longer needs the fixed-`w` order).

## Next (lap 4)
Prove `KataiQuant`'s Cauchy–Schwarz half in a new `src/NormalNumbers/TwoPointKataiProof.lean`:
`|E_{n<N} f(n)a(n)|² ≤ (Σ_{p≤w} 1/p)^{-2} · E_n |Σ_{p≤w} 1_{p|n} a(n) …|²` expanded into the
pair average plus the diagonal `p = q` term.  Leave the Turán–Kubilius input (the lower bound on
`Σ_{p≤w} 1/p` and the variance of `Σ_{p≤w} 1_{p|n}`) as a named sub-`sorry` IN `src/`.
