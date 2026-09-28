# HANDOFF — entropy grind lap 31 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8967 jobs**; all in
`src/NormalNumbers/G4EntropyTiling.lean`, sorry-free, `#print axioms` clean.

## What was proved — the tiled headline, rendered on digits

`blockFreqT` (lap 30) became the load-bearing quantity, so it needed the same faithfulness
rendering `blockFreq` got in laps 24–25 — and it comes out **cleaner**, because the tiled blocks
are exactly aligned (`j < m_K/ℓ ⇒ (j+1)ℓ ≤ m_K`), so `blkAt_blockVal` applies with no `min`
correction:

| declaration | statement |
|---|---|
| `blockFreqT_eq_count` | `blockFreqT = #{(n,(α,j)) : block = w}/(\|P_K\|·\|Atom_K\|·⌊m_K/ℓ⌋)` |
| `blockFreqT_eq_digits` | the event is `blockVal (fract x) (2·kIdx(n,α) + jℓ) ℓ = w` — **aligned**, no `min` |
| **`tendsto_occursCountT_primeLambertFour`** | for every finite binary word `v`: the proportion of triples `(n,α,j)` at which `OccursAt 2 G₄ v (2·kIdx(n,α) + j\|v\|)` holds tends to `2^{−\|v\|}` |

`tendsto_blockFreqT_growing` was also relaxed to *eventual* hypotheses (`∀ᶠ i`, via
`squeeze_zero_norm'`), which is what a fixed word of length `ℓ ≤ kk i = 40000 + i` actually
satisfies.

So the expedition's final arithmetic statement now exists in its strongest and most literal
form simultaneously: disjoint tiling (no position double-counted), aligned positions
`2·kIdx(n,α) + j|v|`, the predicate `OccursAt 2 · v ·` shared with `isDisjunctive_two`, and the
quantitative rate `2√(200 log 2·|v|/√K)`.

## Next bounded test

The only remaining lever is `entropy_E1`'s deficit `δ_K = 50√K` (`ℓ = o(m_K/δ_K)` is now
exact).  Trace where the `50√K` is produced — grid resolution, counting slack, or the
`b₀`/`X` choice — and record which part is improvable without touching the barrier modules.
Then state `δ_K = K^{1/2−ε} ⇒ ℓ = o(K^{1/2+ε})` as an explicit corollary.

## Lean gotchas from this lap

- `squeeze_zero_norm'` is the eventual version of `squeeze_zero_norm`; pair it with
  `filter_upwards [h₁, h₂] with i hi₁ hi₂`.
- `Filter.Eventually.of_forall` is the current name for `Filter.eventually_of_forall`.
