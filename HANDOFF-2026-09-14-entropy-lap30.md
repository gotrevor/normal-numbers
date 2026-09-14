# HANDOFF — entropy grind laps 29–30 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8967 jobs**.  New module
`src/NormalNumbers/G4EntropyTiling.lean`, sorry-free, `#print axioms` clean.

## The correction, and what replaced it

Lap 28 read its `√(ℓ²/m_K)` term as a *sampling* limit ("an `m`-bit window has only `m/ℓ`
blocks to average over") and concluded no deficit could ever beat `ℓ = o(√m_K)`.  **That was
wrong**, and the tell was available: at `δ = 0` the law is uniform, every block marginal is
exactly uniform, and the true error is `0` — while the lap-28 bound still gives `√(ℓ²/m)`.

The term came entirely from `sum_block_deficit_le`'s `|A|·ℓ` slack, i.e. from the *overlapping*
last coordinate of `blkCoord`.  Lap 29 removed the overlap; lap 30 re-ran the chain on it.

| declaration | statement |
|---|---|
| `remCoord`, `tileCoord` | the `m/ℓ` disjoint blocks **plus** the low `m % ℓ` bits |
| `tile_injective`, `tileCoord_injective` | they tile the window exactly |
| `H₂_map_rem_le` | the remainder carries `≤ m % ℓ` bits |
| `sum_block_deficit_tile_le` | `∑_{α, j<m/ℓ} (ℓ − H₂) ≤ Δ` — **zero slack** |
| `abs_avg_block_prob_tile_le` | the averaged word probability, numerator `2 log 2·Δ` (no `|A|ℓ`) |
| `blockFreqT` | the frequency over a genuine tiling: no position counted twice |
| **`abs_blockFreqT_sub_le_of_deficit`** | `\|blockFreqT − 2^{−ℓ}\| ≤ 2√(log 2·ℓδ/m_K)` for `ℓ ≤ m_K`, uniform in `w` and `x` |
| `abs_blockFreqT_sub_le_primeLambertFour` | at the implemented schedule: `≤ 2√(200 log 2·ℓ/√K)` |
| `tendsto_blockFreqT_growing` | `ℓ(K) = o(√K)` controlled, words free to vary |

Now the bound has the right degenerate behaviour (`δ → 0` ⇒ error `→ 0`) and the reading is
clean: **the controlled word length is exactly `ℓ = o(m_K/δ_K)`** — the deficit is the only
lever.  For the implemented schedule `δ_K = 50√K`, `m_K = K/4`, giving the same `o(√K)` as lap
26, but now attributed to `entropy_E1` alone rather than to the geometry.

## Next bounded test

(a) Record `δ_K = K^{1/2−ε} ⇒ ℓ = o(K^{1/2+ε})` as an explicit corollary.
(b) Trace the `50√K` in `entropy_E1` to its source (grid resolution vs. counting slack) and
record what part of it, if any, is improvable **without** touching the barrier modules.

## Lean gotchas from this lap

- `Fin.lastCases` needs the index in `castSucc`/`last` form; a raw `⟨j, h⟩` will not match the
  `@[simp]` lemmas.  Prove an index-form lemma (`tileCoord_of_lt`) and `rw` with that instead.
- `congr 1` on `L.map f = L.map g` leaves the *map* equality, not `f = g`; prove
  `have : f = g := by funext z; …` and `rw` it.
- `rw [h] at *` will rewrite the hypothesis you are about to use into a tautology — name the
  targets (`rw [hsplit] at hsub`).
- `√K · √K = 4·kk` inside a bigger product: `linear_combination (c) * hsq` closes what
  `nlinarith` will not.
