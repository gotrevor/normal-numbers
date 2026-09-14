# HANDOFF — entropy session wrap, laps 24–33 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  **HEAD** `7b4f116`.  Working tree **clean**, nothing uncommitted.
`lake build` green, **8968 jobs**.  Every declaration added this session is sorry-free and
`#print axioms`-clean (trust triple only).  No pre-expedition file edited; `entropy_E0`,
`entropy_E1` and all lap 8–22 modules untouched; `isDisjunctive_four/two/base` and
`primeSumAtBase_eq_primeLambertAtBase` unchanged.

## Objective state (DIRECTION's CURRENT DIRECTIVE, review lap 23)

The directive's 🎯 objective — "turn `entropy_E1` into a frequency theorem about `G₄`'s binary
digits" — is **met, and then sharpened past the form it asked for**:

```
tendsto_occursCountT_primeLambertFour  (G4EntropyTiling.lean)
  for every finite binary word v:
    #{(n,α,j) : OccursAt 2 G₄ v (2·kIdx(n,α) + j|v|)} / (|P_K|·|Atom_K|·⌊m_K/|v|⌋) → 2^{−|v|}
```

with `OccursAt 2 · v ·` the very predicate behind `isDisjunctive_two`, positions **aligned and
disjoint**, and no `FinLaw` anywhere in the statement.

## The three new modules

| module | content |
|---|---|
| `G4EntropyRender.lean` | faithfulness rendering (laps 24–25): `blkAt_blockVal_min`, `blockFreq_eq_count/_eq_digits`, `seqVal_inj`, `blockVal_eq_wordVal_iff`, `tendsto_occursCount_primeLambertFour`; the general theory (laps 26–28): `abs_blockFreq_sub_le_sqrt`, `tendsto_blockFreq_growing`, `defRatio`, **`tendsto_blockFreq_of_E0`**, `abs_blockFreq_sub_le_of_deficit`, `tendsto_blockFreq_of_capacity` |
| `G4EntropyTiling.lean` | the disjoint tiling (laps 29–32): `remCoord`, `tileCoord`, `tileCoord_injective`, `H₂_map_rem_le`, **`sum_block_deficit_tile_le`** (zero slack), `abs_avg_block_prob_tile_le`, `blockFreqT`, **`abs_blockFreqT_sub_le_of_deficit`** (`≤ 2√(log 2·ℓδ/m_K)`), `blockFreqT_eq_count/_eq_digits`, `tendsto_occursCountT_primeLambertFour`, `tendsto_blockFreqT_growing`, `tendsto_blockFreqT_of_capacity` |
| `G4EntropySpectral.lean` | the deficit probe (lap 33): `log_one_add_le_log_two_add_posPart`, `sum_log_tensorLam`, `log_det_one_add_tensorGram_le_pos`, **`log_det_one_add_tensorGram_le_twelve`** |

## The four findings of the session

1. **§5's positive answer is about the scheme, not `G₄`** (`tendsto_blockFreq_of_E0`): `E0 x`
   alone pins every fixed word's sampled frequency, for every real `x`.  All `G₄`-specific
   content is the *supply* of the deficit.
2. **The controlled word length is exactly `ℓ = o(m_K/δ_K)`** (`tendsto_blockFreqT_of_capacity`)
   — words, reals and deficits all free to vary with the scale.
3. **Lap 28's "sampling limit" was wrong and is corrected**: the `√(ℓ²/m)` term came from the
   *overlapping* last block of `blkCoord`, not from geometry.  The tiling (`remCoord` +
   `m/ℓ` disjoint blocks, alphabet budget `m` on the nose) removes it, and the bound then has
   the right degenerate behaviour (`δ → 0` ⇒ error `→ 0`).
4. **`δ_K ≍ √K` is a wall of the spectral/cover route**: traced `entropy_E1`'s `50√K` through
   `entropy_cover_bound`'s floor to `log_det_one_add_tensorGram_le'`, and the `(log Λ)^+`
   refinement (lap 33) halves the constant (`23√K → 12√K`, so `δ ≈ 25√K`) while leaving the
   order untouched — the log-spectrum is centred, so the `√K` is a genuine CLT-scale spread.

## Next steps for a fresh session

1. Nothing in §5 is open.  Optional tidy: state the `OccursAt` corollary of
   `blockFreqT_eq_digits` for a general `x` under `E0` (the digit rendering already is general;
   only the `G₄` instance is spelled out).
2. If the campaign is to continue past §5, the only order-level lever named by this session is
   **cancellation across `j` in `∑_j log(1 + Λ_j)`** — a different estimate of
   `det(1 + T_{K²}^{⊗K})`, not a tighter constant.  That is the single sentence a next
   directive would need to decide on.
3. The brief §8 outcome conditions (E0/E1 settled; `T_E` refuted with a witness meeting its
   exact premise; §5 answered) are all met; the run's remaining scope is a judgement call for
   an altitude lap, which owns `DIRECTION.md`.

## Lean gotchas harvested this session (all verified)

- `div_le_div_iff` → `div_le_div_iff₀`; `Nat.pos_pow_of_pos` → `Nat.pow_pos`.
- `Tendsto.atTop_mul_const` multiplies on the right; use `Tendsto.const_mul_atTop` for `c * f`.
- `squeeze_zero_norm'` is the eventual version; `Filter.Eventually.of_forall` the current name.
- `Filter.Tendsto.sqrt` exists — better than composing with `Real.continuous_sqrt.tendsto`.
- `set S := √K with hS` does not fold into later hypotheses: `rw [← hS] at h`.
- `Fin.lastCases` needs `castSucc`/`last` form; prove an index-form lemma and `rw` with it.
- `congr 1` on `L.map f = L.map g` leaves the map equality; prove `f = g` by `funext` and `rw`.
- `rw [h] at *` can rewrite the hypothesis you were about to use into a tautology.
- `field_simp` closes many of these goals outright; a trailing `ring` then errors "No goals".
- `linear_combination c * h` closes product-substitution goals `nlinarith` refuses.
