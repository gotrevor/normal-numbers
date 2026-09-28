# HANDOFF — entropy grind lap 35 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8970 jobs**.  New module
`src/NormalNumbers/G4EntropyOffset.lean`, **sorry-free**, `#print axioms` clean.  No
pre-expedition file edited; `G4EntropyTiling`/`G4EntropyRender` untouched (added to, never
changed).

## Why this thread

The directive's endpoint — met on laps 29–31 — counts a word among the **aligned** blocks of the
sampled window (positions `2k + jℓ`).  Normality counts a word at **every** position.  The
all-offsets statement is therefore strictly stronger and is the honest normality-shaped form of
§5's answer.  This lap builds the reduction; the rendering onto digit positions is next.

## The reduction, and why it is loss-free

Dropping the top `r` bits of each window is `lowTuple m r`.  The pair (top `r` bits, low `m−r`
bits) is injective, so generalized subadditivity gives

```
H₂_lowTuple_ge :  L.H₂ − |A|·r  ≤  (L.map (lowTuple m r)).H₂
```

The *maximum* entropy drops by exactly `|A|·r` too, so the truncated law carries the **same**
deficit `δ·|A|` on `m − r` bits.  And the aligned tiling of the truncated window is precisely
the offset-`r` tiling of the original.  Hence

```
abs_avg_block_prob_offset_le  (0 < ℓ, r + ℓ ≤ m, deficit δ) :
  | avg over (α, j < (m−r)/ℓ) of Pr[block at offset r + jℓ = w] − 2^{−ℓ} |
      ≤ 2 √(log 2 · ℓ δ / (m − r))
```

— every offset class obeys the tiled capacity bound, with `m` replaced by `m − r`.  For
`r < ℓ = o(√K)` and `m = m_K` this is the same bound to within `1 + o(1)`, so **no order is
lost by passing from the aligned blocks to all positions**.

Also new: `abs_avg_block_prob_tile_opt` — the abstract, `t`-optimized form of the tiled capacity
bound (`G4EntropyTiling`'s `abs_blockFreqT_sub_le_of_deficit` is that statement welded to the
schedule; this is the same argument for an arbitrary `FinLaw`, and is what the offset version
instantiates).

## Lean gotcha harvested (cost ~40 min, worth recording)

**Never let the elaborator unify two `FinLaw.map`s up to beta.**  `exact L.H₂_map_comp_injective f hg`
against a goal whose map argument is beta-equivalent but not syntactically equal times out at
`isDefEq` even at 10^6 heartbeats: comparing `L.map f₁` with `L.map f₂` forces whnf through the
`Finset.filter` in `map`'s mass function, hence through `Fintype.decidablePiFintype` on
`A → Fin (2^m)`.  The fix is the wrapper

```
FinLaw.H₂_map_congr_comp (L) (f) (hg : Injective g) (F) (hF : ∀ ω, F ω = g (f ω)) :
    (L.map F).H₂ = (L.map f).H₂
```

which takes the composition **pointwise**: `hF` is discharged by `fun z => rfl` (a cheap
beta/delta check on a single value, no `map` in sight), and the `rw [funext hF]` inside the
wrapper does the rest.  Same shape will be needed for any future `map`-level rewriting.

## Next bounded test

The position rendering.  For each `r < ℓ` the offset-`r` full blocks sit at window positions
`r + jℓ`, `j < (m−r)/ℓ`; as `(r, j)` ranges over all pairs these cover each window position
`p ≤ m − ℓ` exactly once (`r = p % ℓ`, `j = p / ℓ`, and `j < (m−r)/ℓ ⟺ p + ℓ ≤ m`).  Averaging
`abs_avg_block_prob_offset_le` over `r` therefore gives

```
| #{(n,α,p) : p + ℓ ≤ m_K, block of G₄ at 2·kIdx + p = w} / (|P_K|·|Atom_K|·(m_K−ℓ+1)) − 2^{−ℓ} |
    ≤ 2 √(log 2 · ℓ δ_K / (m_K − ℓ))
```

— every word at **every** position of the sampled window, i.e. the statement `isDisjunctive_two`
would need if the sampled positions had density one.  Two pieces: (1) the counting bijection
`(r,j) ↔ p` with the `(m−r)/ℓ` ranges (pure `Nat`), (2) the `blkAt`-level dictionary, which
`G4EntropyRender.blkAt_blockVal_min` already supplies for aligned blocks and which needs the
`lowCoord` composition identity `(z % 2^(m−r)) / 2^b % 2^ℓ = z / 2^b % 2^ℓ` for `b + ℓ ≤ m − r`.
