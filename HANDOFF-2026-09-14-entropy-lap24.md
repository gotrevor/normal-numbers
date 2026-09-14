# HANDOFF — entropy grind lap 24 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  **HEAD** `8ec3adf`.  Tree clean, `lake build` green, **8966 jobs**.
One new module, `src/NormalNumbers/G4EntropyRender.lean`, sorry-free, `#print axioms` clean
(trust triple only).  No pre-expedition file edited; only `src/NormalNumbers.lean` gained the
import line.

## What was proved (PENDING_WORK item 1 — the faithfulness rendering — is DONE)

| declaration | statement |
|---|---|
| `blockVal_div_mod` | `blockVal y p (s+ℓ+t) / 2^t % 2^ℓ = blockVal y (p+s) ℓ` |
| `blkAt_blockVal_min` | for `ℓ ≤ m`, block `j` of the `m`-window of `y` at `p` is the `ℓ`-window at `p + min (jℓ) (m−ℓ)` |
| `blockFreq_eq_count` | `blockFreq i ℓ x w = #{(n,(α,j)) : blkAt … = w} / (\|P_K\|·\|Atom_K\|·(m_K/ℓ+1))` |
| `blockFreq_eq_digits` | that event **is** `blockVal (fract x) (2·kIdx(n,α) + min (jℓ) (m_K−ℓ)) ℓ = w` |
| **`tendsto_wordCount_primeLambertFour`** | the headline with **no `FinLaw` in the statement**: the digit-pattern count of `G₄` over the triple count → `2^{−ℓ}` |

The mathematical content beyond a restatement: `blkAt_blockVal` covered only the aligned range
`(j+1)ℓ ≤ m`, so the *last* of the `m/ℓ+1` coordinates — the one that exists precisely to cover
the `m % ℓ` leftover digits, and which overlaps its predecessor — had no digit meaning at all.
`blkAt_blockVal_min` gives it one (`min (jℓ) (m−ℓ)`), which is what let the whole average be
pushed onto digits rather than only `m/ℓ` of its terms.

## Bottleneck that moved

Before this lap the headline's *reading* depended on unfolding `FinLaw.map` and `empirical`; a
reader had to trust two definitions to see a frequency.  Now every quantity in
`tendsto_wordCount_primeLambertFour` is a cardinality of an explicitly described finite set of
digit positions of `G₄`.  This is the brief §8 test of the final arithmetic statement.

## Next bounded test

1. **Word-list rendering.**  `blockVal (fract x) p ℓ = (w : ℕ)` is still a *numeric* encoding of
   the word.  Prove `blockVal_eq_iff_digits : blockVal y p ℓ = wordVal L ↔ ∀ i < ℓ, digitOf 2 y
   (p+i) = L.getD i 0` (one direction is `blockVal_eq_of_occursAt`; the converse is the
   base-2 uniqueness of the expansion, i.e. `Nat.digits`-style induction on `blockVal_succ`).
   Then restate the headline over `OccursAt 2 x w` and the counted event becomes literally
   "the word `w` occurs at position `2·kIdx(n,α) + min(jℓ, m_K−ℓ)`" — the same predicate
   `isDisjunctive_two` uses, which makes the comparison with disjunctivity mechanical.
2. `blockFreq_eq_digits` / the limit for an arbitrary `x` carrying `E0` (the abstract
   `abs_avg_block_prob_sub_le` already is general; only `abs_blockFreq_sub_le` is `G₄`-specific).

## Lean gotchas from this lap

- `div_eq_div_iff` now takes `b ≠ 0`, `d ≠ 0` (not `0 < b`): pass `h.ne'`.
- `Fintype.card_pos` needs a `Nonempty` instance; for `A × Fin (n+1)` there is none by default —
  compute the card with `Fintype.card_prod`/`Fintype.card_fin` and use `positivity`.
- `refine Finset.filter_congr fun n _ => ?_` gets stuck on `DecidablePred ?m` if applied
  under a `congr 1` that has not yet fixed the predicates; `congr 2` down to the two `Finset`s
  first, then `filter_congr`.
- After `Fin.ext`, `rw` will not fire under `↑⟨_, _⟩`; `show` the `ℕ`-level goal first.
