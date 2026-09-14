# HANDOFF — entropy grind lap 25 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  **HEAD** `c24f66d`.  Tree clean, `lake build` green, **8966 jobs**.
All new declarations in `src/NormalNumbers/G4EntropyRender.lean`, sorry-free, `#print axioms`
clean (trust triple).  No pre-expedition file edited.

## What was proved

Lap 24 rendered the headline on *numeric* window values; this lap renders it on the **digit
predicate**.

| declaration | statement |
|---|---|
| `seqVal`, `seqVal_succ`, `seqVal_lt` | the value of a length-`m` binary string, its recursion and bound |
| `seqVal_inj` | **uniqueness of the binary encoding** — two length-`m` binary strings with equal value agree digit by digit.  (`digitOf_congr_of_blockVal` only compared two *reals*; a word is not a real, so this was genuinely missing.) |
| `wordVal`, `wordVal_lt` | the value of a word given as a `List ℕ`, `< 2^{\|w\|}` |
| `blockVal_eq_wordVal_iff` | `blockVal (fract y) p \|w\| = wordVal w ↔ OccursAt 2 y w p` |
| **`tendsto_occursCount_primeLambertFour`** | for every finite binary word `w`, the proportion of triples `(n,α,j)` at which **`w` occurs** in `G₄`'s binary expansion, at position `2·kIdx(n,α) + min (j\|w\|) (m_K − \|w\|)`, tends to `2^{−\|w\|}` |

## Bottleneck that moved

The expedition's frequency theorem and `isDisjunctive_two` are now stated over the *same*
predicate, `OccursAt 2 · w ·`.  The comparison — disjunctivity gives some occurrence, this gives
the correct *frequency* of occurrences on the sampled system — is mechanical rather than
interpretive, which is exactly what the §8 faithfulness test asks for.  Nothing about normality:
the positions counted have density zero (laps 9–22).

## Next bounded test

1. The general-`x` version: `abs_avg_block_prob_sub_le` is abstract already; only
   `abs_blockFreq_sub_le`'s deficit supply is `G₄`-specific.  Give the `E0`-hypothesis form.
2. **The quantitative edge** (E-T5 territory, to be recorded and not hidden): the deviation is
   `O(√(ℓ/√K))`, so `ℓ` may grow with `K` up to roughly `ℓ = o(√K)`.  State and prove the
   version with `ℓ = ℓ(K)`; that is the sharp form of "how much of `G₄`'s digit structure the
   sample sees", and it is the quantity any future positive branch would have to beat.

## Lean gotchas from this lap

- `OccursAt b x w n` is stated on `Int.fract x`; a `blockVal y …` bridge lemma must take
  `blockVal (Int.fract y) …` or the `rw` fails on the `mp` side.
- After `Finset.sum_congr`, goals appear as `(fun i => …) i = …`; `simp only` on such a beta
  redex reports "made no progress" while `rw` still works through it — don't insert the `simp`.
