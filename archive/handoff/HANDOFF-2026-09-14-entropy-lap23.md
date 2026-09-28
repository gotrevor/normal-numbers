# HANDOFF — entropy review lap 23 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  **HEAD** `3e284a3` (five commits this lap: `33dc377` altitude,
then `7626bc5`, `7efe929`, `93f7f7a`, `3e284a3`).  Working tree clean.
`lake build` green, **8965 jobs**.  Four new modules, all
sorry-free and `#print axioms`-clean (trust triple).  No pre-expedition file edited.
`isDisjunctive_four/two/base` and `primeSumAtBase_eq_primeLambertAtBase` re-checked clean.

## The review finding

Lap 15 filed brief §5 as answered *negatively*: "entropy rate → 1 controls no sampled
frequency, at any word length".  Its theorem `entropy_rate_not_control_bit` is true but is
about `highHalf m` — the frequency at a **fixed offset** inside the window.  Normality counts a
word's occurrences **averaged over the offsets**, and on lap 15's own witness (uniform on the
leading-bit-zero half) that averaged 1-frequency is `(m−1)/(2m) → 1/2`, i.e. correct.  Entropy
*does* control the averaged frequency.  §5's real answer is positive — and it was unproved.

`DIRECTION.md`'s CURRENT DIRECTIVE and `STATUS.md` were refreshed accordingly (this lap is the
altitude lap; the entropy override's §6 table, seven laps behind, is now recorded).

## What was proved

| declaration | statement |
|---|---|
| `FinLaw.gibbs` | `H₂ L ≤ −∑ p·log₂ q` for any sub-probability `q` dominating `supp L` |
| `FinLaw.H₂_le_sum_H₂_map` | jointly-injective coordinates ⇒ `H₂ L ≤ ∑ᵢ H₂ (L.map (f i))` |
| `klb_ge_sq` | `KL₂(p‖u) ≥ (p−u)²/2` (nats) — Hellinger route, **no calculus** |
| `sq_prob_sub_le_logb_card_sub_H₂` | `(L.prob B − \|B\|/\|Ω\|)²/(2 log 2) ≤ log₂\|Ω\| − H₂ L` |
| `blkAt_injective` | the `m/ℓ+1` aligned `ℓ`-blocks determine an `m`-bit window |
| `blkAt_blockVal` | block `j` of a window of `x` at `p` is the `ℓ`-window of `x` at `p+jℓ` |
| `sum_block_deficit_le` | `m·\|A\| − Δ ≤ H₂ L` ⇒ `∑ (ℓ − H₂ of a block) ≤ \|A\|ℓ + Δ` |
| `abs_prob_singleton_sub_le` | `\|M.prob {w} − 2^{−ℓ}\| ≤ √(2 log 2 (ℓ − H₂ M))` |
| `abs_avg_sub_le` | AM-GM averaging: `\|avg g − u\| ≤ S/(2tN) + t/2` for every `t > 0` |
| `abs_blockFreq_sub_le` | `\|blockFreq i ℓ G₄ w − 2^{−ℓ}\| ≤ log 2(ℓ+50√K)/(t(m_K/ℓ+1)) + t/2` |
| **`tendsto_blockFreq_primeLambertFour`** | **`blockFreq i ℓ G₄ w → 2^{−ℓ}` for every fixed word `w`** |

So the expedition's entropy theorem is not merely a richness statement: `entropy_E1` pins
**every finite binary word's frequency** among the `ℓ`-aligned blocks of the sampled windows of
`G₄ = ∑_p 1/(4^p − 1)`.  That is strictly stronger on this system than `isDisjunctive_two`,
which gives occurrence with no frequency.

## What is NOT claimed

Nothing about the normality of `G₄`.  The positions read here have density zero (laps 9–22),
and `not_T_E`'s witness `maskedReal G₄` has literally the same joint law at every scale, hence
literally these same block frequencies, and is not normal.

## Next bounded test

1. **Faithfulness rendering** (`PENDING_WORK` item 1): `blockFreq` is defined through
   `FinLaw.map`.  Prove `blockFreq_eq_count` (it equals `#{(n,α,j) : …}/(|P_K|·H_K·(m_K/ℓ+1))`,
   from `map_empirical_p`) and `blockFreq_eq_digits` (the block IS the `ℓ` digits of `G₄` at
   `2·kIdx(n,α)+jℓ`, from `blkAt_blockVal` + `ZSample_eq_blockVal`).  Until then the statement
   is honest but its reading depends on unfolding rather than a stated dictionary.
2. The same statement for arbitrary `x` with an `E0`-type hypothesis (the abstract
   `abs_avg_block_prob_sub_le` already is).

## Lean gotchas from this lap

- `Real.log_prod` takes the nonvanishing hypothesis as its **only** explicit argument
  (`Real.log_prod hne`), not `s`, `f`, `h`.
- `div_le_div_iff` is gone: use `div_le_div_iff₀`; `div_le_div_iff_of_pos_right` for `a/c ≤ b/c`.
- `Nat.pos_pow_of_pos` is gone: `Nat.pow_pos`.
- `div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c`.
- To turn `(K : ℝ)` into `√K·√K` without rewriting inside the `√`, `set S := Real.sqrt K`
  FIRST, then `rw [hKS]` only hits the bare cast.
- `field_simp` frequently closes the goal outright; a trailing `ring` then errors with
  "No goals to be solved".

## Lap-close state (2026-09-14, budget reached)

Working tree clean at `3e284a3`; nothing uncommitted.  The only `sorry`s anywhere in `src/` are
`PrimeLambertOscillation.phaseOscillation` and `MahlerDriftOne.exists_prime_nonresidue`, both
from other campaigns and both on this expedition's forbidden-drift list — untouched.

`DIRECTION.md`'s CURRENT DIRECTIVE (review lap 23) is the binding objective and its step 3 is
now DONE; the next grind lap should start at `PENDING_WORK.md`'s item 1, the faithfulness
rendering (`blockFreq_eq_count`, `blockFreq_eq_digits`).  That is a genuine obligation, not
polish: the headline currently reads correctly only through definitional unfolding of
`FinLaw.map` and `empirical`, and the brief (§8) asks the final arithmetic statement to be
tested against a literal rendering of the sample law.
