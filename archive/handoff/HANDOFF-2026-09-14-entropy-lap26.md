# HANDOFF — entropy grind lap 26 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8966 jobs**; everything new in
`src/NormalNumbers/G4EntropyRender.lean`, sorry-free and `#print axioms` clean.

## What was proved — the E-T5 quantity, recorded not hidden

`abs_blockFreq_sub_le` carried a free parameter `t`.  Optimizing it (`t = √(2A)`, using
`m_K/ℓ + 1 ≥ K/(4ℓ)`) collapses the bound to a single closed form:

| declaration | statement |
|---|---|
| `rBlocks_lb` | `K/(4ℓ) ≤ m_K/ℓ + 1` |
| `abs_blockFreq_sub_le_sqrt` | `\|blockFreq i ℓ G₄ w − 2^{−ℓ}\| ≤ √(8 log 2 · (ℓ²/K + 50ℓ/√K))`, **uniformly in `w`** |
| **`tendsto_blockFreq_growing`** | for any `ℓ(K)` with `ℓ/√K → 0` and any words `w_K`, `blockFreq − 2^{−ℓ(K)} → 0` |

So the earlier theorem (fixed `ℓ`, fixed `w`) was far from the truth of the method: the sampled
system pins the frequency of **every** word of length up to `o(√K)`, inside windows of
`m_K = K/4` bits, with the word free to vary with the scale.  The directive's route trigger
E-T5 asked for exactly this rate to be stated rather than hidden behind a fixed `ℓ`.

The `√K` ceiling is the honest one for this route: the deficit `entropy_E1` supplies is
`50√K·H_K` bits against `m_K·H_K`, and the Hellinger/AM-GM step converts a per-block deficit
`ε` into a bias `√(2 log 2 ε)`; `ℓ ≍ √K` is where the per-block deficit stops being small
compared with `2^{−ℓ}`-scale detail.  A better exponent needs a better deficit, not a better
averaging step.

## Next bounded test

1. The general-`x` form (`E0` hypothesis in place of `G₄`); `abs_avg_block_prob_sub_le` is
   already abstract, so only the deficit supply needs abstracting.
2. Whether the `o(√K)` ceiling is an artifact of `entropy_E1`'s `50√K` deficit or of the
   Hellinger conversion — i.e. what deficit would be needed for `ℓ ≍ K^{1−ε}`, stated as an
   explicit conditional lemma.  That is the sharp question about how much of `G₄` this sample
   sees, and it is answerable without touching the barrier work.

## Lean gotchas from this lap

- `set S := √K with hS` does **not** fold `S` into hypotheses obtained afterwards; `rw [← hS]
  at h` them explicitly.
- Use the literal `(((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ)` rather than the `abbrev` `rBlocks i ℓ` in
  anything `linarith` must match: reducible abbreviations are still distinct atoms for it.
- `field_simp` closed three goals outright here; the habitual trailing `ring` then errors with
  "No goals to be solved" (twice) or leaves `1 + 1 = 2` for `norm_num`.
- `Filter.Tendsto.sqrt` exists — `simpa using h.sqrt` beats composing with
  `Real.continuous_sqrt.tendsto`, which leaves a `Function.comp` mismatch.
