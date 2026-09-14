# HANDOFF — entropy grind lap 27 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8966 jobs**; all new work in
`src/NormalNumbers/G4EntropyRender.lean`, sorry-free, `#print axioms` clean.

## What was proved — §5's positive answer is about the SCHEME, not about `G₄`

| declaration | statement |
|---|---|
| `defRatio i x` | `1 − H₂(Z^x_K)/maxH_K`, the relative entropy deficit; `defRatio_nonneg` |
| `abs_blockFreq_sub_le_defRatio` | `\|blockFreq i ℓ x w − 2^{−ℓ}\| ≤ log2·ℓ/(t·(m_K/ℓ+1)) + log2·ℓ·defRatio/t + t/2`, every `t>0`, **every real `x`** |
| **`tendsto_blockFreq_of_E0`** | `E0 x → ∀ ℓ w, blockFreq i ℓ x w → 2^{−ℓ}` |
| `tendsto_blockFreq_primeLambertFour'` | `G₄` recovered as the instance, via `E0_primeLambertFour` |

The mathematical point: the deficit `Δ_i = defRatio·m_K·H_K` enters the bound only through
`Δ/(H_K·D)` with `D = m_K/ℓ+1`, and `m_K/D ≤ ℓ`, so the deficit's *contribution is at most
`log 2·ℓ·defRatio/t`* — no arithmetic input whatever.  Everything `G₄`-specific was in the
supply of the deficit (`entropy_E1`), and is now quarantined in one instance line.

Combined with lap 26, the full picture of what this sample's entropy controls:
`E0 x` ⇒ every fixed word's frequency; and for `x = G₄`, where the deficit is quantitatively
`50√K·H_K`, uniformly every word of length `o(√K)`.

## Next bounded test

Whether the `o(√K)` ceiling is an artifact of `entropy_E1`'s `50√K` deficit or of the
Hellinger conversion: state the conditional lemma "deficit `Δ_K = δ(K)·H_K` ⇒ word lengths up
to `ℓ = o(m_K/δ)` are controlled", which makes the trade-off explicit and turns the question
into a purely quantitative one about `entropy_E1`.

## Lean gotchas from this lap

- `Tendsto.atTop_mul_const` multiplies on the **right**; for `c * f x` use
  `Tendsto.const_mul_atTop`.
- `h1.add h2` into `Metric.tendsto_atTop` gives `dist … (0 + 0)`: strip with
  `simp only [Real.dist_eq, add_zero, sub_zero]`, not `rw [sub_zero]`.
- `div_le_div_iff` is gone → `div_le_div_iff₀` (already in the lap-23 list; it recurs).
- `(1 − H/(mC)) * (mC) = mC − H` is `sub_mul`/`one_mul`/`div_mul_cancel₀`, not `field_simp`,
  which leaves an unprovable-looking rearrangement.
