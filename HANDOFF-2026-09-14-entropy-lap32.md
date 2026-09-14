# HANDOFF — entropy grind lap 32 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8967 jobs**, sorry-free additions,
`#print axioms` clean.

## 1. Proved: the capacity limit in its final form

`tendsto_blockFreqT_of_capacity` — words `w_K`, reals `x_K` **and** deficits `δ_K` all free to
vary; the single hypothesis is `ℓ_K·δ_K/m_K → 0`, i.e. exactly `ℓ_K = o(m_K/δ_K)`.  No second
obstruction (contrast `tendsto_blockFreq_of_capacity`, whose hypothesis still carries the
spurious `ℓ²/m_K` from the overlapping block).  Instantiating: `δ_K = 50√K` (the implemented
schedule) gives `o(√K)`; a hypothetical `δ_K = K^{1/2−ε}` would give `o(K^{1/2+ε})`.

## 2. Traced: where `entropy_E1`'s `50√K` actually comes from

Chain, read out of the source this lap:

```
entropy_E1  (δ_K = 200/√K, i.e. deficit 50√K·H_K)
  └ entropy_cover_bound admits any δ ≥ (92√K + 51)/(K log 2) ≍ 133/√K
      └ 92√K = 4·23√K, from Lg = rDim·(log 2 + 23√K)
          └ log_det_one_add_tensorGram_le' (G4Tensor:260)
              └ log_det_one_add_tensorGram_le:  s^K(log 2 + √(K μ₂ + K(K−1) μ₁²))
                 with μ₂ ≤ 520, μ₁ = log(s+1)/s at s = K²  ⇒  √(520K + 4) ≤ 23√K
```

**The `√K` is a genuine fluctuation, not accounting slack.**  It is `√(K μ₂)`: the log of a
tensor eigenvalue `Λ_j = ∏_i λ_{j_i}` is a sum of `K` iid-like terms, so `|log Λ|` is typically
`≍ σ√K` — a CLT-scale spread, and Cauchy–Schwarz
(`sum_abs_le_sqrt_card_mul_sum_sq`) is tight up to a constant for such a sum.

The one visible looseness is `log(1 + Λ) ≤ log 2 + |log Λ|`, which is wasteful for `Λ ≪ 1`
(there `log(1+Λ) ≈ Λ`, not `|log Λ|`).  Refining it to `log 2 + (log Λ)^+` does **not** help at
the order: the log-spectrum here is essentially centred (`μ₁ = log(K²+1)/K² → 0`, so the
per-tensor mean `K μ₁ ≍ 2 log K / K → 0`), so about half the tensor eigenvalues exceed `1` and
their `(log Λ)^+` is still of size `σ√K`.

**Verdict for the record:** `δ_K ≍ √K` is intrinsic to the *spectral/cover* route as built.
Beating it needs a different estimate of `det(1 + T_{K²}^{⊗K})` — e.g. exploiting cancellation
across `j` rather than bounding each `|log Λ_j|` — not a tightening of any constant.  So the
expedition's word-length ceiling `ℓ = o(√K)` stands, and is now attributed precisely.

## Next bounded test

The trace above gives the only remaining lever a name: `∑_j log(1 + Λ_j)` with `Λ_j` the tensor
spectrum.  A bounded probe: prove `∑_j log(1+Λ_j) ≤ s^K log 2 + ∑_j (log Λ_j)^+` and compute
`∑_j (log Λ_j)^+` exactly for `K = 1, 2` at small `s`, to see whether the constant (not the
order) moves.  If the order does not move — the expected outcome — record `δ_K ≍ √K` as a
*wall of this route* in `PENDING_WORK.md` and close §5's quantitative thread.
