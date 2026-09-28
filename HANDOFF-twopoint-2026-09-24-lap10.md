# HANDOFF twopoint lap 10 — the Kátai/BSZ inequality is PROVED in kernel

## Crux
`twoPointWeightedAvg_all` still `sorry`.  But the hypothesis the whole averaged route rests on
is no longer cited: it is proved.

## Advance — `src/NormalNumbers/TwoPointKataiAssemble.lean` (no `sorry`, axiom-clean)

**`katai_master`**: for `‖a‖, ‖f‖ ≤ 1`, `f` multiplicative on coprimes, `2π(w) ≤ N`,

    L(w)·‖Σ_{n ≤ N} f(n)a(n)‖
      ≤  √( (N+1)·( N·L(w) + kataiPairGram a w N ) )  +  2N  +  N·√(2 L(w)) .

Assembled from the four obligations:
- `turanKubilius_abs` (lap 8) — the `ℓ¹` concentration of `ω_w`;
- `sum_kataiOmega_mul_complex` (lap 9) — the exact rearrangement;
- `kataiMultiplicativeError` (lap 9) — peeling `f(pm) = f(p)f(m)`, cost `≤ 2N`;
- `katai_cauchySchwarz` (lap 7) with `kataiDiagonal_le` — the diagonal is `Σ_p ⌊N/p⌋ ≤ N·L(w)`.

**This settles the run's central claim in kernel.**  Divide by `N·L(w)`: the pair term is divided
by `N·L(w)²`.  The `L(w)²` normalisation that laps 4–6 derived by hand — and that
`KataiOrthogonalityAvg`'s `π(w)²` normalisation contradicts — is now a machine-checked consequence
of the argument itself, not an assertion about what the literature proves.

## Honest note, recorded in the file header
The pair term `kataiPairGram` is the **truncated** Gram sum: correlations of `a(p·)` against
`a(q·)` over `m ≤ min(⌊N/p⌋, ⌊N/q⌋)`.  That is what the argument genuinely produces.  It is NOT
the full-range `pairSum` used in `KataiQuantSharp` / `TwoPointHonestChain`.  Bridging the two
(the truncated correlations are a sub-range of the full ones; going between them needs a
Cauchy–Schwarz or an Abel summation) is the remaining gap between `katai_master` and the `Prop`
`KataiQuantSharp`.

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%**; suffices for C1 via a correct Kátai step: **5%**.
- The run's finding (that `KataiOrthogonalityAvg` overstates BSZ/Kátai): **95%** — the inequality
  is now proved with its constants, so the only remaining doubt is whether some *different*
  argument gives the averaged form, which no source claims.
- `KataiQuantSharp` as stated (full-range `pairSum`) discharged: **55%** — the truncation bridge
  is real work and may want the `Prop` restated on `kataiPairGram` instead.

## Next (lap 11)
Two options, in order of value:
1. **Restate the honest chain on `kataiPairGram`.**  Rather than bridge truncated → full range,
   define `KataiQuantTrunc` directly from `katai_master` (it is a theorem, not a hypothesis!) and
   re-derive `ConjC1` from Delange + `katai_master` + a leaf phrased on the truncated Gram sum.
   That removes the last cited `Prop` from the chain entirely — C1 would then rest on Delange
   plus ONE open leaf, everything else kernel-checked.
2. The truncation bridge, if the leaf is more natural on full-range means.
Option 1 is strictly better: the leaf is open either way, and option 1 buys a fully
machine-checked Kátai step.
