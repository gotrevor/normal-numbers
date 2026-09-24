# HANDOFF twopoint lap 25 — 2026-09-24

Branch `wip/twopoint-avg`.  Full build 🟢 green.  New file
`src/NormalNumbers/TwoPointKataiFree.lean`; all declarations trust-triple.
Read `HANDOFF-twopoint-2026-09-24-lap24.md` first (the review lap that unlocked this).

## The crux

`MultiElliott b p q t` — Elliott's conjecture for `4K(R)` linear forms with `K(R) → ∞`, open even
in logarithmic average — equivalently (`pairDecorr_iff_twoPointWeighted`) the **two**-point
weighted correlation `TwoPointWeighted b p q t` at natural density.  It is now the ONLY non-Delange
input to `ConjC1`.

## The advance

Lap 24's `conjC1_of_delange_pairDecorr` is pushed all the way down the repo's existing proof
direction, so every headline of the C1 swing loses its cited `KataiOrthogonality`:

| new theorem | supersedes | remaining hypotheses |
|---|---|---|
| `conjC1_of_delange_decouple` | `conjC1_of_delange_katai_decouple` | Delange + `PairDecouple` |
| `conjC1_of_delange_largeDecay` | — | Delange + `LargeDecay` |
| `conjC1_of_delange_shiftCorr` | — | Delange + `ShiftCorrSmall` |
| **`conjC1_of_delange_multiElliott`** | `conjC1_of_delange_katai_multiElliott` | Delange + `MultiElliott` |

**Ledger.**  `ConjC1` rests on exactly two inputs and no others: `DelangeMean` (🟡 PROVEN,
Selberg–Delange, project-scale to formalise) and `MultiElliott` (🔴 OPEN, and *equivalent* to the
leaf by `shiftCorrSmall_iff_multiElliott`, hence not merely sufficient).  The 🔴 is honest: C1 is a
conjecture in the source, so measuring its depth as one named open problem IS the deliverable.

## Two escape hatches closed this lap (record, do not re-open)

1. **`WeightDecouple` is not an easier sub-problem.**  Given `TwoPointElliott`, `E[X]E[Y] → 0`
   automatically, so `WeightDecouple ⟺ TwoPointWeighted` — the whole crux.  Both directions are
   already witnessed in `PairDecoupleTwoPoint.lean` (`twoPointWeighted_of_split`,
   `weightDecouple_of_twoPointWeighted`).
2. **The elementary small/large-prime split cannot be tuned.**  `z = R^δ` ⇒ `ω_{>z} ≤ 1/δ` bounded,
   but the periodic modulus `∏_{ℓ≤z}ℓ ≈ e^z ≫ R`; `z ≈ θ log R` ⇒ modulus `R^{O(θ)}` fine, but
   `ω_{>z} ≈ log R/log log R` unbounded.  Exactly leaf (D)'s tension, re-derived independently.
   The periodic side is already unconditional (`periodMean_pair_tendsto_zero`, `SwingC1Pair.lean`).

## Next session — start here

The route's depth is now measured; what is left is to CHIP, not to re-price.

1. **The 🟡 debt: `DelangeMean`.**  `E_{n≤N} e(t ω(n)) → 0` for `t = m/b`, `b ∤ m`.  This is the only
   *proven* input C1 still cites and it is the one axiom on the chain that can actually be
   discharged.  Selberg–Delange gives rate `(log N)^{Re e(t) − 1}`; `src/PNTPort/` has
   Wiener–Ikehara scaffolding.  **Highest value remaining.**
2. **Narrow `MultiElliott` toward the published case.**  `TwoPointElliott` (K = 1) is Tao 2016 in
   *logarithmic* average.  A lap that states the log-average form as a hypothesis and proves
   `ConjC1Log`-side consequences from it (`SwingC1Log.lean` has `ConjC1Log` and `castLawLog_one_iff`)
   would place the published theorem inside the development instead of beside it.
3. Do NOT re-attack: the uniform per-pair saving (lap-24 correction), the trivial/ℓ¹/ℓ²/constant-`z`
   rotation routes (laps 13–23), `WeightDecouple` as a cheap decoupling, or the small/large-prime
   tuning — all priced in kernel.

**Rules honoured.**  `twoPointWeightedAvg_all` untouched.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs.  All new
code in `src/NormalNumbers/TwoPoint*.lean`; `src/` sorry count unchanged.

## Confidence at lap 25
- `MultiElliott` TRUE: **93%**; provable with known techniques: **3%**.
- `ConjC1` is equivalent in practice to a named open problem (no route strictly between): **85%**.
- `DelangeMean` formalisable in this repo within ~10 laps: **45%**.
