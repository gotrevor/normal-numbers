# HANDOFF twopoint lap 26 — 2026-09-24

Branch `wip/twopoint-avg`.  Full build 🟢 green (9284 jobs).  New file
`src/NormalNumbers/TwoPointGrowingCut.lean`; all declarations trust-triple.

## The crux

Leaf (D): natural density versus one full primorial period, for
`E_{n<R} e(t(θ_{pn} − θ_{qn}))`, `p ≠ q` fixed primes.  Equivalently (`TwoPointKataiFree.lean`)
`MultiElliott`.  It is the only non-Delange input to `ConjC1`.

## The advance — an UNCONDITIONAL theorem about the crux object

The repo had the periodic-model half only at a FIXED cut `P`, where the density mean converges to
the *nonzero* constant `Π_{r≤P} pairLocalFactor`.  Letting the cut grow slowly fixes that:

    primeCut R = ⌊log₄ R⌋ / 2,   so  primorialLe (primeCut R) ≤ 4^{primeCut R} ≤ √R

(`primorial_le_four_pow`; `four_pow_primeCut_sq_le`).  Then, with NO hypothesis,

**`truncPair_fullMean_tendsto_zero`** :
`E_{n<R} e(t(θ^{(primeCut R)}_{pn} − θ^{(primeCut R)}_{qn})) → 0`
for every `b ≥ 2`, `t ≠ 0` and distinct primes `p ≠ q`.

Mechanism: period mean `= Π_{r ≤ primeCut R} pairLocalFactor → 0` (Mertens plus the separation
bound, `periodMean_pair_tendsto_zero`), and the Cesàro/period defect is `≤ 2Q/R ≤ 2/Q → 0`
(`norm_fullMean_sub_periodMean_le`, `tendsto_period_over_R`).  This is the honest natural-density
mean — the small-prime half of leaf (D) is now a theorem, not a model.

**What is left, named and minimal.**  `PairDecoupleGrowing b p q t` — the defect between the full
pair mean and its `primeCut R` truncation — with

* `pairDecorr_of_pairDecoupleGrowing` : it alone gives `PairDecorr`;
* `conjC1_of_delange_pairDecoupleGrowing` : Delange + it give `ConjC1`.

The model term is no longer an obligation anywhere in the chain.

## Recorded obstruction (do not retry)

`PairDecoupleGrowing` is irreducibly a **cancellation** statement.  At `P ≍ log R` the large-prime
remainder has `E_{n<R}|pairRemainder| ≍ log(log R / log P) ≍ log log R → ∞`, so no triangle
inequality can close it.  Pushing `P` up to `R^δ` makes the remainder bounded (`ω_{>z} ≤ 1/δ`) but
the period `e^{R^δ}` then dwarfs `R`.  That two-sided squeeze IS the parity-type obstruction, and it
is why the shift-cut route buys an `o(1)` tail at the price of a `4K`-point correlation
(`MultiElliott`).

## Next session — start here

1. **`DelangeMean`** — the only *proven* input left on the chain (🟡): `E_{n≤N} e(t ω(n)) → 0` for
   `t = m/b`, `b ∤ m`.  Equivalently, since `e(t·)` has finite order `d`, the equidistribution of
   `ω(n) mod d`.  This is PNT-strength (Landau: `Σ(−1)^{Ω(n)} = o(x) ⟺ PNT`) plus a Selberg–Delange
   Tauberian step for the branch point `ζ(s)^z`.  `src/PNTPort/` has a sorry-free Wiener–Ikehara
   port (`Wiener.lean`), `ZetaBounds.lean`, `MellinCalculus.lean`, `Rectangle.lean`,
   `ResidueCalcOnRectangles.lean`, `MediumPNT.lean`.  **Scope it first**: does `PNTPort` give
   non-vanishing of `ζ` on `Re s = 1` and a usable contour framework?  If yes, decompose
   Selberg–Delange into named sub-goals in `src/`; if no, name the missing prerequisite.
2. Do NOT re-attack: the uniform per-pair saving (lap 24), trivial/ℓ¹/ℓ²/constant-`z` rotation
   (laps 13–23), `WeightDecouple` as a cheap decoupling (lap 25), the small/large-prime tuning
   (laps 25–26), or the model term (now a theorem).

**Rules honoured.**  `twoPointWeightedAvg_all` untouched.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs.  All new
code in `src/NormalNumbers/TwoPoint*.lean`; `src/` sorry count unchanged.

## Confidence at lap 26
- `PairDecoupleGrowing` TRUE: **92%**; provable with known techniques: **3%**.
- `DelangeMean` reachable from the existing `PNTPort` within ~15 laps: **35%**.
