# HANDOFF twopoint — SESSION WRAP 3 (laps 24–27), 2026-09-24

Branch `wip/twopoint-avg`.  HEAD `e87b52f`.  Working tree **clean**; every lap committed green
(pre-commit runs `lake build`, 9285 jobs).  All new declarations `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).  `src/` sorry count unchanged from session start (46;
the three pre-existing off-campaign ones plus the ratified `twoPointWeightedAvg_all`).

## What this run did

Lap 24 was a review lap that found an eleven-lap drift and a false recorded fact; laps 25–27 cashed
the correction.  Net effect: **the C1 chain lost its cited Kátai/BSZ hypothesis, the small-prime
half of leaf (D) became a theorem, and the last dischargeable axiom (`DelangeMean`) was decomposed
into two named `Prop`s with the skeleton proved.**

### The chain now
**`conjC1_of_delange_multiElliott`** (`TwoPointKataiFree.lean`): `ConjC1` from **exactly two**
inputs and no others —

* `DelangeMean` — 🟡 PROVEN (Delange 1969 / Selberg–Delange); being chipped, see lap 27;
* `MultiElliott` — 🔴 OPEN (Elliott for `4K(R)` linear forms, `K(R) → ∞`, open even in log
  average), and *equivalent* to the leaf by `shiftCorrSmall_iff_multiElliott`, so not merely
  sufficient.

That 🔴 is honest: C1 is a conjecture in the source, so measuring its depth as one named open
problem is the deliverable, and it satisfies the kickoff's success criterion.

### New files (all in `src/`, imports added to `src/NormalNumbers.lean`)
| lap | file | content |
|---|---|---|
| 24 | `TwoPointGramDiagonal.lean` | **`exists_slow_cutoff`** (diagonalisation, no uniformity in `w`), `gramRatio_tendsto_of_fixedPair`, `twoPointPairGramSmall_of_fixedPair`, `truncSum_div_tendsto_of_twoPointWeighted`, **`conjC1_of_delange_pairDecorr`** (+ `…_pairwiseTwoPoint`, `…_twoPointElliott_weightDecouple`) |
| 25 | `TwoPointKataiFree.lean` | `conjC1_of_delange_decouple`, `…_largeDecay`, `…_shiftCorr`, **`conjC1_of_delange_multiElliott`** — every swing headline, Kátai-free |
| 26 | `TwoPointGrowingCut.lean` | `primeCut`, `four_pow_primeCut_sq_le`, `tendsto_period_over_R`, **`truncPair_fullMean_tendsto_zero`** (unconditional), `PairDecoupleGrowing`, `pairDecorr_of_pairDecoupleGrowing`, `conjC1_of_delange_pairDecoupleGrowing` |
| 27 | `TwoPointDelange.lean` | `delangeKernel`, **`sum_delangeKernel_divisors`**, **`sum_zpow_omega_eq`**, **`norm_delangeLocal_sq`**, `norm_delangeLocal_le`, **`prod_delangeLocal_tendsto_zero`**, `DelangeKernelMean`, `DelangeKernelTail`, **`delangeMean_of_kernel`** |

### The lap-24 correction (why the direction changed)
`PairGramSmallGrowing` quantifies the cutoff `w` **existentially**, so the leaf must hold at only
ONE cutoff per `N`.  At a fixed `w` the pair sum is a finite sum of `o(N)` terms over the positive
constant `L(w)² ≥ 1/4`, so the ratio already vanishes; a stair diagonalisation
(`exists_slow_cutoff`) then produces `w(N) → ∞` with `w(N)² ≤ N`.  Consequences:

* SESSION-WRAP-2's "per-pair decorrelation does not imply the leaf (the budget is too small)" is
  **FALSE**.  `tendsto_maxRecipSum_div_sq` (`M(w)/L(w)² → ∞`) bounds the *trivial-bound strategy*
  from below, not the leaf.
* Laps 15–23 were producing a **uniform-in-`(p,q,w)`** saving `δ ≍ L(w)²/π(w)` — sufficient, far
  from necessary, and *stronger* than the fixed-pair `o(1)` the diagonal route consumes.  Those
  files stay in `src/` (sorry-free, the pricing is real) but are **off-path**.

### Escape hatches closed (kernel- or argument-grounded; do NOT re-open)
| claim | why it is closed |
|---|---|
| uniform per-pair saving is needed | no — `exists_slow_cutoff` (lap 24) |
| `WeightDecouple` is an easier sub-problem | no — given `TwoPointElliott`, `E[X]E[Y] → 0` automatically, so `WeightDecouple ⟺ TwoPointWeighted`, the whole crux (`twoPointWeighted_of_split` + `weightDecouple_of_twoPointWeighted`) |
| the small/large-prime split can be tuned | no — `z = R^δ` bounds `ω_{>z} ≤ 1/δ` but the period `e^{R^δ} ≫ R`; `z ≈ θ log R` fixes the period but `ω_{>z} ≈ log R/log log R` |
| leaf (D) is an `L¹` statement | no — at `P ≍ log R` the remainder has `L¹` mass `≍ log log R → ∞`, so it is irreducibly a *cancellation* statement |
| the periodic model is still an obligation | no — `truncPair_fullMean_tendsto_zero` (lap 26) is unconditional at a growing cut |
| trivial / `ℓ¹` / `ℓ²`-fourth-moment / constant-`z` rotation | priced and refuted as strategies, laps 13–23 |

## Next session — start here

The route's depth is measured; the work now is to CHIP, not to re-price.

1. **`DelangeKernelTail z` for `‖z−1‖ < 1`** (highest value, 1–2 laps).  For `w = ‖z−1‖ < 1` and any
   `K`: `Σ_{n≤N} w^{ω(n)} ≤ N w^K + #{n ≤ N : ω(n) ≤ K}`, and Chebyshev on the in-kernel
   `turanKubilius` (`Σ_{n ≤ N}(kataiOmega w' n − L(w'))² ≤ 2 N L(w')`) gives
   `#{n≤N : ω(n) ≤ K} = o(N)` — choose the prime cut `w'` so `L(w') → ∞` slowly, and use
   `kataiOmega w' n ≤ omegaNat n` (the direction needed).
2. **`DelangeKernelMean z` for the same range** (2–4 laps): truncated multiplicative sum vs its
   Euler product (`prod_delangeLocal_tendsto_zero` is the product side, already a theorem).
   Wirsing/Levin–Fainleib comparison.
3. Together, 1+2 give **`DelangeMean t` unconditionally for `‖t‖_{ℝ/ℤ} < 1/6`** — a genuine partial
   discharge of the 🟡 axiom.  The remaining `t` (i.e. `‖z−1‖ ≥ 1`) need Halász / Selberg–Delange
   over `src/PNTPort/` (sorry-free quantitative PNT: `ZetaNoZerosOn1Line`, `ZetaZeroFree9`,
   `MediumPNT`, `MellinCalculus`, `ResidueCalcOnRectangles`, `Rectangle`).  Multi-lap contour work,
   but the prerequisites are in the tree.
4. `MultiElliott` / `PairDecoupleGrowing` are the 🔴 open leaf — narrow and cite, do not expect to
   clear.  Any new attack must be a *cancellation* mechanism, not a triangle inequality.

`DIRECTION.md` → CURRENT DIRECTIVE is set for this branch (lap-24 review lap) and OUTRANKS this
file.  `PENDING_WORK.md` top four sections carry the attack path and the refuted list.  `STATUS.md`
header, "What's happened" and the axiom ledger are refreshed to lap 27.

**Rules honoured throughout.**  `twoPointWeightedAvg_all` never deleted, renamed or weakened.  No
edits to `PairDecouple*.lean`, `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`,
`agent-mail/`, other KICKOFFs.  All new code in `src/NormalNumbers/TwoPoint*.lean`.

## Confidence at wrap
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%**.
- `ConjC1` is equivalent in practice to a named open problem (no route strictly between): **85%**.
- `DelangeKernelTail` for `‖z−1‖ < 1` closable in 1–2 laps: **70%**.
- Full `DelangeMean` from `PNTPort` within this run: **10%**.
