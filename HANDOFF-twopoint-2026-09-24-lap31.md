# HANDOFF twopoint — lap 31: the weight-free surface is an EQUIVALENCE

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointDepthPeel.lean` (sorry-free,
trust-triple).  `DIRECTION.md` step 3: "A lap that PINS that obstruction as a theorem (an
implication `fixed-pair leaf ↔ named open statement` …) is a success."

## The advance
Lap 29 gave `pairDecorr_of_unweighted` (sufficiency).  The weight-removal bound
`norm_fullMean_sub_le` is symmetric, so it runs backwards too:

| result | content |
|---|---|
| `multiElliottGrowing_of_pairDecorr` | the crux forces the unweighted `2K(M)`-point means to vanish |
| **`pairDecorr_iff_unweighted`** | for ANY depth schedule `K` meeting the carry budget, `PairDecorr b t ↔ ∀ p≠q, MultiElliottGrowing b p q t K` |
| `pairDecorr_iff_unweighted_id` | the same at the certified schedule `K(M)=M`, hypothesis-free |

**What this pins.**  The fixed-pair crux is neither weaker nor stronger than the vanishing of

    E_{n<M} ∏_{k<K(M)} ζ_k^{ω(pn+1+k)} · conj(ζ_k^{ω(qn+1+k)}),   ζ_k = e(t/b^{k+1}),

an **unweighted, natural-density, growing-length Elliott correlation** for the completely
determined multiplicative-in-ω phase `ζ^ω` along the `2K(M)` linear forms `pn+1+k`, `qn+1+k`.
No `peelWeight` survives anywhere.  That is the named open problem: Elliott's conjecture for
`ζ^ω` in natural density (known only in log density and only for two points — Tao 2016 — or in
the shift-averaged form — MRT 2015; neither applies, since here the forms are *dilates* `pn`,
`qn`, not shifts, and the density is natural).

The equivalence means **no route lies strictly between** the C1 leaf and that problem: any proof
of C1 through this branch proves the correlation statement, and conversely.  Together with lap 25's
`shiftCorrSmall_iff_multiElliott` the route's depth is now measured at both the weighted and the
weight-free surface, and they agree.

## Run to date
* lap 28 `92ede26` — `DelangeKernelTail` unconditional for `‖z−1‖<1`.
* lap 29 `ab283df` — peel weight drops at growing depth.
* lap 30 `2d4d2c3` — exact CRT counts for the `2K` forms (`card_hit_eq`).
* lap 31 (this) — the reduction upgraded to an equivalence.

## Next
Still open and worth a lap: split `MultiElliottGrowing` at a prime cut `z` into a small-prime
factor (provably `→ 0` by `card_hit_eq` + Mertens) and a named large-prime remainder, giving the
`2K`-form analogue of lap 26's `truncPair_fullMean_tendsto_zero`.  Lap 30 already records why this
cannot close the leaf by a triangle inequality (used mass `≍ 2K log(log z/log K)` diverges), so the
value is in naming the remainder precisely, not in hoping it is small.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- The C1 route is equivalent to a named open problem, with a machine-checked equivalence at the
  weight-free surface: **now a theorem in `src/`, not an estimate.**
