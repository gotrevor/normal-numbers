# HANDOFF — entropy laps 66–81, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8992 jobs**.  Every new module sorry-free; every
endpoint `[propext, Classical.choice, Quot.sound]`.

## The result

> **`Sched.tendsto_bandRead_freq`** — for every finite binary word `v`,
> `winCount (bandDig G₄) v (bT (i+1)) / bT (i+1) → 2^{−|v|}`,
> where `bandDig G₄ j = digitOf 2 (fract G₄) (bandPos j)` and
> **`Sched.bandPos_strictMono`** — `bandPos` is strictly monotone.

`G₄`'s binary digits, read along a **strictly increasing** position sequence, have the correct
frequency of every finite binary word along the subsequence of prefix lengths `bT (i+1)`.

This is exactly the strongest statement the lap-63 wall permits: the full limit over *all*
prefix lengths is normality, and `certified_granule_exceeds_previous_scale` forbids it on this
mechanism.  Previously the repo had *either* normality with a non-injective position map
(`isNormal_realOfDigits_samplePos`, lap 52) *or* a strictly increasing map with only
disjunctivity (`isDisjunctive_enumReal`, laps 56–60).  This is between them, and new.

## How it was built (laps 66–81)

| lap | module | content |
|---|---|---|
| 66 | `G4EntropyGoodAtoms` | `exists_good_coord(_deficit)` — one coordinate good for every word of every length |
| 67–68 | `G4EntropyAtomFreq` | `coordAvg_eq_count/_digits`, `goodAtom`, `tendsto_goodAtom_occursCount` — **one atom per scale suffices**; the average over `(K²+1)^K` atoms is not needed |
| 69–71 | `G4EntropyBand` | `band_gap(_strong)`, `bandTop/bandLo/bandS`, `card_bandS_ge'` — the scales can be read in **ordered bands**, dropping at most half the sample |
| 73–75 | `G4EntropyBandFreq` | `bandLaw`, `H₂_bandLaw_ge`, `abs_posAvg_bandLaw_le`, `tendsto_band_occursCount` — the band-restricted atom is **still certified** (`σ ≥ ½` costs a factor 2) |
| 76–81 | `G4EntropyBandSeq` | `bnth/bpos/bL/bT/bandPos`, `bandPos_strictMono`, the dictionary, `band_winCount_bounds`, `bL_step'`, `bT_kk_le`, `tendsto_bandRead_freq` |

The three structural facts that make the read strictly increasing:
1. inside a window the positions are consecutive;
2. consecutive windows of one band are a **full window apart** (`window_gap_same_atom`, lap 65 —
   `P₀ = Mprod·freezeQ ≥ d²·freezeQ` and `freezeQ > |Idx| ≥ m_K`);
3. band `i` lies entirely below band `i+1`'s floor (`pos_lt_bandTop`, `band_gap`).

And the two quantitative ones that make the limit work:
* `bT_kk_le`: `bT i · m_i ≤ 4·bL i` — the history is a `4/m_i` fraction of the current band, a
  bound that *improves* with the scale, so the per-window seam corrections (`≤ |v|` each) vanish.
* `abs_posAvg_bandLaw_le`: the band's own capture bound `2√(2000 log2·|v|/√K) → 0`.

## What is still not available, and why

Normality of the band read.  At a cutoff *inside* band `i` the accumulated content is an
uncontrolled prefix of band `i`, and `certified_granule_exceeds_previous_scale` (lap 63) says any
non-vacuously certified sub-collection of scale `i+1` already reads more digits than scale `i`
produced in total — so no choice of granules makes the prefix frequencies converge.

## Next bounded tests

1. Package the band read as a real: `ProperDigits` for `bandDig` (via
   `tendsto_bandRead_freq` applied to `0^{N+1}`, as in lap 58), then
   `realOfDigits 2 (bandDig G₄)` and its disjunctivity/irrationality.
2. Whether the cutoff sequence can be thickened: the limit holds along `bT (i+1)`; does it hold
   along `bT i + c·bL i` for each fixed `c ∈ (0,1]`?  That asks for the certification of a
   *fixed-fraction* prefix of one band — `σ = c` costs `(δ+1)/c`, which is fine for fixed `c`.
   If so, the exceptional set of cutoffs is only the `o(1)`-fraction near each band's start.
