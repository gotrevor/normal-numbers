# HANDOFF — entropy lap 60 (the sampled set has density ZERO), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8984 jobs**.  `G4EntropyEnum.lean` sorry-free.

## 0. The lap in one line

Lap 59's crude `density ≤ ¼` is sharpened to the true statement: the set of sampled positions has
**density zero**, so `sampleEnum` skips almost every digit of `G₄`.

## 1. What was proved

```
exists_cover_tail (I L)   positions < L sampled only by scales > I lie in finitely many scales
density_geom (i L)        #{scale-i sampled < L} ≤ ⅛·2^{−i}·L
card_tail_le (I L)        #{q < L : ∃ i > I, q ∈ sampledPosAt i} ≤ ⅛·2^{−I}·L
tendsto_density_isSampled #{q < L : IsSampled q} / L → 0
```

All `[propext, Classical.choice, Quot.sound]`.

## 2. The argument

Density is not summable over scales naively — an infinite union of positive-density sets can be
everything.  What makes it work is that **each `sampledPosAt i` is finite**.  Split at a cutoff
`I`: the head `⋃_{i ≤ I} sampledPosAt i` is one fixed finite set, contributing `C/L → 0`; the
tail is bounded uniformly by `⅛·2^{−I}·L` via the finite-cover trick plus
`density_le_pow_real` and a geometric sum.  Both halves are made smaller than `ε/2`, the head by
taking `L` large and the tail by taking `I` large.

## 3. What this settles

`isDisjunctive_enumReal` (lap 58) is a statement about a density-zero subsequence of `G₄`'s
binary digits — as far from a relabelling of `isDisjunctive_two` as it could be.

## 4. Next bounded test

Is `realOfDigits 2 enumDigits` **normal**?  `enumDigits` is not a block concatenation so lap 54's
`chunks_insufficient` does not transfer directly, but the same prefix problem reappears: `|S_i|`
explodes with `i` and the enumeration order is forced, so repetition — rung 3's fix — is
unavailable.  A frequency estimate is further blocked because the enumeration interleaves windows
from different scales, so a word may straddle two scales' windows.  The first concrete sub-probe
is whether maximal runs of `IsSampled` are exactly single windows.
