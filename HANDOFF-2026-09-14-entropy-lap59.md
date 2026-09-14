# HANDOFF — entropy lap 59 (non-vacuity of the subsequence headline), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8984 jobs**.  `G4EntropyEnum.lean` sorry-free.

## 0. The lap in one line

A faithfulness audit of laps 56–58 found a genuine gap — nothing controlled the **union** of the
sampled sets over all scales — and closed it: that union has density at most `¼`.

## 1. The gap

`density_le_pow_real` (lap-era `G4EntropyWall`) bounds the density of **one** scale's sampled
positions by `⅛(2/K⁶)^K`.  But `IsSampledPos`/`IsSampled` quantifies over *all* scales, and every
scale contributes positions near `0`, with `|Atom_i| = (K²+1)^{K}` atoms each.  Had the union been
cofinite, `sampleEnum` would be the identity map, `enumDigits` would be `G₄`'s own digits, and
`isDisjunctive_enumReal` would be a restatement of the already-known `isDisjunctive_two` —
true, but worthless.  Nothing proved ruled that out.

## 2. What was proved

```
isSampledPos_iff_isSampled   IsSampledPos q ↔ IsSampled q     (the new predicate is the repo's)
exists_cover (L)             positions < L are sampled by scales from a FINITE range
card_filter_isSampled_le (L) (#{q < L : IsSampled q} : ℝ) ≤ L / 4
```

All `[propext, Classical.choice, Quot.sound]`.

The finite-cover step is what makes an infinite union of densities summable at all: the finset of
sampled positions below `L` is finite, so each element's witness scale is bounded, and the count
is dominated by `∑_{i ≤ I} ⅛(2/K_i⁶)^{K_i}·L ≤ ⅛·2·L`.  The per-scale bound goes through
`(2/K⁶)^K ≤ 2^{−K} ≤ 2^{−i}` and `sum_geometric_two_le`.

## 3. What this establishes

`sampleEnum` omits at least three quarters of `G₄`'s digits, so laps 56–58 are a statement about
a genuinely sparse subsequence, not a relabelling of `G₄`.

## 4. Next bounded test

Is `realOfDigits 2 enumDigits` **normal**?  Lap 54 refutes the chunking route to normality along a
strictly increasing map; nothing proved says it is impossible, and `enumDigits` is not a block
concatenation, so the lap-54 argument does not apply to it directly.  The obstacle to even
stating a frequency estimate is that the enumeration interleaves windows from different scales,
so a word may straddle two scales' windows.
