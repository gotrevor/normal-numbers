# HANDOFF — entropy laps 64–65, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8988 jobs**.  Sorry-free; endpoints
`[propext, Classical.choice, Quot.sound]`.

## Lap 64 — `posAvg_eq_sum_coordAvg` (`G4EntropyGoodAtoms.lean`)

`posAvg m ℓ L w = (1/|A|)·Σ_α coordAvg m ℓ L α w`.  The per-coordinate averages of lap 61 mean
exactly the repo's already-controlled `posAvg`, so `card_good_ge` is a **refinement** of
`abs_posAvg_sub_le`, not a parallel statement.

## Lap 65 — the same-atom window geometry (`G4EntropyWindows.lean`)

Lap 60's open structural probe ("are maximal runs of `IsSampled` exactly single windows?") is
now settled on its same-atom half:

```
card_Idx_lt_freezeQ     |Idx| < freezeQ          (Bertrand: a prime in (|Idx|, 2|Idx|] divides it)
card_Idx_gridAt(_pos), kk_le_card_Idx            m_K ≤ |Idx|
P₀_le_sub_of_mem        distinct sample times differ by ≥ P₀
window_gap_same_atom    2·kIdx n α + m_K ≤ 2·kIdx n' α      for n < n' in P_K
```

**At a fixed atom the sampled windows are pairwise disjoint, with a margin.**  The chain:
`n' − n ≥ P₀ = Mprod·freezeQ ≥ d_α²·freezeQ`, and `n = t_α + d_α·kIdx`, so the orbit indices
differ by `≥ d_α·freezeQ ≥ freezeQ > |Idx| ≥ m_K`.

**Why it matters.**  Any overlap inside `IsSampled` is a genuine *cross-atom* collision; a
disjoint sub-family of windows can be chosen atom by atom with no loss at all.  That is the
missing geometric input for any construction that wants the read sequence to be literally a
concatenation of window contents (the form lap 52's counting bridge consumes), rather than a
set of positions with unknown multiplicity.

## Where the campaign stands

The route family "concatenation of *certified* granules" is closed (laps 61–63,
`certified_granule_exceeds_previous_scale`).  What laps 64–65 add is on the other side: the
tools are now sharp enough that the remaining question is purely geometric — the cross-atom
collision structure of `{2·kIdx(n,α) + p}`.

## Next bounded tests

1. **Cross-atom collisions.**  Can two atoms `α ≠ β` and sample times `n, n'` give
   `|2·kIdx(n,α) − 2·kIdx(n',β)| < m_K`?  `kIdx(n,α) = (n−t_α)/d_α`, so this asks whether
   `(n−t_α)/d_α` and `(n'−t_β)/d_β` can be within `m_K/2`.  With `d_α ≠ d_β` this is a
   divisor-ratio question about the grid, not about `G₄`.
2. If collisions are rare/absent, the band construction becomes available: read scale `i`'s
   windows only inside the band `[2X(K_{i−1}), 2X(K_i))` — a sub-collection of relative size
   `≈ 1`, hence certified — and the frequency along the band-end cutoffs would converge to
   `2^{−ℓ}`.  That is "normal along a subsequence of prefix lengths", the strongest statement
   `certified_granule_exceeds_previous_scale` still permits.
