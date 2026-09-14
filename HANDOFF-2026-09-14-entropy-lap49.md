# HANDOFF — entropy lap 49 (joint richness, abstract layer), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8979 jobs**.  `src/` sorry-free.  No `axiom`.

## 0. The lap in one line

The successor target the lap-48 handoff identified — a **joint richness** endpoint, the one
functional of the joint law that lap 48's refutation does *not* touch — is proved at the
abstract layer.

## 1. What was proved — `G4EntropyJointRich.lean` (new module)

```
suppOf M / suppOf_nonempty
two_pow_H₂_le_card_support   2^{H₂ M} ≤ |supp M|          (entropy bounds support below)
tupleOf m t blk b            the t windows of a block, UNtruncated
leftTuple / richFam / richFam_injective
H₂_map_tupleOf_le            H₂(tuple_b) ≤ t·m
H₂_map_leftTuple_le          a missed atom costs ≤ m, a covered one 0
sum_tuple_deficit_le         ∑_b (t·m − H₂(tuple_b)) ≤ Δ   — ZERO SLACK
card_support_tupleOf_ge      |supp(tuple_b)| ≥ 2^{tm − d_b}
poorBlocks / card_poorBlocks_le      |poor| · η ≤ Δ
joint_richness               both halves together
```

**`joint_richness`**: under a total deficit of `Δ` on the joint law, all but at most `Δ/η` of
the `|B|` blocks see their `t` sampled windows take at least `2^{tm − η}` **distinct joint
values**.

## 2. Which bottleneck moved

Two things.

1. **`sum_tuple_deficit_le` is new machinery**, not a corollary: the campaign's budget lemma
   (`sum_patCoord_deficit_le`) accounts the `⌊m/ℓ⌋` *pattern* coordinates plus the remainder;
   this one accounts the **whole window tuple** through `H₂_le_sum_H₂_map` with a two-family
   decomposition (`richFam` = block tuples ⊕ missed atoms), and it also closes with zero slack:
   the deficit on the `|B|` tuples is at most the deficit `Δ` on the joint law, not `tΔ`.
2. **The frequency/richness dichotomy is now proved on both sides.**  Lap 48: the deficit
   premise cannot control a *fixed* pattern's frequency (witness kills it outright).  Lap 49:
   the same premise *does* control the joint support size on most blocks.  The lap-48 witness
   is consistent with lap 49 — its tuple deficit is `t`, so it takes `2^{t(m−1)}` joint values
   per block, comfortably rich.  That is the sharp statement of what §5's "entropy controls
   richness, not frequency" means jointly.

## 3. The next bounded test (lap 50)

The schedule instance and digit rendering of `joint_richness`, mirroring laps 45/47:

1. `richSched i t η := joint_richness` at `A = (gridAt i).Atom`, `B = Fin (nblk i t)`,
   `m = kk i`, `blk = blkSched i t`, `Δ = 50√K·|Atom|`.
2. With `|Atom| ≤ 2t·nblk`, `Δ/|B| ≤ 100t√K`, so at `η = 200t√K` **at least half** the blocks
   are rich: their `t` windows take `≥ 2^{t(m_K − 200√K)}` joint values, and since
   `m_K = K/4`, the richness *rate* `(m_K − 200√K)/m_K → 1`.
3. Digit rendering: `suppOf (jointLawAt i G₄ |>.map (tupleOf …))` is the set of distinct
   `t`-tuples of `m_K`-bit binary blocks of `G₄` read at `(2·kIdx(n, blkSched b s))_s` as `n`
   ranges over `P_K`; state the count on that set via `map_empirical_p`/`Finset.image`.

Endpoint to aim for: *for at least half the blocks, the number of distinct `t`-tuples of
`m_K`-bit binary blocks of `G₄` seen at the sampled positions is at least
`2^{t·m_K(1 − 800/√K)}`* — a joint statement with no averaging over positions at all, and hence
outside the reach of the lap-48 obstruction.

## Claim limits (unchanged)

Nothing here is a statement about the normality of `G₄`; all endpoints concern the *sampled*
positions only.
