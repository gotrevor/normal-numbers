# HANDOFF — entropy laps 44–45 (the uniform endpoint), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8976 jobs**.  `src/` sorry-free.  No axiom.

## 0. The two laps in one line

The uniform `t`-wise bound is proved (lap 44) and rendered on `G₄`'s digits (lap 45):
**every** vector of sampled positions, averaged, decorrelates.

## 1. What was proved

`G4EntropyJointUniform.lean`, abstract layer (lap 44):

```
mul_sqrt_div_self       a·√(X/a) = √(aX)
diagAgg m ℓ t blk L w jj = ∑_b (L.map (jjPat … b jj)).prob {w}
sup_coe_lt              max d < J
abs_diagAgg_sum_sub_le  |∑_{j<J−max d} diagAgg (d+j·1) − |B|(J−max d)2^{−ℓt}|
                          ≤ 2√(|B|J·log2·Δ)          (one diagonal)
abs_uniPatFreq_sub_le   |uniPatFreq − 2^{−ℓt}| ≤ 2t√(log2·Δ/(|B|·J))   (Jℓ ≤ m)
```

The diagonal bound is `abs_avg_patPos_prob_opt` at offsets `pp s = d s·ℓ` and cut length
`D_d = (J − max d)·ℓ` — a multiple of `ℓ`, so `D_d/ℓ = J − max d` **exactly** (the lap-43
warning).  `sum_diag_decomp` reindexes, `card_diagSet_le` counts the diagonals, and the weight
`J^{t−1}/J^t` cancels the `1/√(J − max d)` blow-up exactly.

Schedule layer (lap 45), namespace `G4.Sched`:

```
uniFreq i ℓ t x w                := uniPatFreq (kk i) ℓ t (kk i / ℓ) (blkSched i t) (jointLawAt i x) w
kk_le_two_mul_div_mul            m_K ≤ 2⌊m_K/ℓ⌋ℓ           (2ℓ ≤ m_K)
abs_uniFreq_sub_le_of_deficit    ≤ 2t√(4log2·ℓtδ/m_K)
abs_uniFreq_sub_le_primeLambertFour  ≤ 2t√(800log2·ℓt/√K)
tendsto_uniFreq_primeLambertFour
jjPat_eq_pack_iff / uniFreq_eq_count / uniFreq_eq_digits
tendsto_occursCountJointUniform_primeLambertFour
```

The endpoint:

```
#{(n,b,jj) : ∀ s<t, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + (jj s)·ℓ)}
  / (|P_K| · nblk_K · ⌊m_K/ℓ⌋^t)  →  2^{−ℓt},
```

`jj` ranging over **all** of `[0,⌊m_K/ℓ⌋)^t`.  Strictly stronger than both predecessors:
`tendsto_occursCountJoint_…` is the common-aligned diagonal, `tendsto_occursCountJointPos_…` is
one fixed offset vector; this is every independent choice of the `t` positions, averaged.
`#print axioms` on both new headline endpoints prints the trust triple.

## 2. Which bottleneck moved

The lap-40 narrowing (uniform average unreachable) is now not merely retracted but **replaced by
a theorem**.  The price of full independence over positions is a single factor `t` on the
aligned bound — no new hypothesis, no new quantifier restriction beyond `2ℓ ≤ m_K`.

## 3. The next bounded test

Per trigger **E-T7** the next altitude lap owes a successor target.  Candidates visible from
here, in decreasing order of value:

1. **Drop the averaging over `jj`**: the current statement averages over position vectors.  A
   *per-vector* statement (fixed `jj`, uniform in `jj`) would need a bound uniform over the
   `J^t` vectors, i.e. the `ℓ∞` rather than `ℓ¹` control — the capacity argument gives `ℓ¹` only,
   so this is a genuine open question, not a rendering exercise.
2. **Unaligned positions**: `jj s · ℓ` is aligned to the `ℓ`-grid.  `abs_avg_patPos_prob_opt`
   already allows arbitrary `pp`, so the uniform version over *all* positions `p ∈ [0, m_K − ℓ]`
   (not just multiples of `ℓ`) should follow by the same diagonal decomposition with `ℓ ↦ 1`
   in the index arithmetic — the cheapest real strengthening.
3. The wall measurement (`G4EntropyWall.lean`) is closed; normality on this mechanism stays
   closed (lap 37/39).

## Claim limits (unchanged)

Nothing here is a statement about the normality of `G₄`.  All endpoints concern the *sampled*
positions only.
