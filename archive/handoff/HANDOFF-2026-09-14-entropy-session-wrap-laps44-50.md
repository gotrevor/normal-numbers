# HANDOFF — entropy session wrap, laps 44–50, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  **HEAD** `781b6ab`.  Working tree **clean**.
`lake build` 🟢 **8979 jobs**.  `src/` **sorry-free**.  No `axiom` introduced.
No pre-expedition G4/G5 file edited; all work is in new `G4Entropy*` modules.

Preserved declarations re-checked, all printing `[propext, Classical.choice, Quot.sound]`:
`isDisjunctive_four`, `isDisjunctive_two`, `isDisjunctive_base`,
`primeSumAtBase_eq_primeLambertAtBase`, `entropy_E0`, `entropy_E1`.

## Where the campaign stands

The session opened on the lap-43 "next bounded test" (assemble `abs_uniPatFreq_sub_le`) and
closed the whole **joint-frequency** line, then opened and closed a **new line** (richness).

### The frequency ladder — complete, with its boundary proved

| lap | endpoint | positions | form |
|---|---|---|---|
| 38 | `tendsto_occursCountJoint_…` | one common aligned position `jℓ` | `ℓ¹` |
| 41 | `tendsto_occursCountJointPos_…` | a fixed offset vector, aligned shifts | `ℓ¹` |
| **45** | `tendsto_occursCountJointUniform_…` | **all** aligned vectors `[0,⌊m_K/ℓ⌋)^t` | `ℓ¹` |
| **47** | `tendsto_occursCountJointFree_…` | **all** vectors `[0,m_K−ℓ+1)^t`, no alignment | `ℓ¹` |
| **48** | `no_pointwise_bound_from_deficit` | any **fixed** vector | **impossible** |

Lap 47 is the strongest frequency statement this arithmetic supports, and lap 48 proves it is:
the averaging is necessary, not an artefact of the estimates.

### The richness line — new, opened and rendered

| lap | endpoint |
|---|---|
| **49** | `sum_tuple_deficit_le` (zero-slack budget for the untruncated tuple), `joint_richness` |
| **50** | `joint_richness_primeLambertFour`, `jointValues_eq_digits`, `tendsto_richness_shortfall` |

## Lap by lap

- **44** `abs_uniPatFreq_sub_le`: `|uniPatFreq − 2^{−ℓt}| ≤ 2t√(log2·Δ/(|B|J))` when `Jℓ ≤ m` —
  the aligned bound times `t`.  Assembly: `sum_diag_decomp` (jj = d + j·1) + per-diagonal
  `abs_diagAgg_sum_sub_le` at offsets `d s·ℓ`, cut `D_d = (J − max d)ℓ` (so `D_d/ℓ` is exact) +
  `card_diagSet_le`.  New helper `mul_sqrt_div_self`.
- **45** schedule instance at `J = ⌊m_K/ℓ⌋` and digit rendering →
  `tendsto_occursCountJointUniform_primeLambertFour` (`≤ 2t√(800log2·ℓt/√K)`).
- **46** `G4EntropyJointFree.lean`: `pvPat`/`pvAgg`, `abs_alignedFamily_sub_le` (the diagonal
  bound freed from multiples-of-`ℓ` offsets), `cntRes`/`sum_range_mod_decomp` (the residue split
  `j = r + qℓ`), and `abs_uniPosFreq_sub_le`: `≤ 2t√(2log2·ℓΔ/(|B|P))` over **all** position
  vectors.  Alignment was an artefact of `abs_avg_patPos_prob_opt`'s step-`ℓ` family; removing
  it costs a factor `√2`.
- **47** schedule instance at `P = m_K − ℓ + 1` → `tendsto_occursCountJointFree_primeLambertFour`
  (`≤ 2t√(1600log2·ℓt/√K)`).
- **48** `G4EntropyPointwise.lean`: the uniform law on `∏_α lowHalf m` has entropy exactly
  `|A|(m−1)` — deficit **one bit per window**, far below the schedule's `50√K·|Atom|` — yet at
  the fixed position vector `pv ≡ 0` the all-ones pattern has probability `0` in every block.
  So no `o(1)` pointwise bound follows from the deficit premise.
- **49** `G4EntropyJointRich.lean`: `sum_tuple_deficit_le` (new machinery — the *untruncated*
  tuple through `H₂_le_sum_H₂_map` with `richFam` = block tuples ⊕ missed atoms, zero slack),
  `two_pow_H₂_le_card_support`, `joint_richness` (all but `Δ/η` blocks see `≥ 2^{tm−η}` joint
  values).
- **50** `suppOf_map_empirical`, `jointValues`, `jointValues_eq_digits`,
  `joint_richness_primeLambertFour`: for at least half the blocks the `t` sampled windows take
  `≥ 2^{t·m_K − 200t√K}` distinct joint values, richness rate `→ 1`
  (`tendsto_richness_shortfall`: `800/√K → 0`).

## The next bounded test (lap 51)

**Richness in *every* block, not just half.**  The Markov step in `card_poorBlocks_le` is lossy:
`∑_b d_b ≤ Δ` only yields a "most blocks" statement.  The bounded probe, in order:

1. Build the concentrating witness: a law putting *all* the deficit on block `0` — e.g. uniform
   on `{z : z (blk 0 s) = const for every s}` times free elsewhere — and compute its per-block
   deficits (`t·m` on block 0, `0` elsewhere).  Its total deficit is `t·m`, so the premise
   `m|A| − Δ ≤ H₂` holds with `Δ = t·m`, which at the schedule is `≪ 50√K·|Atom|`.
2. If that goes through, `joint_richness`'s "all but `Δ/η`" is **sharp** and the every-block
   form is refuted — mirror `no_pointwise_bound_from_deficit`'s shape and state it as
   `no_everyblock_richness_from_deficit`.
3. Then record (cheap corollary): the richness *rate* `1 − 800/√K` is independent of `t`, so
   `t` may grow with `K` subject only to `2t ≤ |Atom|` and `200t√K ≤ t·m_K`.

Per trigger **E-T7**, no lap in this session picked its own successor target beyond the handoff
chain; the next altitude lap should confirm or re-point.

## Claim limits (unchanged)

Nothing in this session is a statement about the normality of `G₄`; normality on this mechanism
is **closed** (lap 37 reflection, quantified lap 39: sampled density `≤ ⅛(2/K⁶)^K` against the
density **one** `qForces_normal_iff_density_one` demands).  All endpoints concern the *sampled*
positions only.
