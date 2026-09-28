# HANDOFF — entropy lap 42 (the lap-40 narrowing RETRACTED), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8976 jobs**.  New module compiles with **two
disclosed `sorry` leaves in `src/`** (named, both pure finite combinatorics); everything else in
the campaign stays sorry-free.

## 0. The lap in one line

Lap 40's narrowing — "the uniform average over all position vectors is unreachable by this
ledger" — is **false**, and the correct bound is the aligned bound times `t`.

## 1. The correction

The narrowing's counting was right about the wrong object.  A *single* jointly injective family
covering all `(m/ℓ)^t` position vectors would indeed have to carry `tℓ(m/ℓ)^t` bits against the
`tm` a block's windows hold.  **But no such family is needed.**  Decompose the vector of aligned
indices `jj ∈ [0,J)^t` (`J = ⌊m/ℓ⌋`) uniquely as `jj = d + j·1` with `min d = 0`.  For each
fixed *diagonal* `d`, the vectors `d + j·1` are precisely what lap 40's
`abs_avg_patPos_prob_opt` controls — at offset vector `pp s = d s·ℓ` and cut length
`D_d = m − (max d)·ℓ`.  Hence, uniformly in `d`,

```
diagonal d's unnormalized contribution ≤ (J − max d)·2√(log2·Δ/(|B|(J − max d)))
                                        ≤ 2√(log2·Δ·J/|B|)
```

and at most `t·J^{t−1}` diagonals exist, so

```
|uniform average − 2^{−ℓt}| ≤ (t J^{t−1}/J^t)·2√(log2·Δ·J/|B|) = 2t√(log2·ℓΔ/(|B|·m)).
```

The divergence of the individual diagonal bounds as `max d → J` is exactly cancelled by those
diagonals' weight — the crude bounds `√(J − max d) ≤ √J` and `#diagonals ≤ tJ^{t−1}` already
suffice, no integral estimate needed.

## 2. What landed — `G4EntropyJointUniform.lean`

```
jjPat m ℓ t blk b jj       the pattern at an arbitrary vector of aligned indices
patPos_eq_jjPat            patPos at offset vector d·ℓ IS jjPat at d + j·1
uniPatFreq m ℓ t J blk L w the uniform average over blocks and all jj ∈ [0,J)^t
diagSet t J                index vectors with a zero coordinate
card_diagSet_le            ≤ t·J^(t−1)                      -- sorry (leaf 1)
sum_diag_decomp            ∑_{jj} g = ∑_{d ∈ diagSet} ∑_{j < J − max d} g (d + j·1)
                                                            -- sorry (leaf 2)
```

Both leaves are finite combinatorics with no analysis in them.

## 3. The next bounded test (lap 43)

1. `card_diagSet_le`: `diagSet ⊆ univ.biUnion (fun s => univ.filter (fun d => d s = 0))`,
   `Finset.card_biUnion_le`, and each fibre injecting into `Fin (t−1) → Fin J` by
   `Fin.succAbove` (`t = 0` separately: `diagSet` is empty).
2. `sum_diag_decomp`: `Finset.sum_nbij'` with `jj ↦ (jj − min jj, min jj)` and
   `(d, j) ↦ d + j`.
3. Then `abs_uniPatFreq_sub_le`, the schedule instance, and the digit rendering to
   `tendsto_occursCountJointUniform_primeLambertFour`.
