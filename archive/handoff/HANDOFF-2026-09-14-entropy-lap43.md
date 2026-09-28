# HANDOFF — entropy lap 43 (both combinatorial leaves proved), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8976 jobs**.  `G4EntropyJointUniform.lean` is
now **sorry-free**; `#print axioms` on both leaves prints the trust triple.  The whole campaign
is back to sorry-free in `src/`.

## 0. The lap in one line

The two leaves lap 42 disclosed — `card_diagSet_le` and `sum_diag_decomp` — are proved, so the
retraction of the lap-40 narrowing now rests on machine-checked combinatorics.

## 1. What was proved

```
card_diagSet_le (t J) : (diagSet t J).card ≤ t * J ^ (t − 1)
minv ht jj            the least coordinate (Finset.inf' over univ : Finset (Fin t))
minv_le / exists_minv_eq / minv_lt
diagOf ht jj          jj translated down so its least coordinate is 0
diagOf_mem / diagOf_add_minv / minv_add_sup_lt / minv_shift
sum_diag_decomp (ht : 0 < t) (g) :
  ∑_{jj : Fin t → Fin J} g jj = ∑_{d ∈ diagSet} ∑_{j < J − max d} g (d + j·1)
```

`card_diagSet_le`: `diagSet ⊆ ⋃_s {d | d s = 0}`, `Finset.card_biUnion_le`, each fibre injecting
into `Fin (t−1) → Fin J` by `Fin.succAbove`.

`sum_diag_decomp`: `Finset.sum_fiberwise_of_maps_to` over `diagOf`, then `Finset.sum_nbij'` on
each fibre with `jj ↦ minv jj` and `k ↦ d + k`.  The inverse must be **total**, so it is defined
with the clamp `((d s) + k) % J`, which is the identity on the range (`J = 0` is handled first:
`Fin t → Fin 0` and `diagSet t 0` are both empty for `t > 0`).

## 2. The next bounded test (lap 44)

`abs_uniPatFreq_sub_le`: assemble
`sum_diag_decomp` (reindex) + `patPos_eq_jjPat` (identify each diagonal's sum with
`posPatFreq`'s numerator at offsets `pp s = d s·ℓ`) + `abs_avg_patPos_prob_opt` (bound each
diagonal by `(J − max d)·2√(log2·Δ/(|B|(J − max d))) ≤ 2√(log2·Δ·J/|B|)`) + `card_diagSet_le`
(`≤ t·J^{t−1}` diagonals), giving `2t√(log 2·ℓΔ/(|B|·m))`.  Then the schedule instance and the
digit rendering.

## 3. Lean notes harvested this lap

- A `Finset.sum_nbij'` inverse map must be **total**: build it with a clamp (`% J`) and prove it
  agrees with the intended formula on the source finset, rather than threading a membership
  proof through the dependent type.
- `Finset.sup_lt_iff` postpones its `⊥ < a` side goal; elaborating it inline as `(by …)` can
  leave `a` a metavariable.  Prove `0 < J − minv` as a named `have` first.
- `Finset.exists_mem_eq_inf'` gives the attaining index for `inf'`.
