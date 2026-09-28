# HANDOFF — entropy lap 20 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `07b9ee8`.  `lake build` green, **8959 jobs**.  New module
`src/NormalNumbers/G4EntropyDiagonal.lean`, sorry-free, trust triple.  No pre-expedition file
edited.

## What was proved

**`qForces_normal_iff_density_one`** — the universal statement the last four laps were
converging on.  Let `W : ι → ℕ × ℕ` be *any* family of (time, quantization level) pairs, over
any index set.  The sample values are `qVal W x i = ⌊2^{mᵢ} {2^{rᵢ} x}⌋`.  Then

> a satisfiable hypothesis about the values `qVal W x` implies binary normality
> **iff** the read set `qRead W = ⋃ᵢ [rᵢ, rᵢ + mᵢ)` has density one.

New ingredient: **`digitOf_congr_of_blockVal`** — a window value *determines* the digits inside
it (converse of the repo's `blockVal_congr`), by the recursion
`blockVal_succ : blockVal y j (m+1) = 2·blockVal y j m + digitOf 2 y (j+m)` and `omega`.  With
`blockVal_congr` this makes "the sample values" and "the digits on the read set" interchangeable,
so lap 16's negative half and lap 17–18's positive half both transfer verbatim.

**The implemented schedule is exhibited as an instance**: `Sched.SchedIdx` (scale, sample point,
atom), `Sched.schedW z = (2·kIdx, m_K)`, and `qRead_schedW_iff : qRead schedW j ↔ IsSampled j`.
`Sched.not_qForces_normal` then refutes it directly from `card_isSampled_le_real` (`≤ 1/4`).

## Which bottleneck moved

Lap 19 identified quantization as the obstruction but left one degree of freedom: the levels
`m_K = K/4` grow, so maybe a fast enough growth repairs the transfer.  It does not.  Only the
*union of the windows* matters, and growing `m` while the times stay sparse changes nothing.
Brief §6's positive branch is now closed in full generality:

| freedom the brief had | status |
|---|---|
| translate the grids | refuted (lap 10) |
| more grids at one scale | refuted (lap 11) |
| more scales, arbitrary pairs | refuted (laps 12–13) |
| any admissible scale at all | intrinsic obstruction (lap 14) |
| any digit-local statistic | density-one characterization (laps 16–18) |
| unquantized orbit values | forces normality at a single time (lap 19) |
| **any quantization level, any schedule** | **density-one characterization (lap 20)** |

## Next bounded test

Everything the expedition's interface can express is now settled.  The remaining mathematics is
a genuinely different object: a sampler whose datum is *not* a finite-precision reading of the
orbit, i.e. an unbounded-precision functional such as the `G4Jackson` / `G4SeparatingTest`
bounded-Lipschitz bump.  The bounded next lap:

* state `bumpVal φ r x := φ ({2^r x})` for a Lipschitz `φ` and prove it is **not** determined by
  `qVal W x` for any `W` with `qRead W` of density `< 1` — the exact analogue of
  `exists_orbitLocal_forces_normal` but with an explicit analytic test rather than normality
  itself.  That is the statement the entropy route would have to be rebuilt on, and it connects
  the barrier back to the Jackson layer that is already in the repo.
