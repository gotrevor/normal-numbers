# HANDOFF — entropy session wrap, laps 38–43, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  **HEAD** `58564fe`.  Working tree **clean**.
`lake build` 🟢 **8976 jobs**.  `src/` **sorry-free**.  No `axiom` introduced.
No pre-expedition G4/G5 file edited.  Preserved declarations re-checked this session and all
printing `[propext, Classical.choice, Quot.sound]`: `isDisjunctive_four`, `isDisjunctive_two`,
`isDisjunctive_base`, `primeSumAtBase_eq_primeLambertAtBase`, `entropy_E0`, `entropy_E1`.

## Where the campaign stands

**Every item of the lap-37 CURRENT DIRECTIVE is closed.**

| Directive item | Closed at | Endpoint |
|---|---|---|
| 🎯 rung 3 (joint `t`-wise, aligned) | lap 38 | `Sched.tendsto_occursCountJoint_primeLambertFour` |
| 📌 measure the wall | lap 39 | `Sched.density_le_pow_real`, `Sched.window_needed_ge`, `not_qForces_normal_at_superpow` |
| 🎯 **as literally stated** (a position `p_s` **per window**) | laps 40–41 | `Sched.tendsto_occursCountJointPos_primeLambertFour` |

Per trigger **E-T7**, no lap in this session picked its own successor target; **the next
altitude lap must set one.**

## Lap by lap

- **38** `G4EntropyJointSched.lean` — `blkSched` + injectivity, `patFreq`,
  `abs_patFreq_sub_le_of_deficit` (`≤ 2√(2log2·ℓtδ/m_K)`),
  `abs_patFreq_sub_le_primeLambertFour` (`≤ 2√(400log2·ℓt/√K)`), the limit, the digit
  rendering, and `tendsto_occursCountJoint_primeLambertFour`.  Design correction in
  `G4EntropyJoint.lean`: all three families of `jointFam` now land in `Fin (2^(ℓt+m))` via
  `upPat`/`upLeft`, which deletes the hypothesis `m ≤ ℓ·t` (it fails at the schedule).
- **39** `G4EntropyWall.lean` — `quartic_le_gridB` (`100K⁴ ≤ B`; `cube_le_gridB` was not
  tight), `density_le_pow`/`_real` (**sampled density `≤ ⅛(2/K⁶)^K`**, against the density
  **one** `qForces_normal_iff_density_one` demands), `levelBudget_of_le_superpow`,
  `window_needed_ge` (density `> 1/4` needs some `mm i ≥ K^{4K}·m_K`),
  `not_qForces_normal_at_superpow` (supersedes `not_qForces_normal_at_pow`).
- **40** `G4EntropyJointPos.lean` — the abstract independent-offset bound.  **The idea: change
  the window, not the ledger.**  `cutTuple m D ρ` cuts each window to a common length `D` at
  *its own* offset; `H₂_cutTuple_ge` shows this costs exactly `|A|(m−D)` bits, so an `m`-window
  deficit `Δ` becomes a `D`-window deficit of the **same** `Δ` and
  `abs_avg_patCoord_prob_opt` applies verbatim with `m ↦ D`.  Hence
  `abs_avg_patPos_prob_opt : ≤ 2√(log2·ℓΔ/(|B|·D))` — the offsets are free.
- **41** the `G₄` instance (`≤ 2√(800log2·ℓt/√K)` when `2(max pp + ℓ) ≤ m_K`), the limit, and
  the digit rendering to `tendsto_occursCountJointPos_primeLambertFour`:
  `#{(n,b,j) : ∀ s<t, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + pp s + jℓ)} /
  (|P_K|·nblk_K·⌊(m_K − max pp)/ℓ⌋) → 2^{−ℓt}`.
- **42** **retracted lap 40's own narrowing.**  It claimed the *uniform* average over all
  position vectors was unreachable, on the grounds that a jointly injective family of
  `(m/ℓ)^t` pattern coordinates per block would carry `tℓ(m/ℓ)^t` bits against the `tm` its
  windows hold.  True, but no *single* such family is needed: decompose `jj ∈ [0,J)^t` as
  `jj = d + j·1` with `min d = 0`; each diagonal is exactly what `abs_avg_patPos_prob_opt`
  controls, contributing `≤ 2√(log2·Δ·J/|B|)` uniformly in `d`, and there are `≤ t·J^{t−1}`
  diagonals — giving `2t√(log2·ℓΔ/(|B|·m))`, the aligned bound times `t`.  Module
  `G4EntropyJointUniform.lean` opened with the two combinatorial leaves disclosed.
- **43** both leaves proved: `card_diagSet_le` and `sum_diag_decomp` (plus the `minv`/`diagOf`
  layer).  `src/` sorry-free again.

## The next bounded test (lap 44)

`abs_uniPatFreq_sub_le` in `G4EntropyJointUniform.lean` — assemble, in this order:

1. `sum_diag_decomp ht` to reindex `∑_{jj ∈ [0,J)^t}` as `∑_{d ∈ diagSet} ∑_{j < J − max d}`;
2. `patPos_eq_jjPat` to identify each diagonal's inner sum with `posPatFreq`'s numerator at the
   offset vector `pp s = d s · ℓ` and cut length `D_d = m − (max d)·ℓ`;
3. `abs_avg_patPos_prob_opt` for the per-diagonal bound, then
   `(J − max d)·2√(log2·Δ/(|B|(J − max d))) ≤ 2√(log2·Δ·J/|B|)` (`√` monotone; no integral
   estimate is needed — the crude bounds suffice);
4. `card_diagSet_le` for the `t·J^{t−1}` factor.

Result: `|uniPatFreq − 2^{−ℓt}| ≤ 2t√(log 2·ℓΔ/(|B|·m))`.  Then the schedule instance
(`δ = 50√K`, `m_K = K/4`) and the digit rendering to
`tendsto_occursCountJointUniform_primeLambertFour` — *every* vector of sampled positions,
averaged, which would be the strongest form of the decorrelation statement this arithmetic
supports.

⚠️ Watch: `patPos` uses `D/ℓ` as the index range while the decomposition uses `J − max d`;
these agree only up to `⌊·⌋`, so state the assembly with `D_d := (J − max d)·ℓ` (a multiple of
`ℓ`) rather than `m − (max d)ℓ`, so that `D_d / ℓ = J − max d` exactly.

## Claim limits (unchanged)

Nothing here is a statement about the normality of `G₄`, and normality on this mechanism is
**closed** (lap 37 reflection, quantified at lap 39: sampled density `≤ ⅛(2/K⁶)^K` against the
required density one).  All new endpoints are about the *sampled* positions only.
