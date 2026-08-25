# HANDOFF — 2026-08-25 — B6 L4 z-side: crux reduced to ONE pure-L² sorry

**Branch:** `master`  **HEAD:** `7d52736`  **Build:** 🟢 8757 jobs, clean tree.
**Headlines:** both B5′ (`exists_absolutely_normal_cf_normal` T1,
`..._khinchin` T2) = trust-triple `[propext, Classical.choice, Quot.sound]` — DONE.
B6 `exists_cfNormal_and_affine_cfNormal` = `+ sorryAx`.
**`src/` open sorries (2):**
1. `variance_blockCount_psi_pushed` (`CFScheduleA.lean:~4254`) — **THE crux**, the pure ψ-pushed
   L² second-moment estimate (see below). Everything on the z-side reduces to this.
2. `schedA_block_linear` (`CFScheduleA.lean:~5630`) — the DEAD two-stream sorry, excised once the
   L4 assembly lands. Not to be attacked (dead route per DIRECTION).

## What this lap did (10 green commits, all obey DIRECTION step 1→2→3 re-integration)

Built the entire single-stream z-selection spine, then — crucially — adversarially verified it,
caught and corrected an over-claim, and found the clean architecture that reduces the whole z-side
to ONE precisely-stated analytic obligation. Chain (all axiom-clean except the final L²-core sorry):

- `chebyshev_blockCount_brick_psi_conditional` (`CFWordBridge`) — ψ-conditional z-Chebyshev
  (relative density `O(1/(n−L))`), via `blockCount_split`. **[kept, but OFF critical path]**
- `gaussMeasure_aggregate_psi_cond_le`, `exists_cfCylinder_psi_avoid_zbad_cond`,
  `exists_scale_cfCylinder_psi_avoid_zbad_cond{,_tight}`, `..._multiscale`,
  `notMem_cfBadZone_nil_of_notMem_psiCond` — the conditional-at-`wz` machinery. **[kept, OFF path]**
- **CORRECTION (commit 5816044):** the conditional-at-`wz` route hits a density-vs-coverage WALL
  (bounded bridge `γ(wz)/γ(wx')` ⟺ empty transfer range; every-`n` coverage forces exponential
  bridge). My earlier "DECISIVE" claim was wrong; corrected honestly. Lemmas stay (valid), off path.
- **CLEAN ARCHITECTURE (commit 875847e):** the whole z-side reduces to the ψ-pushed
  x-cylinder-relative Chebyshev `psi_pushed_chebyshev_brick`:
  `γ(cfCyl wx' ∩ ψ⁻¹(cfBadZone [] v n δ)) ≤ O(1/n)·γ(cfCyl wx')` (LOCAL density, `γ(cfCyl wx')`
  factor cancels the cylinder mass → polynomial threshold, transfer range `n ≲ |wx'|` NON-EMPTY).
  Proved from it: `gaussMeasure_aggregate_psi_pushed_le` and
  **`exists_scale_cfCylinder_psi_avoid_zbad_poly`** (the clean polynomial-threshold z-good selector,
  composes directly with the EXISTING absolute digit-agreement transfer
  `notMem_cfBadZone_nil_of_cfDigit_agree`).
- **CRUX NARROWED (commit 7d52736):** `psi_pushed_chebyshev_brick` is now PROVED from the deeper
  sorry `variance_blockCount_psi_pushed`. The full Chebyshev/Markov wrapper is machine-checked
  (restricted-measure `mul_meas_ge_le_integral_of_nonneg`, `f ≤ n²` integrability, `(δn)²`-rescale,
  γ-factor-cancelling arithmetic).

## NEXT (hardest-first — the sole remaining analytic crux)

1. **Prove `variance_blockCount_psi_pushed`** (`CFScheduleA:~4254`): the ψ-pushed second moment
   `∫_{cfCyl wx'} (blockCount(cfCyl v) n (ψ·) − nγv)² dγ ≤ (8|v|+80)·n·γv·γ(cfCyl wx')`.
   Route: expand the square → diagonal `∑_{k<n} γ(cfCyl wx' ∩ ψ⁻¹T^{-k}A)` (the `O(n)` term) +
   off-diagonal `∑_{k≠k'} [γ(cfCyl wx' ∩ ψ⁻¹T^{-k}A ∩ ψ⁻¹T^{-k'}A) − …]`, bound off-diagonal by
   ψ-conjugated mixing. **The real sub-task: extend `gaussMeasure_cylinder_mixing`
   (`CFGammaMixing.lean`, cylinder-base, geometric rate `(9/10)^g`) to INTERVAL / affine-image
   bases**, since `ψ(cfCyl wx')` is an interval, not a z-cylinder. Model the whole proof on
   `variance_blockCount_le` (`CFBlockFreq.lean:401`), which does exactly this for the full measure.
   This is the genuine research core (affine-invariance of CF-normality); narrow it, don't expect
   one-lap closure. If interval-base mixing is itself big, decompose it as its own named sorry.
2. **In parallel (independent, needs only the brick STATEMENT):** wire
   `exists_scale_cfCylinder_psi_avoid_zbad_poly` + the absolute transfer
   (`notMem_cfBadZone_nil_of_cfDigit_agree`, `exists_tail_cfCylinder_subset_ball`,
   `blockCount_eq_of_cfDigit_agree`) + `tendsto_of_scale_coverage` into `StepSpecL4` /
   `schedStepL4_exists` to deliver `CFOrbitEquidist (ψ xA)`, then assemble the NEW
   `exists_interleaved_affine_witness` on the L4 stream and EXCISE `schedA_block_linear`. The
   s↔n coverage is now clean (poly threshold ⟹ every-`n` coverable as `|wx'_s|→∞`).

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms` both B5′ headlines after any schedule wiring (trust triple).
- DIRECTION.md CURRENT DIRECTIVE still governs (single-stream re-integration; two-stream is
  proven-infeasible — do NOT resurrect it). PENDING_WORK.md has the full detailed record incl. the
  CORRECTION and the L²-core attack plan.
- Uncommitted edits: NONE (clean tree at `7d52736`).
