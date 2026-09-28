# HANDOFF — 2026-08-24 — B6 L4: ROUTE-B MEASURE+SELECTION+Z-ENGINE LAYER COMPLETE

**Branch:** `master`  **HEAD:** `3b6d753`  **Build:** 🟢 8757 jobs, clean tree.

## Brick-4 z-transfer prerequisites also DONE this session (axiom-clean)
- `blockCount_eq_of_cfDigit_agree` (`4b8cfb8`) — digit agreement on first `m` ⇒ equal
  `v`-block count at scales `n` with `n+|v| ≤ m`.
- `exists_nhds_cfDigit_eq` (`3b6d753`) — local CF-digit stability: an open ball around an
  irrational `y∈(0,1)` on which the first `m` CF digits are constant.
- **NEXT (compose these + ψ-Lipschitz):** transfer lemma `ψ(xA) ∉ cfBadZone [] v n δ_s`
  from a deep-enough `x`-cylinder + the brick-3′ point's avoidance; then the
  `SchedStateL4` recursion, brick 5-proper (`tendsto_of_scale_coverage`), brick 6.

  **Sole open `src/` sorry:** the DEAD
two-stream crux `schedA_block_linear` (`CFScheduleA.lean`), reached only via
`schedA_hfreq_x`/`schedA_hfreq_z` → `schedA_block_geom` → `schedA_block_linear`.
It is to be EXCISED once the route-B single-stream `exists_interleaved_affine_witness`
lands. **Headline `exists_absolutely_normal_cf_normal_khinchin` = trust-triple**
(re-verified). DIRECTION.md CURRENT DIRECTIVE (resume single-stream L4) outranks this.

## What this session proved (all axiom-clean, trust-triple) — the ENTIRE route-B measure layer

The single-stream L4 route's feasibility was the whole B6 crux uncertainty. It is now
SETTLED YES in-kernel. Commits, in dependency order:

1. `cfBadZone_nil_shift_mem_cfBadZone` + `gaussMeasure_cfBadZone_nil_inter_cylinder_le`
   (`d16a00a`) — **brick 2b-ii, two-scale split.** `blockCount` is a Birkhoff sum, so
   `birkhoffSum_add` splits `bc A N x = bc A d x + bc A (N−d)(gᵈx)` with NO seam junk;
   the seam term `∈[0,d]` shaves only `d/N` of the slack. (Reformulation that killed the
   feared countOccurrences-seam mess.)
2. `gaussMeasure_interval_sdiff_covered_le` (`c9426c4`) — **brick 2b-i, γ-residual**, a
   pushforward of the ALREADY-EXISTING Lebesgue `volume_interval_sdiff_covered_le`
   (`CFIntervalGood`). `coveredByCyl`/covering geometry was already done — reused, not
   re-derived.
3. `gaussMeasure_cfBadZone_nil_inter_cylinder_frac_le` (`6921bde`) — per-cylinder
   fraction (2b-ii ∘ `chebyshev_blockCount_brick`); the fraction is uniform in `w'`.
4. `gaussMeasure_interval_inter_cfBadZone_nil_le` (`db09458`) — **brick 2b-iii single
   scale, THE route-decisive bound:** `γ((a,b) ∩ cfBadZone [] v N δ) ≤ frac·γ(a,b) +
   residual`, via cover-by-depth-`d` + `measure_biUnion` (disjoint) + `ENNReal.tsum_mul_left`.
5. `gaussMeasure_interval_inter_iUnion_cfBadZone_nil_le` (`37ba36a`) — F/NS aggregate
   (finite double-subadditivity).
6. `gaussMeasure_interval_inter_preimage_affineMap_le` (`08ba500`) — **ψ-pullback
   bridge:** `γ((c,d)∩ψ⁻¹S) ≤ (2/q)·γ(S∩ψ((c,d)))` via `preimage_image_eq` (injective ψ)
   + brick 1.
7. `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo` (`f4ac8fd`) — **brick 3′, route-B
   combined selection:** picks irrational `x∈(c,d)` avoiding x-bad(base `wx`) AND
   ψ⁻¹(z-bad, ABSOLUTE base `[]`) with LINEAR mass budget. hbound z-term uses the pullback
   bridge + aggregate lemma.
8. `tendsto_of_scale_coverage` (`6933f05`) — **brick 5 core, z-side engine:** `f n → L`
   when `|f n−L|<δ_s` on stage `s`'s scale set and stages cover all large `n` with `δ_s→0`.
   This is WHY `ψ(xA)` equidistributes with NO telescoping chain.

## The remaining work: brick 4 (single-stream recursion) + wiring 5/6

**Where the sorry actually lives:** `schedA_hfreq_x/z` depend on `sorryAx` (via
`schedA_block_geom`→`schedA_block_linear`); the schedule STEP
(`exists_freq_good_extend_affine_steer_uniform`, `schedStepA_exists`) is CLEAN. The sorry
is the SLACK-summability (`hslack`), which needs geometric word growth = linear blocks —
FALSE for the two-stream (it steers a z-block into `J_z=ψ(x-cyl)`, whose width is
z-cylinder-nested ⇒ super-exponential block). Route B removes the z-block entirely.

**Brick 4 = a route-B single-stream schedule.** Build ONLY `wxSeq_L4` (no `wzSeq`):
- **State `SchedStateL4`:** `wx` (genuine) + interval `(e,f)` with `cfCylinder wx ⊆
  ψ⁻¹(Ioo e f)` (same `hinv` as `SchedStateA`, DROP all `wz` fields).
- **Step:** mirror `exists_freq_good_extend_cfCylinder` (line 2005, CLEAN, LINEAR blocks,
  pure x-side) to extend `wx→wx'` freq-good; ADDITIONALLY, at stage `s`, use brick 3′
  (`exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo`) to select the sub-interval so the
  point avoids ψ⁻¹(absolute z-bad zones for the stage's z-range `NSz_s`), then refine
  `wx'` DEEP ENOUGH that `ψ(cfCylinder wx')` has diameter below a depth-`max(NSz_s)`
  z-cylinder — so ψ(x)'s first-`n` z-digits (n∈NSz_s) are FIXED for all x∈cfCylinder wx',
  hence the point's z-freq-goodness transfers to the limit `ψ(xA)`. (This "fine x-cylinder
  fixes finitely many z-digits" transfer, from ψ continuity, is the one genuinely new
  sub-lemma; everything else is existing apparatus.)
- **x-side hfreq:** reuse `chain_hfreq_of_uniform_blocks` with LINEAR blocks — NO
  `schedA_block_linear` needed (the x-block from `exists_freq_good_extend_cfCylinder` is
  `n ≈ max(N,L,|wx|)+1`, linear). So `chain_orbit_equidist_uniform` gives
  `CFOrbitEquidist xA` clean.
- **Brick 5 proper:** instantiate `tendsto_of_scale_coverage` with `f n = blockCount
  (cfCyl v) n (ψxA)/n`, `S s = NSz_s`, `havoid` from the stage z-avoidance transfer,
  `hcover` from the schedule design (`δ_s→0`, `NSz_s` cofinal — pick e.g. quadratically
  spaced ranges `[≈2|wx_s|, …]` with `δ_s→0`). ⇒ `CFOrbitEquidist (ψxA)`.
- **Brick 6:** assemble the NEW `exists_interleaved_affine_witness` proof (xA from x-side,
  ψxA equidist from brick 5, ψxA∈(0,1) from interval nesting, ψxA irrational from xA
  irrational + q≠0); then EXCISE `schedA_block_linear` + the dead `schedA`/`wzSeq`/
  `schedA_hfreq_*` two-stream layer.

## Notes
- ADDITIVE ONLY 🧊: after schedule work re-`#print axioms
  exists_absolutely_normal_cf_normal_khinchin` — MUST stay trust-triple.
- Route-B lemmas are contiguous in `CFScheduleA.lean` (bricks 1/2a at ~255–385; new layer
  after brick 2a ~488–1010; brick 5 core after brick 3′). PENDING_WORK.md top has the full
  brick list with commit hashes.
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
