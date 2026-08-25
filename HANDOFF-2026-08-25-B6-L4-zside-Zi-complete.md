# HANDOFF — 2026-08-29 — B6 L4: crux proved, x-side done, Z-I measure engine complete

**Branch:** `master`  **HEAD:** `1ad27cd`  **Build:** 🟢 8757 jobs, clean tree.
**Headline:** `exists_absolutely_normal_cf_normal_khinchin` = `[propext, Classical.choice,
Quot.sound]` (re-verified). `exists_cfNormal_and_affine_cfNormal` still `+ sorryAx` via the
DEAD two-stream route.
**Sole open `src/` sorry:** the DEAD two-stream `schedA_block_linear` (CFScheduleA.lean:4687),
excised once the L4 z-side lands.

## What landed this session (9 commits, all additive + axiom-clean)

**THE CRUX (DIRECTIVE step 3) IS PROVED:**
- `schedL4_block_linear` (`030d8fb`) — `|chainApp (wxSeq_L4) s| ≤ ρ·|wxSeq_L4 s|`. Plus helpers
  `poly_succ_le_two_pow`, `inner_bound`. Needs `set_option maxHeartbeats 1600000`.

**x-side downstream (DIRECTIVE step 4, REUSE):**
- `schedL4_hfreq_x` (`ebf28fa`) — x chain-freq via `chain_hfreq_of_uniform_blocks` + the crux.
- `exists_xA_L4_orbit_equidist` (`c0d188b`) — `xA` irrational in (0,1), orbit equidistributes.

**Z-I z-side measure engine (COMPLETE):**
- `exists_irrational_mem_cfCylinder_notMem_of_gaussMeasure_lt` (`07d832d`) — cylinder selector.
- `gaussMeasure_cfCylinder_inter_preimage_affineMap_le` (`c23d0b5`) — cylinder pullback bound.
- `exists_cfCylinder_psi_avoid_zbad` (`996ad56`) — per-stage z-good point engine (`hbudget` ⇒
  irrational `p∈cfCylinder wx'` with `ψ(p)∉cfBadZone[] v n δ` for `v∈F,n∈NSz`).

**Z-III irrationality-fix ingredients:**
- `countable_preimage_affineMap_range_rat` (`6ec0554`) — `ψ⁻¹(ℚ)` countable.
- `exists_digit_cfCylinder_notMem` (`1ad27cd`) — point-excluding extension digit.

## THE key structural finding this session

The block-linear rebuild of `StepSpecL4`/`schedStepL4_exists` (`acdcb19`) carries **ZERO z-side
control** (`grep cfBadZone|affineMap` over `StepSpecL4` = 0). So the current `wxSeq_L4` makes
`x` normal but gives NO control on `ψ(x)`. The DIRECTIVE calls the z-side "REUSE" — that assumed
the earlier StepSpecL4; the cfK rewire dropped it. **The z-side is NOT reuse; it needs schedule
re-integration.** Full analysis + the two design subtleties are in `PENDING_WORK.md` (top block,
"🔴 2026-08-29").

## NEXT (hardest-first) — remaining z-side, per PENDING_WORK

1. **Chebyshev budget lemma** discharging `exists_cfCylinder_psi_avoid_zbad`'s `hbudget` for a
   concrete `NSz_s`/`δ_s` (via `gaussMeasure_aggregate_cfBadZone_le`, `γ(cfCyl [])`, scales
   `n ≳ cfK(wx_s)²` so z-bad mass < `(q/2)·γ(cfCylinder wx_s)`). ⇒ p_s existence UNCONDITIONAL.
2. **Thread z-record into `StepSpecL4` + `schedStepL4_exists`** — add a conjunct recording the
   p_s avoidance (from step 1) AND the point-exclusion for `ψxA` irrationality (via
   `exists_digit_cfCylinder_notMem` diagonalised over `ψ⁻¹(ℚ)`). Adds one `_` to 4 destructurings
   (schedL4_block_linear, schedL4_hfreq_x, wxSeq_L4_length_ge, cfK_wxSeq_L4_le). KEEP the x-block
   builder as-is so blocks stay LINEAR (p_s is a point pick in the already-fixed cylinder).
   **Discharge cleanly (no new sorry) so `schedL4_block_linear` stays axiom-clean.**
3. **Z-II transfer engine** ⇒ `CFOrbitEquidist (ψ xA)`: from the per-stage p_s avoidance +
   `δ_s→0` + `NSz` cofinal, transfer to the limit via the 6 existing transfer lemmas
   (`exists_ball_cfDigit_psi_eq`, `exists_tail_cfCylinder_subset_ball`,
   `blockCount_eq_of_cfDigit_agree`, `notMem_cfBadZone_nil_of_cfDigit_agree`, …) +
   `tendsto_of_scale_coverage`. The delicate part is the **s↔n coupling** in `hcover`
   (subtlety 2, PENDING_WORK): each scale `n` needs its own large-enough `s` for the depth-`m=n+|v|`
   ball inclusion.
4. **Z-III assemble** NEW `exists_interleaved_affine_witness` on the L4 stream (`xA` from
   `exists_xA_L4_orbit_equidist`, `ψxA` equidist from Z-II, `ψxA∈(0,1)` from feasibility+interval,
   `ψxA` irrational from step-2 steering), then EXCISE the two-stream `schedA_block_linear` sorry.

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` after any
  schedule wiring — MUST stay the trust triple.
- Fast check: scratch `.lean` importing `NormalNumbers.CFScheduleA`, `lake env lean <abs>` from
  ROOT. Working scratch: `…/scratchpad/L4Assembly.lean` (the block-linear proof, compiles clean).
- DIRECTION.md governs; its "z-side = REUSE" is now known to be optimistic (see finding above) —
  flag for the next altitude/review lap.
