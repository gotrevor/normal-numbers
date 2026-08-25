# HANDOFF — 2026-08-25 — B6 L4 z-side: subtlety-1 done, Z-I done, Z-II core landed

**Branch:** `master`  **HEAD:** `a273107`  **Build:** 🟢 8757 jobs, clean tree.
**Headlines:** both B5′ (`exists_absolutely_normal_cf_normal` T1,
`..._khinchin` T2) = trust-triple `[propext, Classical.choice, Quot.sound]` — DONE.
`exists_cfNormal_and_affine_cfNormal` (B6) = `+ sorryAx`.
**Sole open `src/` sorry:** the DEAD two-stream `schedA_block_linear`
(`CFScheduleA.lean:5078`), excised once the L4 z-side assembles.

## What this run landed (all axiom-clean, obey DIRECTION step 1→2→3)

1. **Subtlety 1 — ψ(xA) irrationality (step 1) ✓.** The `StepSpecL4`/`schedStepL4_exists`
   rebuild: append one diagonalisation filler digit `[d]` per stage
   (`exists_digit_cfCylinder_notMem`, now returns `a≤2`), block `= u++[d]`, `hword`
   `= n₁+m²+1`, freq slack `2|v|→3|v|`, cfKb rate `κ→κ+2log2`, new conjunct
   `enumPsiRat q r s ∉ cfCylinder S'.wx`. All 4 consumers rewired (`block_len_le'`,
   `chain_hfreq_of_uniform_blocks_snoc`, etc.). Delivered
   **`exists_xA_L4_psi_irrational`** (`wxSeq_L4_avoids_enumPsiRat` +
   `affineMap_irrational_of_iInter_avoids` + `mem_range_enumPsiRat`).
2. **Z-I (step 2) ✓.** `exists_scale_cfCylinder_psi_avoid_zbad` (Chebyshev budget
   discharge at `NSz={n}`) + `exists_scale_zgood_wxSeq_L4` (per-stage z-good witnesses).
   NB: `exists_scale_zgood_wxSeq_L4` is TRUE but OFF-PATH — see the obstruction below.
3. **Z-II core (step 3, in progress).** `blockCount_split` (`CFWordBridge.lean`):
   `blockCount(cfCyl v) n x = card(matches in first L windows)
   + blockCount(cfCyl v)(n−L)(gaussMap^[L] x)`.

## THE CRUX, now sharply located (read `PENDING_WORK.md` §"2026-08-25 CRUX FINDING")

The naive post-hoc z-good witness is in the WRONG SCALE REGIME: its z-good threshold
`N_s ~ 1/γcyl_s ~ φ^{2|w_s|}` sits far above the digit-agreement transfer range
`n ≲ |w_s|`, so `[N_s, |w_s|]` is EMPTY. Root cause: inside a deep cylinder `ψ` PINS
the first `~|w_s|` z-digits, so `blockCount` at `n ≲ |w_s|` is DETERMINED (= value at
`ψxA`), not selectable; z-digit `n` is only selectable at the pinning stage
(`|w_{s*}| ≥ n > |w_{s*-1}|`), where the feasible bad density is the CONDITIONAL/relative
`O(1/(n−L))`, needing a **ψ-conditional z-Chebyshev** (absolute `cfBadZone []` aggregate
too weak). `blockCount_split` is the exact decomposition that exposes that relative part.

## NEXT (hardest-first; DIRECTION forbids two-stream / target-shrink / hdom / box-stuck)

1. **Assemble the ψ-conditional z-Chebyshev** from `blockCount_split` +
   `chebyshev_blockCount_brick`. Target shape (for `z ∈ cfCylinder wz`, `|wz|=L`, `n>L`):
   `γ(cfCylinder wz ∩ {z : δ ≤ |blockCount(cfCyl v) n z/n − γv|})
   ≤ 7·(8|v|+80)γv/((δ/2)²(n−L))·γ(cfCylinder wz)`.
   Route: `z` scale-`n` freq-bad (tol δ) ⇒ shifted orbit `gaussMap^[L] z` scale-`(n−L)`
   freq-bad (tol `δ' = δ − O(L/n)`), via `blockCount_split` (prefix count `C ∈ [0,L]`,
   `|C/n| ≤ L/n` and the `n` vs `n−L` rescale ≤ `L/n`); then the bad set
   `⊆ cfCylinder wz ∩ (gaussMap^[L])⁻¹'{shifted-bad}`, whose mass is
   `chebyshev_blockCount_brick wz v … (n−L) (δ')`. The ε-management (choose `n ≥ 2L`,
   `δ' = δ/2`) is the only fiddly part.
2. **Pinning-stage z-selection into the block builder.** Thread the window-`(|w_{s-1}|,
   |w_s|]` z-bad avoidance into
   `exists_uniformly_freq_good_block_steer_len_rel_cfK`'s budget (joint interval-scale
   template = `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo`), keeping blocks LINEAR
   (extra term `O(1/|u|)·γ`, absorbed like the x-freq term). Record in `StepSpecL4`.
3. **Z-II coverage** via `tendsto_of_scale_coverage`: every large `n` pinned at exactly
   one stage, `δ_s→0`, transfer range matches ⇒ no gap. Then step 4 assemble NEW
   `exists_interleaved_affine_witness` on the L4 stream + excise the two-stream sorry.

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms` both B5′ headlines after any schedule wiring
  (must stay trust triple).
- Uncommitted edits: NONE (clean tree at `a273107`).
