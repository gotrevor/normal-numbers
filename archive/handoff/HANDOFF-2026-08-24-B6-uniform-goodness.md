# HANDOFF 2026-08-24 — B6 crux RE-ROUTED: hdom refuted, uniform-goodness route PROVED to the block; only the schedule plumbing remains

**Branch/HEAD**: master @ `3c2c9b1`, `lake build` green (8768 jobs, was 8757 +11
new decls). Sole active `src/` `sorry` = the B6 crux
`exists_interleaved_affine_witness` (`CFScheduleA.lean`, ~line 1170). Headline
`exists_absolutely_normal_cf_normal_khinchin` re-verified trust-triple
`[propext, Classical.choice, Quot.sound]`. DIRECTION.md item 3 (the recursion's
dominance) is the live target; this lap settled its route-decisive uncertainty.

## The arc this lap (11 commits `11cbecc..3c2c9b1`, all axiom-clean)

### 1. Route-decisive CORRECTION: `hdom` is UNATTAINABLE (commit `ec0875d`)
The prior handoff called the recursion "pure wiring" with "hdom follows from slow
growth." **That was wrong**, verified against the exact compiler dependency
(`chain_cf_digit_freq_tendsto` → `cfDiscLt_append_take` → `hdom`, CFChainFreq:391-397).
The affine schedule forces each steer block to RESOLVE one stream to the other's
metric scale, costing `≈ log_φ(cfK) = Θ(word)` digits (Lévy: `log Kₙ ≈ 1.19 n` for
freq-good words). So `block_s = Θ(|w_s|)`, growth is geometric, `block/word → const
≠ 0`: **`hdom` cannot hold**. The hdom-FREE uniform-prefix-goodness route is
mandatory. Full reasoning: `PENDING_WORK.md` top two ⭐⭐⭐⭐⭐⭐/⭐⭐⭐⭐⭐ sections.

### 2. The uniform-goodness route, PROVED end-to-end to the block level
Tight-block toolkit (needed regardless — caps block length + additive slack), in
`TBrickRefine.lean`:
- `goldenRatio_pow_le_sqrt5_mul_fib_add_one`, `sqrt5_mul_fib_le_goldenRatio_pow_add_one`
  (tight Binet bounds, pin `√5·fibₙ ∈ [φⁿ−1,φⁿ+1]`)
- `fib_sq_gt_of_goldenRatio`, `exists_nat_goldenRatio_pow_gt` (logarithmic thresholds)

The uniform-goodness chain, in `CFScheduleA.lean` (each wraps the previous):
- `exists_freq_good_block_steer_len` — tight caller-controlled block length
- `gaussMeasure_multiscale_cfBadZone_le` — bad-zone measure over a scale-set NS
- `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo` — point avoiding ALL scales
- `exists_multiscale_freq_good_block_steer_len` — block freq-good at every `n∈NS`
- `abs_countOccurrences_take_interp` — per-scale → every-prefix interpolation
- `quadScales` + `quadScales_{nonempty,card_le,mem_ge,max,cover}` — quadratic scales
- **`exists_uniformly_freq_good_block_steer`** — THE CRUX CRACK: a steer block `u`
  of length `n₁+m²` with `cfCylinder(wx++u) ⊆ (c,d)` AND every prefix good:
  `∀ k∈[n₁,|u|], ∀v∈F, |countOcc v (u.take k) − γv·k| < δ·k + (4√k + 2|v|)`.
  Slack `= o(k)`. This is the hdom-free block-goodness the schedule needs.

### 3. hdom-free chain limit — STARTED
- **`chainTail_dev_split_var`** (`CFChainFreq.lean`, after `chainTail_dev_split`):
  varying-slack telescoping, tail dev `< ε·len + ∑_{i≤k}(C(s₀+i)+(|v|−1))`. The
  base-word-goodness half of the hdom-free limit.

## NEXT (only plumbing remains — the math uncertainty is settled)
Detailed recipe: `PENDING_WORK.md` "REMAINING (step 4 only)".
1. **hdom-free `chain_cf_digit_freq_tendsto` variant** (CFChainFreq, copy-extend,
   NEVER edit the existing one). Hypothesis per block = uniform-prefix-goodness
   (`∀k, |dev((chainApp w s).take k)| < δ_s·k + (4√k+2|v|)`) INSTEAD of `hgood∧hdom`.
   - whole-word goodness: `chainTail_dev_split_var` (built) — need `∑ C_j = o(word)`
     from geometric `|u_j|` growth (a `Filter.Tendsto` lemma; `4√·` and `s·2|v|`
     both `o(Σ|u_j|)`).
   - mid-block prefix at `p = |w s| + j`: decompose `w s ++ (chainApp w s).take j`;
     bound via `countOccurrences_append_addslack₂` using (whole-word good `w s`) +
     (block's OWN prefix bound at `j`). **This replaces `cfDiscLt_append_take`** —
     no hdom. Then `δ_s → 0` gives the metric limit. Mirror the structure of the
     existing `chain_cf_digit_freq_tendsto` (CFChainFreq:327-412), swapping those
     two steps.
   - wrap into `chain_orbit_equidist`-style `CFOrbitEquidist` via the existing
     orbit↔window bridge (CFChainFreq:423 tail is reusable as-is).
2. **ψ-round `_uniform`**: rebuild `exists_freq_good_extend_affine_steer` to emit
   uniformly-good blocks — call `exists_uniformly_freq_good_block_steer` per stream.
   Choose `n₁,s ~ poly(1/δ_s)` (measure budget) and `m_s` so `n₁+m²_s` reaches the
   resolution length `~κ|w_s|` (tight Binet + `exists_nat_goldenRatio_pow_gt`).
   The budget `(m+1)·A₁(n₁) < γ(c',d')` is satisfiable once `|w_s|` large (geometric
   beats poly) — this is the per-round feasibility the schedule must discharge.
3. **`SchedStateA`/`schedStepA`/`schedA`** two-stream recursion (mirror
   `CFSchedule.sched`), → two uniformly-good chains → the step-1 limit →
   `CFOrbitEquidist` both streams → assemble `exists_interleaved_affine_witness`.
   Limit-gluing toolkit READY: `eq_of_mem_iInter_Icc`,
   `cfCylinder_chain_volume_tendsto`, `irrational_mem_Ioo_of_mem_iInter_cfCylinder`.

## Watch-outs
- The four `goldenRatio`/`fib` commits' "tight blocks ⇒ hdom" framing is
  SUPERSEDED by commit `ec0875d` — those lemmas remain load-bearing (block-length
  cap + slack bound), but do NOT resurrect the hdom route.
- ADDITIVE ONLY: never edit frozen/locked decls or the existing
  `chain_cf_digit_freq_tendsto`/`chainTail_dev_split`; copy-extend. Re-`#print
  axioms exists_absolutely_normal_cf_normal_khinchin` after schedule work.
- `chainApp w s = w(s+1).drop|w s|`; the uniform block IS this appended word.
