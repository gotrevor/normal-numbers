# HANDOFF 2026-08-24 — B6: hdom-free chain limit BUILT end-to-end; only ψ-round + recursion remain

**Branch/HEAD**: master @ `5fe8f09`, `lake build` green (8757 jobs). Sole active
`src/` `sorry` = the B6 crux `exists_interleaved_affine_witness`
(`CFScheduleA.lean:1559`). Both B5′ headlines re-verified axiom-clean
(trust-triple `[propext, Classical.choice, Quot.sound]`). This was a REVIEW lap
that ratified the hdom→uniform-goodness pivot, then proved item 1 of the
directive to completion.

## What landed this lap (4 commits `51726d1..5fe8f09`, all axiom-clean)

1. **`51726d1`** — review: ratified the `hdom`→uniform-goodness route pivot
   (`ec0875d`/`f2b4b33`), retargeted the CURRENT DIRECTIVE (was still mandating the
   REFUTED dominance route), refreshed STATUS.
2. **`2c61e7c` — `chainTail_dev_prefix_var`** (`CFChainFreq`, after
   `chainTail_dev_split_var`): the recursion core. If each appended block is
   uniformly prefix-good (`∀q≤|block s|, |dev(block_s.take q)| < ε·q + C s`), then
   EVERY prefix of the accumulated tail is good with accumulated slack. Induction:
   prefix lands in tail (IH) or reaches last block (whole-tail via
   `chainTail_dev_split_var` ⊕ block's own prefix bound, composed by
   `countOccurrences_append_addslack₂`). **The hdom-free replacement for
   `cfDiscLt_append_take`.** Settles the review's route-decisive question YES.
3. **`5fe8f09` — the full hdom-free limit** (`CFChainFreq`):
   - `chain_cf_digit_freq_tendsto_uniform`: window freq → γv. Decomposes
     `cfPref y p = w s₀ ++ (chainTail w s₀ (s+1)).take(p−L₀)` (via `chain_exists_stage`
     + `cfPref_take` + `w_eq_append_tail`), bounds the tail prefix by
     `chainTail_dev_prefix_var`, composes with the fixed short prefix `w s₀` via
     `addslack₂`. Hyps: `hblock` (uniform, margin→0) + `hslack` (`∑C=o(word)`).
   - `chain_orbit_equidist_uniform`: same orbit↔window bridge as `chain_orbit_equidist`,
     fed by the uniform limit → the `CFOrbitEquidist` payload per stream.

## NEXT — directive items 2 then 3 (do NOT rebuild item 1)

**The schedule now only needs to PRODUCE `hblock` + `hslack` per stream.**

2. **ψ-round `_uniform`**: rebuild `exists_freq_good_extend_affine_steer`
   (`CFScheduleA:1438`) to emit uniformly-good blocks by calling
   `exists_uniformly_freq_good_block_steer` (`CFScheduleA:1013`) for each stream.
   Choose `n₁,s ~ poly(1/δ_s)` (measure budget) and `m_s` so `n₁+m²` reaches the
   resolution length `~κ|w_s|` (use `exists_nat_goldenRatio_pow_gt` + the tight
   Binet bounds in `TBrickRefine`). **Route-decisive probe**: check the two budget
   inequalities (`(m+1)·A₁(n₁) < γ(target)` and `4/(d−c) < fib(...)²`) are
   JOINTLY satisfiable for `|w_s|` past a threshold (geometric beats poly). Then
   `hslack` (`∑_{i≤k}(C(s₀+i)+(|v|−1)) < ε·|w(s₀+k)|`, `C_s=4√|block_s|+2|v|+n₁,s`)
   follows from the geometric block growth — a `Filter.Tendsto` lemma.
3. **`SchedStateA`/`schedStepA`/`schedA` recursion** (mirror `CFSchedule.sched`)
   → two chains → `chain_orbit_equidist_uniform` both streams → assemble
   `exists_interleaved_affine_witness`. Gluing toolkit READY (`eq_of_mem_iInter_Icc`,
   `cfCylinder_chain_volume_tendsto`, `irrational_mem_Ioo_of_mem_iInter_cfCylinder`).

## Watch-outs
- ADDITIVE ONLY: never edit the existing `chain_cf_digit_freq_tendsto` /
  `chain_orbit_equidist` / `chainTail_dev_split*` or any B5′/locked decl; copy-extend.
- Re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` after schedule work
  (MUST stay trust-triple).
- `hslack` uses `|w(s₀+k)|` (word BEFORE the last block), NOT `|w(s₀+k+1)|` — the
  `+1` form is `≥ p` and points the wrong way. See PENDING_WORK top.
- `chainApp w s = w(s+1).drop|w s|`; the uniform block IS this appended word.
