# HANDOFF — 2026-08-29 — B6 L4: `schedL4_block_linear` PROVED

**Branch:** `master`  **HEAD:** `030d8fb`  **Build:** 🟢 8757 jobs.
**Headline:** `exists_absolutely_normal_cf_normal_khinchin` still `[propext, Classical.choice,
Quot.sound]`.  New `schedL4_block_linear` same triple.
**Sole open `src/` sorry:** the DEAD two-stream `schedA_block_linear` (CFScheduleA.lean:4687),
excised once the L4 downstream lands `exists_interleaved_affine_witness`.

## What landed this session

The route-B block-linear crux is CLOSED. `schedL4_block_linear` (CFScheduleA.lean:4482):

    ∃ ρ ≥ 0, ∀ s, |chainApp (wxSeq_L4 hq hr) s| ≤ ρ · |wxSeq_L4 hq hr s|

sorry-free, axiom-clean. Two supporting lemmas added just above it:
- `poly_succ_le_two_pow` (4439): `(s+1)^k ≤ C·2^s`.
- `inner_bound` (4463): `2/(γtar·δ²/(2(Sg·γwx+γwx))) ≤ 16(Sg+1)/δ²` when `γtar ≥ ¼γwx`.

Assembly chain (all in the one proof): `block_len_le` → `2m²+7`; `StepSpecL4`'s m²-bound;
`Nfib ≲ |w|` via `logb_golden_sqrt_le`+`four_div_width_le_cfK`+`cfK_wxSeq_L4_le`;
`inner ≤ 8976(s+1)⁴` via `inner_bound`+`sum_gaussMeasure_wordFamily_le` (`|v|≤s`); everything
poly-in-`s` absorbed by `2^s ≤ |w_s|` (`wxSeq_L4_length_ge`) + `poly_succ_le_two_pow`.
Needs `set_option maxHeartbeats 1600000` (heavy context; `clear_value` on the measure defs +
`clear` of unused StepSpecL4 conjuncts keeps it tractable).

## NEXT (hardest-first): the L4 downstream wiring (all REUSE, no new hard math)

Mirror the two-stream `schedA_hfreq_x/z` path but single-stream:

1. **`chain_hfreq` for wxSeq_L4** via `chain_hfreq_of_uniform_blocks` (CFScheduleA:4480).
   Its three hyps for `w := wxSeq_L4 hq hr`:
   - `hext`: `wxSeq_L4_ext` (already proved).
   - `hgood`: from `StepSpecL4` — `s ≤ |blk|` (the `_hsdrop` conjunct), `n₁²≤|blk|√|blk|`,
     the freq conjunct.  Note `chainApp (wxSeq_L4) s = blk` definitionally (see the `show` in
     `schedL4_block_linear`).
   - `hgeom`: **`schedL4_block_linear` — just proved.**
2. Feed that into `chain_orbit_equidist_uniform` (HDOM-FREE, `CFChainFreq.lean:731`);
   the `slack_telescoping`/`chain_slack_littleO`/`blk→∞` sub-hyps are what
   `chain_hfreq_of_uniform_blocks` already discharges from `hgeom`.
3. z-side scale-coverage (`tendsto_of_scale_coverage` + brick-4a transfer lemmas) — copy from
   the `schedA_hfreq_z` construction.
4. Assemble the NEW single-stream `exists_interleaved_affine_witness`; the two-stream
   `schedA_block_linear` sorry then becomes dead and is deleted.

Check `interleaved_affine_target_not_always_nonempty` (4641 pre-splice; now shifted) is not a
blocker — it was the two-stream obstruction the L4 route sidesteps.

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` after any
  schedule wiring — MUST stay the trust triple.
- Fast check: scratch `.lean` importing `NormalNumbers.CFScheduleA`, `lake env lean <abs>` from
  project ROOT.  Working scratch this session:
  `…/scratchpad/L4Assembly.lean` (compiles clean standalone).
- DIRECTION.md governs.
