# HANDOFF 2026-08-24 — B6 review lap + CRUX ADVANCES + route-decisive finding

**Branch/HEAD**: master @ `6913a7f`, `lake build` green (8757 jobs).
No uncommitted Lean edits (only untracked `CLAUDE.local.md`, expected).
Sole `src/` `sorry` = the B6 crux `exists_interleaved_affine_witness`
(`CFScheduleA.lean`, ~line 604). B5′ headlines trust-triple throughout.

## This session (review lap → crux drive), commits `32558a7..6913a7f`

1. **Review / PIVOT TO CRUX** (`32558a7`) — diagnosed crux-neglect (laps 11–21 =
   geometric atoms, crux untouched); reset `DIRECTION.md` CURRENT DIRECTIVE +
   STATUS + PENDING to build the frequency telescoping hardest-first.
2. **`chain_orbit_equidist`** (`7446822`, new `CFChainFreq.lean`, axiom-clean) —
   ABSTRACT generic-chain frequency telescoping: ports `CFCorrect.xstar_cf_freq_tendsto`
   to any nested genuine chain with two per-block hypotheses (`hgood` margin-good,
   `hdom` dominance). **The telescoping abstracts cleanly.**
3. **`affine_image_Ioo_subset_Icc_pre`** (`2afecc0`, axiom-clean) — the
   establishable-invariant image lemma (`cfCylinder wx ⊆ ψ⁻¹(Icc e f)`).
4. **`exists_freq_good_extend_affine`** (`c0a5241`, axiom-clean) — the ψ-ROUND
   STEP: maintains the interval invariant `cfCylinder wx ⊆ ψ⁻¹(Ioo e f)` through
   one joint refinement, producing freq-good extensions of BOTH streams + the new
   invariant + new wz-interval. The novel geometric heart of B6.
5. **ROUTE-DECISIVE FINDING** (`6913a7f`, docs) — see below.

## ⚠️ THE FINDING — read before touching the recursion
Wiring the round step into the telescoping is NOT "just assembly." Quantitatively:
to land `ψ(cfCylinder wx')` in the new z-cylinder `wz'` (width `~φ^{-2|wz'|}`),
`x` must refine to depth `~|wz'|`, forcing `~(z-payload)` NAVIGATION digits;
symmetrically for z. So **each round's filler ≈ the OTHER stream's payload**, an
irreducible Θ(payload) fraction of uncontrolled (non-freq-good) digits. Burying a
stream's filler needs its payload `≫` the other's → imbalance → the lagging
stream's filler blows up next round. `CFCorrect.cfDiscLt_short_append` requires
the filler to be `o(good mass)`, which Θ(payload) violates ⇒ frequency need not
converge. Full analysis + 3 candidate escapes in `PENDING_WORK.md` (top section).

## NEXT ACTION (per PENDING escape #2 — the route-decisive probe)
Build a **relative freq-good placement primitive**:
`exists_freq_good_extend_into_preimage` — extend a genuine word `wx` into
`ψ⁻¹(Ioo e' f')` (a preimage sub-interval of `cfCylinder wx`'s region) by a block
whose new digits are ALL freq-good (the navigation IS the payload, no uncontrolled
filler), with new-digit-count `≈` the relative depth `log_φ(width(cfCylinder wx)/
width(target))`. If provable, the interleaved schedule closes (fillers vanish);
if not, escalate toward escape #3 (natural-extension / measure argument, closer to
Vandehey's method) — write `ROUTE-ESCALATION-2026-08-25.md`.
**Do NOT build `SchedStateA`/`schedStepA` until #2 settles** — the recursion is
worthless if each round carries Θ(payload) uncontrolled filler.

## Assets ready (all axiom-clean, reusable regardless of route)
`CFChainFreq`: `chain_orbit_equidist`, `chain_cf_digit_freq_tendsto`, chain tail
machinery. `CFScheduleA`: `exists_freq_good_extend_affine` (ψ-round),
`affine_image_Ioo_subset_Icc_pre`, `exists_freq_good_extend_cfCylinder` (x-stage),
`exists_freq_good_block_in_Ioo` (interval engine), all L1–L3 atoms,
`irrational_mem_Ioo_of_mem_iInter_cfCylinder`, the limit toolkit
(`eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`).

## Faithfulness
All new decls additive; frozen B5′ modules unedited. After ANY schedule work
re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` — MUST stay
trust-triple. `DIRECTION.md` CURRENT DIRECTIVE governs (build the telescoping
contract; the finding is WITHIN its "if it does NOT feed cleanly, THAT is the real
crux — escalate" clause).
