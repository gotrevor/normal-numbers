# HANDOFF — 2026-08-25 (review lap #2b) — B6 ROUTE PIVOT to the measure argument

**Branch:** `master`  **HEAD:** `59a04e6` (+ this doc commit).  **Build:** 🟢 8757, clean tree.
**Headlines:** both B5′ = trust-triple (DONE). B6 `exists_cfNormal_and_affine_cfNormal` = `+sorryAx`.

## The finding that changed the route

`variance_blockCount_psi_pushed` (`CFScheduleA.lean:4390`, the mandated schedule crux) is
**PROVABLY FALSE** — full counterexample in `OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md`.
Short version: for `v=[1]` and a deep `wx'` with `ψ(cfCyl wx')⊆cfCyl[2,…,2]`, the pushed block
count is `≡0` at scales `n≤|wx'|`, so `∫_{cfCyl wx'}(…)²dγ = n²γv²γ(wx')` exceeds the claimed
`88·n·γv·γ(wx')` once `n>212`. Root cause: a deep cylinder is a tiny interval ⇒ `blockCount n(ψ·)`
is near-CONSTANT over it for `n≲|wx'|` at an affine-handed value ≠ `nγv` ⇒ 2nd moment `Θ(n²)`. Both
schedule z-routes are therefore dead (two-stream super-exp; single-stream refuted). Pre-registered
escalation taken (`ROUTE-ESCALATION-2026-08-25.md`).

## The route now (DIRECTION.md CURRENT DIRECTIVE governs — obey it)

B6's stated theorem is bare EXISTENCE, trivially true a.e. Prove it by measure, in a NEW file
`src/NormalNumbers/CFAeNormal.lean`:
1. **`ae_isCFNormal` — the new crux.** `∀ᵐ y ∂gaussMeasure, IsCFNormal y`. L²→a.e.:
   `variance_blockCount_le` (`CFBlockFreq:401`) + Chebyshev ⇒ per-word tail `≤ (8|v|+80)γv/(δ²p)`;
   Borel–Cantelli on `p=k²` (summable) + monotone squeeze on gaps ⇒ a.e. `blockCount(cfCyl v) p·/p→γv`;
   intersect over countable valid `v` + a.e. orbit-in-`(0,1)` ⇒ `isCFNormal_of_orbit_freq`
   (`CFOrbitFreq:34`). Birkhoff-FREE.
2. **`ae_isCFNormal_affine`.** `∀ᵐ x, IsCFNormal(ψx)`: `{IsCFNormal∘ψ}=ψ⁻¹{IsCFNormal}`, complement
   `=ψ⁻¹(null)`; `volume_preimage_affineMap` (`CFAffine:94`) + `γ≈volume` bounded-density ⇒ co-null.
3. **Assemble** `exists_cfNormal_and_affine_cfNormal` (feasible branch): two co-null sets on
   `(0,1)∩ψ⁻¹(0,1)` meet ⇒ witness. Integer-shift reduction for `r∉(-q,1)` already present.

**Suggested first probe (de-risk):** stub `ae_isCFNormal` + `ae_isCFNormal_affine` as `sorry`, prove
the co-null-intersection ASSEMBLY (step 3) and wire it into the feasible branch of
`exists_cfNormal_and_affine_cfNormal`. If that compiles, B6 reduces cleanly to the two a.e. sorries;
then grind `ae_isCFNormal` (the one real lemma). Then B6 is `sorryAx`-free.

## FORBIDDEN (see directive)
Do NOT try to prove `variance_blockCount_psi_pushed` / `psi_pushed_*` / `_poly` / conditional-`wz`
(FALSE or rest on it); do NOT grind the two-stream `schedA_block_linear` or the schedule
`exists_interleaved_affine_witness` (obstructed, explicit-witness route retired); do NOT DELETE
them (marked REFUTED, kept in `src`); do NOT chase an explicit witness (not required, obstructed).

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms` both B5′ headlines after any change (trust triple, else revert).
- The restricted 2nd-moment identities (`integral_blockCount_{,sq}_psi_restricted`, `a92dd8c`) are
  TRUE + axiom-clean but now off-path; harmless, keep.
