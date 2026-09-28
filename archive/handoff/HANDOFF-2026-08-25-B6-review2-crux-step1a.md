# HANDOFF — 2026-08-25 (review lap #2) — B6 crux step 1a landed

**Branch:** `master`  **HEAD:** `a92dd8c`  **Build:** 🟢 8757 jobs, clean tree.
**Headlines:** both B5′ (`exists_absolutely_normal_cf_normal` T1,
`..._khinchin` T2) = trust-triple `[propext, Classical.choice, Quot.sound]` — DONE (re-verified).
B6 `exists_cfNormal_and_affine_cfNormal` = `+ sorryAx`.
**`src/` open sorries (2):**
1. `variance_blockCount_psi_pushed` (`CFScheduleA.lean:4390`) — **THE crux** (ψ-pushed L² variance).
2. `schedA_block_linear` (`CFScheduleA.lean:5766`) — the DEAD two-stream sorry B6's `sorryAx`
   currently flows through; excise on L4 z-selector assembly. NOT to be attacked (dead route).

## This lap (review + one crux brick)

- **Review:** validated the direction as SOUND. The prior CURRENT DIRECTIVE was stale-in-a-good-way
  (its step 1 = ψ(xA) irrationality PROVED; steps 2–3 = Chebyshev/transfer COLLAPSED onto the single
  analytic crux). Rewrote `DIRECTION.md` CURRENT DIRECTIVE to mandate PROVING
  `variance_blockCount_psi_pushed`, decomposed (1) identity → (2) mixing → (3) assembly. Refreshed
  `STATUS.md` (ledger, where-it-stands, dated bullet). Directive history appended. `771250a`.
- **Crux step 1a LANDED (`a92dd8c`, axiom-clean):** the restricted ψ-pushed 2nd-moment IDENTITIES in
  `CFScheduleA.lean` just above the crux:
  - `integral_blockCount_psi_restricted`    : `∫_S (S_n∘ψ) dγ  = Σ_j γ(S ∩ ψ⁻¹T^{-j}A)`
  - `integral_blockCount_sq_psi_restricted` : `∫_S (S_n∘ψ)² dγ = Σ_{j,j'} γ(S ∩ (ψ⁻¹T^{-j}A ∩ ψ⁻¹T^{-j'}A))`
  + helpers `blockIndic_comp`, `measurable_affineMap`, `blockIndic_psi_mul`,
  `setIntegral_indicator_one_gaussMeasure`. Pure measure theory, mirrors `integral_blockCount{,_sq}`
  (`CFBlockFreq`). This reduces the crux to **bounding the pair-correlation masses** (the mixing).

## NEXT (hardest-first — see PENDING_WORK.md top for the full concrete reduction)

- **Step 1c FIRST (landable now, narrows the crux to exactly two statements):** reduce
  `variance_blockCount_psi_pushed` to two named ψ-conjugated interval-base mixing sub-sorries
  (1-point + 2-point) via `(S_n∘ψ−c)² = (S_n∘ψ)² − 2c(S_n∘ψ) + c²`, the two landed identities, and
  the geometric fold from `variance_blockCount_le`. Watch the extra 1-point correction term
  (`∫_S S_n∘ψ ≠ nγv·γ(S)` exactly here) and work out the 1-pt decay index (no `∸|v|` shift — affine
  base has no cylinder depth).
- **Step 1b (THE research core):** prove the two mixing sub-sorries. Route: change-of-variables
  `y=ψx` → interval-base (`J=ψ(cfCyl wx')`) pair-correlation in `γ` × bounded density ratio
  `ρ=gaussDensity(ψ⁻¹y)/(q·gaussDensity(y))` (elementary), then extend `gaussMeasure_cylinder_mixing`
  (`CFGammaMixing:236`) from cylinder base to subinterval `J`. Split further if big. Narrow, don't
  expect one-lap closure.
- **In parallel / after (reuse, not the crux):** wire `exists_scale_cfCylinder_psi_avoid_zbad_poly`
  + absolute transfer + `tendsto_of_scale_coverage` into `StepSpecL4` ⇒ `CFOrbitEquidist (ψ xA)`,
  assemble the NEW L4 `exists_interleaved_affine_witness`, excise `schedA_block_linear`.

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms` both B5′ headlines after any change (trust triple, else revert).
- NEVER drop the base-mass factor `γ(cfCyl wx')` from the crux RHS (its loss re-hits the
  density-vs-coverage wall, commit `5816044`).
- Uncommitted edits: NONE after the pending doc commit.
