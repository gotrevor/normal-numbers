# HANDOFF — 2026-08-28 — B6 measure-budget obstruction + cfK/shift infrastructure

**Branch:** `master`  **HEAD:** `f3cbe5b`  **Build:** 🟢 8757 jobs, clean tree.
**B5′ headlines:** both re-verified trust-triple `[propext, Classical.choice,
Quot.sound]` (`exists_absolutely_normal_cf_normal`,
`exists_absolutely_normal_cf_normal_khinchin`).

## The one thing to read first

`OBSTRUCTION-2026-08-28-block-measure-budget.md` — the session's headline finding.
**The B6 crux `schedA_block_linear` is NOT provable with the current two-stream
construction**, and the failure is deeper than cfK: the freq-good *measure budget*
`n₁ ≳ 1/ρ` blows up because the x-block target relative size
`ρ = μ(target)/μ(cfCylinder wx) ≈ e^{−2κ|zblock|}` is exponentially small (coupled
stream is one full block deeper). `n₁` sits inside the per-block slack `C_s`, so
`chain_cf_digit_freq_tendsto_uniform`'s `hslack` fails independently of the length
bound. Verified against the code. **This needs an attended review to sanction the
proposed single-stream pivot** (select `x` avoiding both x-bad-zones and the
ψ-pullback `ψ⁻¹(cfBadZone_z …)`; target becomes the full cylinder, `ρ=1`, blocks
linear). DIRECTION mandates the two-stream route, so a grind lap must not just
switch — hence the escalation.

## Two open `src/` sorries (both in `CFScheduleA.lean`)

1. **`schedA_block_linear` (:2537)** — the crux; blocked pending the pivot review
   (see obstruction doc). Do NOT grind it under the current construction.
2. **`TODO(shift)` (:2828)** — `exists_cfNormal_and_affine_cfNormal` general-`r`
   branch. **This is the productive next target** (independent of the crux route).

## What landed this session (all axiom-clean, reusable)

The cfK-controlled-steering infrastructure (correct route, superseding the
refuted digit-cap): `exists_fib_threshold_linear_of_cfK`,
`frac_mass_bad_extensions`, `cfKbadExtSet` + `volume_cfKbadExtSet` +
`measurableSet_cfKbadExtSet` + `exists_rate_gaussMeasure_cfKbadExtSet_le`
(`CFDigitLaw.lean`), `exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` +
`exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo` (`CFScheduleA.lean`).
These fix the *resolution* cost but NOT the measure-budget blowup — keep them;
they are reusable regardless of the pivot.

Item-2 core: **`cfFreq_tendsto_of_digit_shift`** (`CFScheduleA.lean`) — CF window
frequency is invariant under a fixed digit shift `d'(k+m)=d k`.

## Next steps (priority order)

1. **Finish item 2 (`TODO(shift)`)** — the doable target. Prove the elementary
   orbit fact `cfDigit (y+n) 0 = 0`, `cfDigit (y+n) 1 = n`,
   `cfDigit (y+n) (k+2) = cfDigit y k` for `y ∈ (0,1)` irrational, `n ≥ 1`
   (`gaussMap`/`Int.fract`/`cfDigit` in `CFDefs.lean`; `g(y+n)=1/(n+y)`,
   `g²(y+n)=y`). Then `IsCFNormal (y+n)` from `IsCFNormal y` via
   `cfFreq_tendsto_of_digit_shift` (m=2). Wire into the shift branch: pick integer
   `n` with `r−n ∈ (−q,1)`, feasible witness at `r₀=r−n`, shift `ψ(x)=(qx+r₀)+n`.
   **Caveat:** covers the `r ≥ 1` half (n ≥ 1). The `r ≤ −q` half gives `n ≤ −1`,
   `qx+r < 0` — needs a negative-shift orbit fact OR choosing `x` in a higher unit
   interval so `qx+r ∈ (0,1)`. Details in `PENDING_WORK.md`.
2. **Crux: await/execute the pivot** — a review lap ratifies the single-stream
   route (obstruction doc §"Proposed pivot"); then build the ψ-pullback bad-zone
   and its distortion measure bound, reusing W1–W5 Chebyshev machinery.

## Notes

- Aristotle can't take the shift lemma cleanly (custom `cfDigit`/`IsCFNormal`
  defs, not mathlib) — prove locally.
- DIRECTION.md CURRENT DIRECTIVE still names the digit-cap route (refuted this
  session) and the two-stream construction (obstructed this session); an altitude
  lap should refresh it per the two findings. Do NOT edit DIRECTION from a grind
  lap.
