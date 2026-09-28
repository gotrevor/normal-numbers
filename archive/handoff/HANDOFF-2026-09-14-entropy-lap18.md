# HANDOFF — entropy lap 18 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `071a315`.  `lake build` green, **8957 jobs**.  All entropy
modules sorry-free and axiom-clean; preserved declarations re-checked.

## What was proved

`G4Entropy.forces_normal_iff_density_one` — **unconditional**:

> For every position set `S`: some *satisfiable* `S`-local hypothesis implies binary normality
> **iff** `S` has density one.

Lap 17 proved this with `∃ z ∈ [0,1), IsNormal 2 z` as a hypothesis (the backward direction
instantiates `P := IsNormal 2`, satisfiable only if a normal number exists in the unit
interval).  The repo already contains one: `isNormal_two_stoneham23` together with
`stoneham23_mem_Ico` — Stoneham's `α₂,₃`, binary normal, sorry-free, trust triple.
`exists_isNormal_mem_Ico` packages it; `Stoneham.lean` is imported, never edited.

## State of the expedition

Brief §6 is closed as a *characterization*, with no side conditions:

| the sample reads | verdict |
|---|---|
| density `< 1` | no digit-local hypothesis whatsoever can imply normality (lap 16) |
| density `1` | one can, and up to logical equivalence it is normality itself (laps 17–18) |
| implemented schedule: `≤ 1/4`; any admissible family over any scales: `≤ 1/8` | refuted |

## Next bounded test (unchanged, item 1 of `PENDING_WORK`)

The only room left is outside digit-locality.  `ZSample_eq_blockVal` is what makes every sample
statistic digit-local (the quantizer reads a finite window).  The bounded next step: define
`IsBlockLocal` and exhibit two reals with identical sampled blocks at every scale but different
values of the `G4Jackson` / `G4SeparatingTest` bounded-Lipschitz bump functional — i.e. prove
that functional is *not* block-local.  That names precisely what an entropy statement would have
to be about instead of `E0`.
