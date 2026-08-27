# Handoff: UniformTV.lean CLOSED — brief done

**Date**: 2026-08-27 · **Branch**: `wip/uniform-tv` · **HEAD**: `cfda2b5`

## Status: BRIEF-uniform-tv.md is fully satisfied

All three theorems in `src/NormalNumbers/UniformTV.lean` are proved,
sorry-free, and axiom-clean (`[propext, Classical.choice, Quot.sound]`):

- `isNormal_of_uniform_digitTV_pow`
- `isAbsolutelyNormal_of_uniformDigitTV`
- `exists_schedule_digitTV_tendsto_not_isNormal` — closed this session

`lake build NormalNumbers` (whole project) is green. `UniformTV` is now
imported from `src/NormalNumbers.lean`.

## What item 3 needed and how it closed

The guardrail theorem needed a real `x` and schedule `N : ℕ → ℕ` with
`N b / b → ∞`, `digitTV b x (N b) → 0`, and `¬ IsNormal 2 x`. Built via Baire
category, reusing existing machinery:

- `smallTVOpen b K : Set ℝ` — union over `p ≥ K` (`p > 0`) and `z : ℤ` of the
  open cylinder forcing digits `[p, p + b*p*p)` to spell the periodic block
  `0,1,…,b-1,0,1,…` (repeated `p` times). Shape copied from
  `NormalMeager.longZeroRunOpen` / `DisjunctiveBaire.orbitLiftOpen`, but with
  a nonzero target block `V(p) := blockNatVal b (periodicPattern b (p*p))`
  instead of an all-zero run.
- `isOpen_smallTVOpen`, `dense_smallTVOpen` — direct analogues of the
  existing density proofs (midpoint-in-target-interval argument).
- `exists_digitTV_le_of_mem_smallTVOpen` — membership derivation: uses
  `orbit_mem_Ioo_of_mem_lift` (from `DisjunctiveBaire`, no sign hypothesis)
  to land `orbit b x p` in the target interval, `digits_prefix_iff` (from
  `DigitInterval`) to read that off as a digit-prefix condition on the
  orbit point, `digitOf_orbit` (needs `0 ≤ x`) to shift back to digits of
  `x` itself, and `periodicPattern_getElem` to identify the block's digit
  values as `j % b`. Feeds straight into the already-proved
  `digitTV_le_periodic_sq`.
- Final assembly: `core := ⋂ b, ⋂ K, if 2 ≤ b then smallTVOpen b K else univ`
  is residual (`countable_iInter_mem` twice + `residual_of_dense_open`).
  Intersected with `{x | ¬ IsNormal 2 x}` (residual directly via
  `isMeagre_setOf_isNormal 2 (by norm_num)` unfolded through `IsMeagre`).
  `Dense.inter_open_nonempty` against `Set.Ioo 0 1` lands a witness `x` with
  `0 ≤ x` for free (sidesteps `digitOf_orbit`'s sign hypothesis) — this is
  the same trick the earlier handoff planned, and it worked as described.
  Schedule: for `b ≥ 2`, use `x ∈ smallTVOpen b b` (i.e. `K := b`) to get
  `p(b) ≥ b`; `N(b) := p(b) + b·p(b)²`. `p(b) ≥ b` gives both limits by a
  clean squeeze (`N(b)/b ≥ b·b`, `digitTV b x (N b) ≤ 2/b²`).

## Gotchas hit this session (add to future reference if useful)

- `Dense.inter_open_nonempty` / `dense_iff_inter_open` produce `U ∩ s`
  (open set **first**), not `s ∩ U` — got the `.1`/`.2` projections
  backwards on the first attempt; the error messages (wrong types on
  `hxcore`/`hxabn`) made the swap obvious once looked at directly.
- `obtain` against a nested `Eventually.and` (`(A.and B).and C`) needs the
  matching nested pattern `⟨p, ⟨hA, hB⟩, hC⟩`, not a flat 4-tuple.
- `(a+1)/c = a/c + 1/c` is not something bare `linarith` sees through (two
  different atoms syntactically) — needed `rw [add_div]` first, then
  `linarith` closes it.
- Field-free `set R := ... with hRdef` then applying a lemma that produces
  a *new* term still stated in the unfolded form (not folded through `R`)
  — don't reflexively `rw [hRdef]` afterward; check whether the goal
  already matches the unfolded form and `exact` directly.

## Next steps

None open in this file. If picking a new target in this repo, check
`PENDING_WORK.md` / `STATUS.md` for the next headline-adjacent obligation —
this brief's scope (`UniformTV.lean` only) is complete.
