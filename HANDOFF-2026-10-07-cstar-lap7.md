# HANDOFF 2026-10-07 — c⋆ lap 7 (review lap)

Branch `proof/uniformbad-threshold`.  Build green (10804 jobs; use `taskset -c 0-5 lake build` — a
wide build hits the box's spurious "Too many open files").

## Review verdict
* **Newhouse thick core: no adaptive escape** (proved, `UniformBadNewhouse.lean`):
  `merge_forced`, `windows_merge_forced`, `window`, `window_disjoint`, `exists_gap_of_Ioo`.  Any
  `τ`-thick `B ⊆ ⋂_{b≥3} E_b(c)` puts every pair of `τ`-close windows inside its hull into one gap, so
  `ThickCore c τ` ⟺ the canonical `τ`-merge closure stays local.  Lap 6's plan (flipped SplitCore,
  discard clusters) cannot work.  Maze row "adaptive split cores for the Newhouse thick core".
* Both known `c ≤ 4` mechanisms are walls (Newhouse: cross-base cluster locality; counting: weight-regular
  exact `{2,3}` core with growth ≥ 1.78).
* **`c⋆ ≤ 5` is bankable**: frozen `UniformBadFive.cStar_le_five` (90%), probe
  `scripts/cstar_models/lvl5c.js` / `pess.js`, pessimistic slack 0.019, control `c = 6` slack 0.21.
* DIRECTION CURRENT DIRECTIVE (branch section) rewritten; STATUS refreshed.

## Next (directive order)
1. Decisive `c = 4` counting probe (exact joint `{2,3}` system, threshold pruning, weight spread,
   worst weight-aware `b ≥ 5` charge).  Record verdict as a node or Maze row.
2. Formalize `cStar_le_five` (plan in `PENDING_WORK.md` lap 7 entry and the `UniformBadFive` docstring).

## Checkpoint
* HEAD `c504ec79` (review commit) + this note.  Tree clean apart from the old untracked probes
  (`scripts/cstar_models/__pycache__/`, `kreg_meet.js`, `mureg.js`, `psi.js`), left as found.
* Scratch probes for `c = 5` are committed as `scripts/cstar_models/lvl5c.js` (true pattern) and
  `pess.js` (worst-case counts per window).  Run: `node scripts/cstar_models/pess.js 5 5`.
* No proof work in flight.  `UniformBadFive.cStar_le_five` is a single disclosed `sorry` (waived in
  BarrierAudit); the formalization starts from `UniformBadCount`'s `bad6` pipeline.
