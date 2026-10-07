# HANDOFF 2026-10-07 — c⋆ lap 13 (review lap, operator gate 2 rerun)
Branch `proof/uniformbad-threshold`, green (`lake build` full, 10809 jobs; barrier + maze audits pass).

## Done (all in Lean)
* `ninety_three_thirty_sevenths_le_cStar` PROVED (`UniformBadLowerBound.lean`): `93/37 ≤ c⋆`, 59-window
  cover (bases 2,3,5,10,17, n ≤ 18), axioms std only.  Located interval now `[93/37, 124/25]`.
* `CStarLeThirteenFifths` (open node, 60%): finite systems with all bases ≤ 3000 and windows ≥ 1e-13 are
  nonempty at c = 2.514–2.6; survivors near binary-periodic rationals; count grows with resolution.
* `not_perStageCert` PROVED (`UniformBadNineHalves.lean`, std + 3 native_decide): the per-stage counting
  engine (best ancestor and kill depth per base-3 stage) has no growth certificate through level 182 at
  c = 9/2, even with only bases 2, 3 and the first 40 levels at rate 2.
* Maze row "local per-window engines at c = 9/2" (wall, MazeAudit link); BarrierAudit crux text updated;
  frozen gate docstring: believed true 95%, no mechanism.

## Evidence for the stuck claim (probes in `scripts/cstar_models/`)
Per-stage Rosenfeld (`eng2.py`), Lebesgue precharge (`leb2.py`, `hyb.py`) and Parry-measure precharge
(`meas2.py`, `nupre.py`) all survive at c = 4.6 and die at 4.55.  Base-3 charges ×0.7 would rescue 4.5
(`eng5.py`); that cut needs knowing where base-3 windows fall in the alive set (exact {2,3} core),
and touching-kill box abstractions of that core collapse (`abs3.js`, bin error tripled per ternary
stage).  Gate stays frozen with its sorry.

## Next (operator's call)
`box stuck` called with this evidence (operator gate 2 fallback complete).  If reopened: (a) formal per-stage engine bank ≈ 4.6–4.7, or
(b) a non-local input for the exact {2,3} core (PENDING_WORK lap 13).
(c) the known long continuation: a containment-kill box abstraction of the exact {2,3} core at 9/2
(lap-4 `abs23.js` style, ternary threshold automaton for 0.0000120120…₃ instead of runs), pruned to
regular weights, with b ≥ 5 counted (lap 8: the true core plus counted b ≥ 5 already survives at 4.25).

HEAD at handoff: c26c676f (branch proof/uniformbad-threshold). Uncommitted: none (only scripts/cstar_models/__pycache__/, untracked). Stuck bail filed this lap.
