# HANDOFF 2026-10-07 — c⋆ lap 5 (Newhouse route)

Branch `proof/uniformbad-threshold`, HEAD `086edde1` + this file. Tree clean.

## Done this lap (4 + 5)
* `UniformBadJoint.lean`: `exists_good_of_subEigen` (proved), node `jointCoreSubEigen_four` (80%).
  Counting route for b ≥ 5 at c=4 recorded as a Maze wall (linked).
* **New route** `UniformBadNewhouse.lean`: `cStar_le_four_of_newhouse` PROVED from three nodes:
  - `gap_lemma` (Newhouse, classical; Palis–Takens sketch in docstring) — sorry 95%
  - `e2_four_facts` (E₂(4) compact, hull [1/15,14/15], gaps ≤ 1/15, thickness 3) — sorry 90%
  - crux `thickCore_four : ThickCore 4 (2/5)` — sorry 70%
  Probes `scripts/cstar_models/thick.py`, `merge.py` (merging near-touching windows costs ~100
  merges; c=3 plausible too; c=2.2/2.4 control collapses).
* ON-LINE-REQUEST: Hunt–Kan–Yorke + thickness survey (2212.02023) statements.

## Next (in order)
1. Prove `gap_lemma` in Lean (linked-pair descent + compactness; gap lengths ≥ ε are finite).
2. Prove `e2_four_facts` (gaps A/2ⁿ ± 2⁻ⁿ/15; bridge arithmetic with 2^j mod 15).
3. Crux: B = E₃(4) (τ=26) with b ≥ 5 windows absorbed; state a cascade-bound node, then prove.
Then the headline `cStar_le_four` in UniformBadThreshold.lean can be closed only after moving the
wiring (Threshold cannot import Newhouse: restructure so Newhouse imports only UniformBad + defs,
or re-prove headline there and keep Threshold's statement — decide then; never weaken it).
