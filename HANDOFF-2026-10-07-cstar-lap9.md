# HANDOFF 2026-10-07 — c⋆ lap 9

Branch `proof/uniformbad-threshold`, green.
## Done
* `five_halves_le_cStar` PROVED (29-window cert `cert52`; greedy fails at 2.51).
* Probe: exact {2,3,5,6,7} core at c=4 grows 1.815; b≥10 counted survives at 4x charges; lookahead-pruned
  core is closed (every kept cell keeps a child, mean 1.80–1.81). Recorded in SmallBaseTreeCore docstring + Maze row.
## Blocker (strike 2)
`cStar_le_four` needs bases 3 and 5 handled exactly, and no finite certificate covers that: the joint phases are irrational,
and the lap-8 Maze row shows that counting them fails at c = 4. The run's scope forbids `cStar_le_five`.
Ask: rescope the run to `sorry-free:UniformBadFive.lean`, or supply a mechanism for an exact multi-base core.
