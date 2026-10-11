# HANDOFF 2026-10-11: operator lever probe (L1, L2) - KILL

Branch `proof/uniformbad-threshold`.  Script-only probe on top of `tail5_refined.py` (i)+(ii)+(iii); close threshold 0.9.
- Controls: refined screen 1.391; L2 machinery with beta = 0 reproduces 1.384 (per-ancestor data, levels <= 26).
  Drop bases 5-7 (0.695), zero tail and kill-all (1.584) as in the relaunch (`refined_screen.txt`).
- (L2) mass charging (`tail5_lever_data.py 26`, `tail5_lever.py 300 100 L2`, output `tail5_out/lever_screen.txt`):
  charge beta * (ancestor weight or depth-j descendant mass) plus K * max_a (s_a - beta D_j(a))^+.  Certified gap
  **1.2552** (design 1.334 at gamma 24.29).  Why it fails: the worst descendant run sums sit under WEIGHT-ZERO core-alive
  ancestors, and charging deeper costs gamma^j.
- (L1) lag-dependent K: no sound formulation found.  Optimistic floor K_l = 1 for l >= 2 (`tail5_lever_l1.py`,
  `lever_l1.txt`) gives 0.705, so L1 is not refuted; it needs a certified K <= 1.4 at lags >= 2 (vs 2.32).
- Lean: `UniformBadTailCounting.lean` (`MassChargingScreenMisses`, `LagTwoComparability`, `lagTwoK_threshold`);
  Maze row "Refined counting screen..." updated.  The improved coefficients are not added to `CountingScreenMisses`,
  because L2's 1.255 is a different (lower) margin and is recorded in its own node.
- NEXT: operator.  Fallback (a) runs separately; it was not started here.  The one live counting lever is a provable
  comparability with K <= 7/5 for the survivors relevant at lags >= 2.
