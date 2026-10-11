# Gate 6 lap 2 (2026-10-11): wiring PROVED; exact {2,3,5} core in progress

Branch proof/uniformbad-threshold. Binding: DIRECTION.md gate 6 (Codex review PASSED).

## Done
- `Fold.tailBudgetSuffices449F` proved (std axioms; waiver removed from BarrierAudit); `WeightedCore449F` docstring fixed.
- `Fold.Good5` (core good cells over {2,3,5}) and `Fold.good5_alive` proved.
- Gate-4 headroom: exact3 certifies 181/100 (weights `scripts/cstar_models/gate6/W181_N128_M24_D6.txt.gz`), NOT 91/50.

## Core certificate search (scripts/cstar_models/gate6/)
- exact35.c (full 4-D joint B&B): too slow.  exact5t.c (pure product W3*PHI): PHI collapses (joint-death pairs, 0.36%).
- exact5x.c (product + sparse exceptions): pass 0 -> 69 PHI zeros, 41k exceptions, but ~1h/pass.
- exact5r.c / exact5k.c (decoupled run-sum adversary, concentration classes): DEAD (refuted numerically, PENDING_WORK).
- exact5y.c: per-pair + exceptions + threshold-aligned base-5 rho bins (slivers; `>=` fix for the unresolved test) +
  clean-root classes.  RUNNING at handoff: `MAXB5=20 /tmp/exact5y 128 24 6 0 6 16 /tmp/W181.txt 60 15 /tmp/PHI_y.txt`
  log /tmp/e5y.txt (lost on box restart; rerun with W181 gunzipped to /tmp/W181.txt).

## Next
1. Watch exact5y convergence (failing pairs / exceptions / zeros per pass).  If it converges: freeze W = W3*PHI (+E),
   write the read-only checker + Lean checker (keep ints < 2^63 so Lean Int stays scalar), Codex review via ON-LINE-REQUEST.md.
2. If it stalls: measure where (state, x5 near 0), consider N5=128 or MAXB5 up.
3. Tail (`TailChargeBudget449F`) is the real crux after the core: counting scheme with uniform finite-state run sums.
