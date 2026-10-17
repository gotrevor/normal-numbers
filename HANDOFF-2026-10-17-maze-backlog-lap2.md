# Maze backlog lap 2 — universal density product block refuted (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-16-maze-backlog.md` in order.  Part 1 was already complete.  This lap
completed Part 2, including its theorem, reopen condition, Maze row, and declaration audit.
Part 3's two Bailey--Borwein boundary witnesses remain, so the kickoff's terminal condition has
not yet been reached.

## Concrete advance

- Added `NormalNumbers.MahlerDensityProduct` with the frozen predicate
  `Mahler.IsDensityProductBlock` exactly in the kickoff's positive-lower-density form.
- Proved `Mahler.not_forall_isDensityProductBlock`: for every finite multiplier set `S`, the
  single irrational witness `Mahler.bgLiouville 3 0 1` defeats `S`.
- Strengthened the existing orbit localization internally as
  `Mahler.orbit_bg_mem_with_distance`, retaining the old `orbit_bg_mem` statement as a wrapper.
  The strengthened result exposes the factorial interval and distance to its right endpoint.
- Proved that, for each positive multiplier `m`, digit `1` is zero on
  `[j!, (j+1)!-(m+1))` once `j >= m+3`.  At the prefix
  `q_j = (j+1)!-(m+1)`, the number of digit-`1` occurrences is at most `j!`, hence its frequency
  is at most `1/j`.  The `m = 0` channel is handled directly.  The real-valued `liminf` proof
  supplies explicit boundedness and coboundedness witnesses and concludes `liminf <= 0`.
- Added `Mahler.DensityProductBlockExponentTwo` as the explicit reopen condition: a finite
  ternary multiplier set working after restriction to irrationality exponent two.
- Added the `.wall/.kernel` Maze row "positive-frequency product block, universal", its audit
  link, and root imports.  `#maze_audit` now reports 196 rows, 89 declaration-backed links, and
  107 legacy prose rows.

No new `sorry` was introduced.  Both new proved declarations checked below depend only on Lean's
standard trust baseline: `propext`, `Classical.choice`, and `Quot.sound`.

## Verification

Narrow checks:

```text
lake build NormalNumbers.MahlerLowerBoundBackground
lake build NormalNumbers.MahlerDensityProduct
lake build NormalNumbers.MazeAudit
```

All completed successfully.  The real gate was:

```text
~/personal/bin/lean-green ~/src/nn-maze-backlog \
  --target NormalNumbers.MazeAudit \
  --axioms NormalNumbers.Mahler.not_forall_isDensityProductBlock \
  --axioms NormalNumbers.Mahler.orbit_bg_mem_with_distance \
  --import NormalNumbers.Maze
```

Verdict: `FORMALIZE-TIER GREEN`; `NormalNumbers.MazeAudit` completed at 10466 jobs.  Both axiom
reports were exactly `[Classical.choice, Quot.sound, propext]`.

## Current crux and next attack

Part 3 is next, beginning with L1 in `StonehamSumsBoundary.lean`:

```text
not_isSimplyNormal_stoneham_sub_succ_mul
```

Pair the odd Stoneham term `j` with the following even term to prove

```text
alpha_{b,p} - (p+1) alpha_{b,p^2}
  = sum_{j odd} b^(-p^(j+1)) * ((b^((p-1)*p^j)-1)/p^j).
```

Fermat plus LTE gives integrality of each displayed block.  The blocks occupy the base-`b`
places through `p^(j+1)`, while the next odd block starts after `p^(j+2)`, giving zero windows
at 0-indexed positions `[p^(j+1), p^(j+2))`.  Port the head/tail and frequency contradiction
from `StonehamSums.digitOf_stoneham_sum_eq_zero` and
`not_isSimplyNormal_stoneham_sum`.  After L1, L2 uses the same template with
`Phi_6(3^(7^k))/7^k` and zero windows `[3*7^k, 7^(k+1))`.  The load-bearing first lemma is the
general divisibility `p^j | b^((p-1)*p^j)-1`; prove and kernel-check that before copying the
analytic tail bookkeeping.
