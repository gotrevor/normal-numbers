# KICKOFF: the growing-prime localized logarithm `ζ_Y` (LAUNCHED 2026-10-02)

**Target.**  Prove `zetaY_isNormal` and `exists_unbounded_zetaY`
(`src/NormalNumbers/GrowingLocalizedLog.lean`).  Frozen byte-identical from the launch commit:
those two statements, `Retained`, `zetaY`, and all of `LiteratureVandeheyDifferencing.lean`
(the cited `VandeheyThm51`, numerically tripwired by `probes/vandehey_thm51_prop_check.py`).

**Why.**  An explicit normal constant with unbounded prime support: the first localized logarithm
whose prime set grows.  Paper: KB note `normal-numbers-localized-log-growing-primes-2026-09-16`,
audited and repaired in `docs/GROWING-PRIME-LOCALIZED-LOG-AUDIT-2026-10-02.md` (sound with two
repairs, 75%).  READ THE AUDIT FIRST: it supersedes the note on the segment cutoff
(`L₀ = N·exp(−(log log N)³)`, not `√N`) and on the differencing depth (choose `k` per segment via
Lemma 6.3; `k = π(Y)+5` is trivial everywhere).

**Route** (audit §6.3; state each as a named lemma, `sorry` allowed while in progress):
1. **N8 `korobov_uniform_saving` first** (the crux, the only place the claim can still die).  Its
   input `vandehey_optimal_range` (audit §6.2, the Lemma 5.4 closed forms + Lemma 6.3 window) must
   be PROVED here from `VandeheyThm51`, not assumed: real-number bookkeeping (Lemma 5.4's bounds on
   the recursion, Lemma 6.3's exponent table, `c ∈ (−1.1710, −1.1709)`).  N7 `log_M_le` via LTE.
2. N1-N6: retained count, tail, 2-adic cancellation, 3-adic exactness, denominator bounds, runs.
   Template for N3-N4: the `{2,3}` arithmetic in CaptainSude/xi-normality (reprove; never vendor).
3. N9 dyadic block Weyl sums `o(N)`, N10 via `equidistributed_of_weyl` (`WeylCriterion.lean`) and
   `isNormal_iff_equidistributed_orbit` (`Wall.lean`).
4. `exists_unbounded_zetaY`: any slowly growing `Y` (e.g. `Y n = max 3 (log log log n)`-ish).

**Stop rules.**  A step found FALSE: `Maze.lean` row aliased onto the refuting theorem, then stop
and say so.  A hypothesis of `zetaY_isNormal` that turns out insufficient is a false contract:
record it as an obstruction (standing rule 5), never weaken the frozen statement.

**Done when.**  `GrowingLocalizedLog.lean` sorry-free, axioms = trust base, in the root import,
STATUS/OVERVIEW/HEADLINES rows.

**Engine.**  Opus/low treadmill, review lap every 4 (the reviewer re-checks the audit's two
repairs against the Lean route).
