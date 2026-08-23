# PENDING WORK — hot-spot campaign (2026-08-23)

**Lap advance**: the crux `isNormal_of_visit_upper_bound` now has a concrete
elementary proof route (no Birkhoff needed — mathlib has none): sliding-window
subword statistics + Chebyshev over scale-K words.  `HotSpot.lean` holds the
proven counting core:
- `card_filter_div/mod/mod_div` (div/mod bijections), `card_filter_subword`,
  `card_filter_subword_pair` (= b^(K-k), b^(K-2k) exact counts),
- `sum_occCount` (first moment, exact), `sum_occCount_sq_le` (second moment),
- `card_badSet_le` (Chebyshev: T²·|Bad| ≤ 2kN·b^(K+k)).

**Blocker**: box lacks the v4.33.1 toolchain (see ON-LINE-REQUEST.md); repo
`lake build` impossible.  Everything above is compiler-verified against the
built v4.31.0 mathlib in `~/src/goodstein-ab-med` via
`scratchpad/check.sh` (LEAN_PATH trick, imports → Mathlib.Tactic).  Port risk
4.31→4.33 is small; re-verify in-repo when the toolchain lands.

**Next attack** (in order):
1. Orbit lemmas: `orbit_add` (u(j+i) = fract(u j·b^i)), cell membership of
   `⌊u j·b^K⌋₊`, subword localization (y ∈ cell(K,m) → fract(y·b^i) ∈
   cell(k, subword i m)).
2. Sliding double-count: N·A(n) − N(K−k) ≤ Σ_{j<n} occCount(M j) ≤ N·A(n) + N(K−k).
3. Bad-visit eventual bound from the hot-spot hypothesis at scale K
   (`eventually_all_finset` over `badSet`), then the ε-squeeze
   `tendsto_cell_of_visit_upper`, then `equidistributed_of_badic` + Wall.
4. Then the 6 counting sorries in Stoneham.lean (`stonehamState_*`,
   `card_units_Ico`, `segment_visit_upper`, final assembly).
