# HANDOFF 2026-09-25 session 6 — the URM route refuted-and-repaired, four of five steps proved

* **Branch** `wip/c3-mrt` · **HEAD** `147a452` · working tree **clean** · `lake build` **green**
  (9445 jobs) · no uncommitted edits.
* Commits this session: `2fc0435`, `7224ea5`, `a6e2801`, `7b2d726`, `44f4f5e`, `626f974`,
  `0d617fe`, `96b2d65`, `61a6997`, `7da2565`, `147a452`.

## 0. The operator's restatement objective was ALREADY DONE

The run was launched for the TT-interface restatement items (a)-(c).  `DIRECTION.md`'s HALT block
already recorded those as done (`25149e0`, `3a7e84a`).  Re-audited at HEAD rather than redone:
`lake build` green, `#print axioms` clean on all twelve names of that surface (defect theorems,
restated `Prop`s, non-vacuity guards, `Maze.lean` aliases), SURVIVORS table verified.  Recorded in
`HANDOFF-2026-09-25-tt-interface-restated.md` (`2fc0435`, `7224ea5`).  **Do not redo it.**  It was
a bounded objective, so the repo-wide self-stop gate correctly declines `box done`; such a run
wants `--done-when 'sorry-free:<target>'`.

## 1. DIRECTION ②.3 — the `t = 0` conductor debt (2 of 5 steps proved)

`src/NormalNumbers/C3MrtCharSumZero.lean`, sorry-free, axiom-clean.

* Head discharged: `norm_charHeadSum_le` — `‖∑_{p ≤ q} conj(χ(p))/p‖ ≤ log(q+2) + mertensBound`,
  really `O(log log q)`, a whole exponential *below* budget.  The head can never obstruct.
* `charPrimeSumLogQZero_of_tail` gives the whole `t = 0` slice with `D = C+1+mertensBound` from one
  input `CharTailCancellation C` (cancellation over `q < p ≤ X²` — Siegel-free `L(1,χ) ≫ q^{-1/2}`
  in strength).  GUARD RULE fully discharged (content locator + empty/singleton/constant verdicts);
  the lap-115 singleton failure mode is proved *structurally absent* (bound additive in the mass,
  not multiplicative in a saving).
* Step 2 of the attack proved: `primePower_tail_le_one` — `∑_{p∈P} ∑_{k∈Ico 2 N} 1/(k p^k) ≤ 1`
  absolutely, via `primePower_inner_le` and `prime_inv_sq_sum_le_one` (telescope, no `ζ(2)`).
* **Tolerance SETTLED** (`44f4f5e`): `nonPrincipalTwistSmall_zero` proves `κ = 0` holds OUTRIGHT
  (`≤ log log X + log 3 + mertensBound`, triangle inequality only).  With
  `nonPrincipalTwistSmall_of_logQBound` (`κ = 1−2D/125`, `D < 62.5`) this shows **nothing weaker
  than `O(log q)` can serve** while the constant is generous.  "Find a cheaper archimedean input"
  is closed off as a route.
* Still open: steps 3-5 (Euler product; `L(1,χ) ≫ q^{-1/2}`; winding number of `arg L`).  Needs
  Dirichlet L-function analytic theory; mathlib has only the qualitative
  `DirichletCharacter.LFunction_apply_one_ne_zero`.

## 2. DIRECTION ②.4 — `UniformResonantMass`: 4 of 5 steps PROVED

`src/NormalNumbers/C3MrtURMLowHigh.lean`.  **`C3MrtWindowMass`'s own sketched plan does not
close** — its `sum_exp_neg_le` docstring commits to an error tail of `1 + 32|t|/π = O(|t|)`, while
`UniformResonantMass` allows `100δ(log log Y + log(2+|t|)) + C` with `C` chosen *before* `t`.  Same
failure mode as laps 102/115, caught before entering the chain.

**Repair:** split at a height that GROWS, `lowHeight t = 16 · log(2+|t|)`.  The `16` is forced:
the effective start `aWin = max((γ_m−δ)/|t|, lowHeight t)` dominates the *average* of its two
bounds, and `max ≥ average` costs a factor `2`; at `8` the surviving factor is `(2+|t|)^{-1/2}`,
too weak to beat the `O(|t|)` window count.

Proved, all axiom-clean: `lowResonantMass_le`, `exp_neg_lowHeight`, `log_le_eps_mul`,
`log_lowHeight_le`, `resonantMass_eq_low_add_high`, `highResonantMass_eq_sum_windows`,
`highResonantMass_eq_zero`, `resWindowCount_le`, `log_resWindowCount_le`, `aWin_*`,
`windowMass_le`, `windowMass_main_le`, `gapMaj*`, `main_term_le_gapMaj`,
`range_succ_eq_insert_Icc`, `main_sum_le`, `aWin_ge_avg`, `err_term_le`, `exp_neg_gWin_le`,
`err_sum_le`, and the assembly **`highResonantMass_le_wide`**.

## NEXT STEP — the single open leaf

`highResonantMass_le_narrow` (`src/NormalNumbers/C3MrtURMLowHigh.lean`, the only `sorry` in the
file): the case `|t| < 2δ`.  Windows exceed a unit in `log p`, so `resonant_window_mass_le`'s
`2δ ≤ |t|` hypothesis fails and Brun–Titchmarsh does not apply.  Plan:

1. Per window, use the two-sided Mertens already in the Erdős67b port,
   `Erdos67b.PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add`, giving
   `log((γ_m+δ)/(γ_m−δ)) + 2·mertensBound ≤ 2δ/(γ_m−δ) + 2·mertensBound`.
2. The main terms sum by the SAME `main_sum_le` (it is stated on `16δ/(γ_m−δ)`, so `2δ/(γ_m−δ)`
   is covered with room to spare).
3. **The care point:** the per-window additive `2·mertensBound` must not be charged `K` times —
   `K` can be `O_δ(log Y)`, which would give `O(log Y)`, far over budget.  Group windows (dyadic
   in the height `a`) so the additive constant is paid once per block, or find a union-of-intervals
   Mertens bound.  This is the one genuinely unfinished piece of ②.4.

Then `uniformResonantMass_of_high` closes `UniformResonantMass` outright, discharging the route's
oldest standing analytic input.  Full 5-step ledgers for both ②.3 and ②.4 are in
`PENDING_WORK.md`.

**Forbidden drift unchanged** (see `DIRECTION.md` ①/②): do not re-attempt `WideBlockSaving` /
`WideBlockPartial` / `BlockPhasePairing`, do not delete refuted statements or their implications,
and honour the GUARD RULE on any new `Prop`.
