# HANDOFF c3-mrt 2026-09-25 lap55 — the natural-density `D`-point rung, and the barrier NAMED

**New file** `src/NormalNumbers/C3MrtNatural.lean` (chain tip:
`lake build NormalNumbers.C3MrtNatural`, 8986 jobs).  Sorry-free, 3 declarations, trust triple.
`lake build` green (9257).

## The two obligations, named

* **`ProgressionLogRung K`** (obligation A, *bookkeeping*) — the `K`-fold assembly's log-averaged
  correlation bound, along the progression `M·X + r`.  `rung_multi_correlation` (lap 52) is exactly
  the case `M = 1, r = 0`; the general case is the same proof with the joint modulus `lcm(d)`
  replaced by `lcm(M, d)` through the truncation chain.  No new analytic input — but several
  files' worth of transcription, so it is named rather than inlined.
* **`LogToNaturalCorrelation K`** (obligation B, **THE BARRIER**) — log-averaged `o(log N)` control
  upgraded to natural-density `o(1)`.  Open already at `K = 2` for Liouville: this is
  *log-Chowla ⇏ Chowla*.

## The payoff

**`depthAvg_tendsto_of_transfer`** — granting A and B, for every FIXED depth `D`

    Tendsto (fun N => depthAvg b P Q j h D N) atTop (𝓝 0) ,

i.e. the twisted `D`-point depth average vanishes.  This is `depthAvg_one_tendsto`
(Selberg–Delange, `D = 1`) generalised to all `D`, and the **first natural-density multi-point
statement of the campaign**.  Mechanism: lap 54's
`norm_depthAvg_le_omega_progressions` bounds `‖depthAvg‖` by `M = Q·primorial P` class sums over
`N`; `filter_linear_lt_eq_range` identifies each class's index set with `range (progIdx M r N)`
(helpers `progIdx`, `progIdx_tendsto`, `progIdx_le`, `progIdx_pos`); B gives `‖S r J‖/J → 0` and
`progIdx M r N ≤ N` converts that to `‖S r (progIdx M r N)‖/N → 0`; a finite sum of `M` null
sequences and `squeeze_zero_norm'` finish.

## Where the ledger stands — the equivalence is in view

`ConjC3`'s `D ≥ 2` route now rests on, and ONLY on:

1. `KPointLogElliott K` = Tao–Teräväinen's product log-Elliott (**published**);
2. `TwistedPrimeSumSavingAllLevels` (the Vinogradov–Korobov-type input);
3. `ProgressionLogRung K` — transcription of 1 along a progression (bookkeeping);
4. **`LogToNaturalCorrelation K` — the log-Chowla ⇏ Chowla barrier (named open problem)**;
5. uniformity in `D` along the schedule `D = D_N ≍ log log log N`, quantified by
   `QuantDepthElliottGen` / `budget_absorb`, needing `η N ≤ exp(−C(log log log N)⁴)` (lap 40).

Nothing else.  Items 3 and 5 are quantitative/bookkeeping; item 4 is the equivalence the ratified
success criterion asks for.

## NEXT

Two independent threads, either is a good lap:

* **(a) Discharge obligation A.**  Carry a fixed extra modulus `M` through
  `C3MrtMultiLinear` → `C3MrtMultiMass` → `C3MrtMultiTrunc` → `C3MrtMultiTupleMass` →
  `C3MrtMultiInner` → `C3MrtMultiChase`.  The single structural change is `Finset.univ.lcm d ↦
  Nat.lcm M (Finset.univ.lcm d)`; `joint_class_multi` already takes an arbitrary modulus list, and
  `prod_le_lcm_mul_pow` is unaffected (it bounds `∏ d_i / lcm`, and `M` only enlarges the lcm,
  which *helps*).  Start with `inner_sum_multi_forms`.
* **(b) Make the `D`-uniform statement.**  Restate `depthAvg_tendsto_of_transfer` with explicit
  rates so it can feed `weylLambertTwist_of_kfold_bound`: obligations A and B both need to be
  quantitative (`η`-shaped) versions.  Lap 40 pins the required `η`.
