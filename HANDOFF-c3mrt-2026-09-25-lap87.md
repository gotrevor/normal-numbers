# HANDOFF c3-mrt 2026-09-25 lap87 — REVIEW lap: the budget is vacuous, the target is the DIAGONAL

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (OUTRANKS this file).  Then
`PENDING_WORK.md` → "Review — lap 87".  Branch `wip/c3-mrt`, tree clean.
Tip: `NormalNumbers.C3MrtUnifK`.

    lake build                            # 9257 jobs, green
    lake build NormalNumbers.C3MrtUnifK   # 9005 jobs, green

Chain: `… → C3MrtKPointNoExc → C3MrtQuantKPoint → C3MrtUnifK` (+ `C3MrtBudget`).

## What this lap found (and why it changed the plan)

**F1 — the budget layer is vacuous.**  `QuantDepthElliottGen b` asks for `C η` with
`‖depthAvg b P Q j h D N‖ ≤ C D · η N` for ALL `D`, plus `C(depthLL b N)·η(N) → 0`.
Instantiate at `D = depthLL b N`:  `C(depthLL b N)·η(N) ≥ ‖depthAvg … (depthLL b N) N‖`.
So *every* budget already forces the DIAGONAL limit — the one thing
`weylLambertTwist_of_depthElliottLL` consumes.  `budget_absorb`, `pow_self_sq_le_exp_cube` and
the `sup_D` assembly of lap 86's NEXT ③ are bookkeeping around a `Prop` no weaker than the
target.  **Now a theorem:** `quantDepthElliottGen_forces_diagonal`.

**F2 — fixed-`K` limits are the end of their line.**  `depthAvg_K_tendsto_of_noExc` (lap 85) is
one limit per `K`; a family of limits has no diagonal along a growing index without uniformity,
and `KPointNaturalCorrelationNoExc K` hides `c, Cst` behind a per-`K` `∃` with no control on
their degradation.  So the input must name them.  **Now in place:** `KPointNoExcWith cK CstK K`,
`kPointNoExc_of_with` (nothing weakened), `exists_with_of_kPointNoExc` (converse at fixed `K`).

**F3 — ledger fidelity.**  `KPointNaturalCorrelationNoExc 2` is 🔴, not "published": it is TT
Thm 3.1(ii) with the exceptional set of scales deleted, which TT say is out of reach, and
`exceptional_set_can_pin_a_scale` shows it is not derivable from the faithful
`TwoPointNaturalCorrelation`.  Also checked (do not re-derive): E cannot be dodged at the
`ConjC3` end either — positive lower density needs *bounded-ratio dense* good scales, and
`∫_E dt/t ≤ Cst L^{-c} log X` with `L ≍ (log X)^κ` swallows a whole dyadic block as soon as
`Cst (log X)^{1-κc} ≥ log 2`; Fubini over `X ∈ [N, N²]` only bounds the doubly-bad set's
*log*-measure by `Cst (log A)^{1-κc} ≫ 1`.  Same wall as log-Chowla ⇏ Chowla; TT's own Thm 1.3
escapes it because *irrationality* needs only infinitely many good scales.

## Landed this lap (`C3MrtUnifK.lean`, 27 declarations, all trust-triple clean)

* `quantDepthElliottGen_forces_diagonal`, `DepthDiagonal`, `weylLambertTwist_of_depthDiagonal`,
  `depthDiagonal_of_quantDepthElliottGen`.
* `KPointNoExcWith`, `kPointNoExc_of_with`, `exists_with_of_kPointNoExc`.
* `norm_progression_sum_le_class_sum` — head + the two boundary points, as an inequality.
* `progression_avg_le_of_window` — lap 86's NEXT ①: the quantitative twin of
  `progression_avg_tendsto_of_window`,
  `‖avg‖ ≤ [r + 2 + (log₂Y+1) + (Φ(Y/2^{k₀}) + 2^{-k₀})·Y]/J`, `Y = MJ+r`.
* `dyadic_window_bound_with` — `dyadic_window_bound_K` with the constants AND the scale
  threshold explicit (`hthr : max 2 (K+1) ≤ (2 log N)^(κ·cK K)`), so it can be evaluated along
  a schedule.
* `windowPhi cK CstK κ K M A` — the explicit per-scale profile
  `a ↦ if a < A then 1 else min 1 (CstK K · (2 log a)^(-(κ·cK K)) / M)`, with
  `windowPhi_le_one`, `windowPhi_nonneg`, `windowPhi_antitone` and `windowPhi_window_bound`
  (the `hB` hypothesis of `class_sum_le_of_window` / `progression_avg_le_of_window`, trivial
  count below `A`, analytic bound above).  `A` is free so it can move with `K`.
* `progCount`, `progCount_bounds` (`N ≤ M·progCount + r ≤ N + M`),
  `norm_progression_below_le` — one residue class below `N`, bounded by the halving stack
  evaluated at the scale `N` itself, the straddle absorbed into the `+ M`.
* **`depthAvg_le_of_window`** — THE EXPLICIT MAJORANT, point-count-free:

      ‖depthAvg b P Q j hh D N‖
        ≤ M₀ · [ (M₀+2) + (log₂(N+M₀)+1) + (Φ(N/2^{k₀}) + 2^{-k₀})·(N+M₀) ] / N ,
      M₀ = Q·primorial P  (fixed before N).

  So the head is `O(M₀²/N)` and the rate is carried entirely by `Φ(N/2^{k₀}) + 2^{-k₀}`.
* `windowPhi_hwin` — the splice: ONE threshold condition at the single scale `A`,
  `max (max 2 (K+1)) M₀ ≤ (2 log A)^(κ·cK K)`, propagates to every `a ≥ A`.
* **`depthAvg_le_with`** — everything of laps 84–87 in one statement: named input ⇒ explicit
  majorant.  Only THREE quantities move with `K`: `cK K`, `CstK K`, and the threshold scale
  `A = A(K)`.  That is exactly the data the diagonal needs.
* `depthLL_pos`, `tendsto_natLog_succ_div`, `tendsto_natLog_shift_div`.
* **`depthAvg_diag_tendsto_of_unif` — THE DIAGONAL IS A THEOREM.**  `depthAvg_le_with`
  instantiated at `K = depthLL b N`.  Every term but one dies under `1/N` (the `M₀²` head, the
  `log₂` head, the `(N+M₀)/N → 1` rescaling), leaving exactly ONE hypothesis:

      windowPhi cK CstK κ (depthLL b N) M₀ (Athr (depthLL b N)) (N / 2^{k₀ N}) + 2^{-k₀ N} → 0

  — the *schedule compatibility* of the profile, i.e. precisely the uniformity the per-`K`
  existential could not express (F2).  Composed with `weylLambertTwist_of_depthDiagonal` this
  closes the crux from a `K`-uniform input.
* **The schedule hypothesis made checkable**, in three steps:
  `windowPhi_diag_tendsto` (once the scale passes the threshold, the profile IS its analytic
  branch), `rate_tendsto_of_exponent` (`Cst·x^{-e} = exp(log Cst − e log x)`, so the whole
  question is whether the constant's log is beaten by the saving), and
  `exponent_tendsto_atBot_of_uniform`.
* **`depthAvg_diag_tendsto_of_uniform` — a `K`-UNIFORM input closes the crux outright**, with
  NO schedule arithmetic: constants independent of `K` give
  `log Cst₀ − κc₀ log(2 log a) → −∞` for free.  The only residual hypotheses are that the cut
  level `k₀` and the cut scale `N/2^{k₀ N}` grow and eventually pass `Athr`.

## NEXT (in order)

1. ~~`windowPhi`~~ — DONE this lap.
2. ~~`depthAvg_le_with`~~ — DONE this lap.
3. ~~`depthElliottLL_of_unif`~~ — DONE this lap (`depthAvg_diag_tendsto_of_unif`).
4. ~~The uniform-constant profile~~ — DONE this lap (`depthAvg_diag_tendsto_of_uniform`).
5. **THE DEGRADING PROFILE — next lap's target**, and the realistic one.  Via
   `rate_tendsto_of_exponent` the whole question is now ONE scalar limit:

       Real.log (CstK D_N) − κ·cK D_N·Real.log (2 log (N/2^{k₀ N}))  →  −∞ ,   D_N = depthLL b N.

   With `k₀ N = Nat.log 2 (Nat.log 2 N)` (so `2^{-k₀ N} ≍ 1/log₂ N → 0`, `log(N/2^{k₀ N}) ≍
   log N`), `cK K = c₀/(K+1)^m` and `CstK K = exp((K+1)^m)` give
   `exp(O((lll N)^m) − κc₀·(ll N)/(lll N)^m) → 0`, since `D_N + 1 = O(lll N)`
   (`pow_depthLL_le : b^{D_N} ≤ b·llProxy N²`).  Needs, in Lean: an explicit `Athr` with
   `Athr (depthLL b N) ≤ N/2^{k₀ N}` eventually, and `Tendsto (fun N => N/2^{k₀ N}) atTop atTop`.
   Arithmetic already
   checked (PENDING_WORK F2): `cK K = c₀γ^K` needs `γ > b^{-1/2}` (γ = 1/2 FAILS at b = 3,
   θ = 2log2/log3 ≈ 1.26 > 1); `cK K = c₀/K^m` is comfortable; `CstK K ≤ exp(K^m)` always
   affordable since `CstK (depthLL b N) = exp(O((log log log N)^m))`.

## Known remaining wiring (pre-existing, not introduced this lap)

`depthAvg_diag_tendsto_of_unif` needs `κ > 0`, which via `ttExponent_pos` needs
`depthRoot b hh 0 ≠ 1`, i.e. `b ∤ hh`.  Every consumer in the chain
(`depthAvg_two_tendsto_of_noExc`, `depthAvg_K_tendsto_of_noExc`, `rung_one`) already carries
`hζ` as a hypothesis, so this is not new — but `DepthDiagonal b` quantifies over ALL `hh : ℤ`.
The two degenerate cases: `hh = 0` (then `depthAvg` is the bare twist average
`(1/N)∑ e(jn/Q) → 0` since `0 < j < Q`), and `b ∣ hh`, `hh ≠ 0` (then `ζ_0 = 1` but
`ζ_v ≠ 1` for `v = v_b(hh)`, so the correlation is the same shape re-indexed from `i = v`,
a translation of `n`).  Name and close these when assembling `WeylLambertTwist`.

## Still refuted — DO NOT RETRY

Lap 80's list, plus: removing `E` from TT Thm 3.1 by varying `X` at a prescribed scale
(`exceptional_set_can_pin_a_scale`); bounded-ratio-density of good scales at the `ConjC3` end
(lap 87 F3); and the whole `QuantDepthElliottGen` budget layer (lap 87 F1).
