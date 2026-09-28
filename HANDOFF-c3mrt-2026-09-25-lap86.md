# HANDOFF c3-mrt 2026-09-25 lap86 — the named inputs, and the start of the rate

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (OUTRANKS this file).
Branch `wip/c3-mrt`, HEAD `8480171`, tree clean.  Tip: `NormalNumbers.C3MrtQuantKPoint`.

    lake build
    lake build NormalNumbers.C3MrtQuantKPoint

Chain: `… → C3MrtNoExc → C3MrtTTPretentious → C3MrtWindowMass → C3MrtUniformMass
→ C3MrtKPointNoExc → C3MrtQuantKPoint`.

## Laps 81–86

* **83.  `uniformResonantMass_holds` is a THEOREM** — the archimedean certificate's one named
  analytic input is discharged, axiom-clean.  `ttNonPretentious_zOmegaNat` is unconditional.
* **84.  The `D = 2` assembly is point-count-free** — `class_sum_tendsto_of_window`,
  `progression_avg_tendsto_of_window`.  The only place the point count enters is the window
  bound, i.e. the named input.
* **85.  `KPointNaturalCorrelationNoExc K`** + `dyadic_window_bound_K` +
  `depthAvg_K_tendsto_of_noExc`: the depth-`K` natural-density rung from exactly
  `ProgressionLogRung K` and `KPointNaturalCorrelationNoExc K`, for EVERY `K`.
  `twoPointNoExc_of_kPointNoExc` checks `K = 2` is the old input.
* **86.  The quantitative layer begins.**  `top_down_weighted_le`, `class_sum_le_of_window`.

## Why the rate is now the crux (the gap, stated honestly)

`weylLambertTwist_of_quantDepthElliottGen` consumes `QuantDepthElliottGen b`: ONE `η N → 0`
beating every power of `llProxy N`, with `‖depthAvg b P Q j h D N‖ ≤ C D · η N` for **all** `D`
— because the depth in play is `depthLL b N`, which GROWS with `N`.  Fixed-`K` `Tendsto`
(lap 85) is therefore not enough.

The arithmetic of the assembly, worked out this lap:
* the window bound gives a per-scale `Φ a ≍ Cst_K (2 log a)^{-c_K}/M`;
* `class_sum_le_of_window` at `k₀ ≍ log log Y` gives
  `‖class sum‖/Y ≲ Cst_K (log Y)^{-κ c_K} + 1/log Y`;
* so `η_K(N) ≍ A_K (log N)^{-κ c_K}`, and `C D` is FREE in `QuantDepthElliottGen`
  (it is any `ℕ → ℝ`).  Taking `C D = A_D · e^{D²}` gives
  `η N = sup_D e^{-D²}(log N)^{-κ c_D}`, maximised near `D ≍ log₄ log log N`, i.e.
  `η N ≈ exp(−const·(log log log N)²)` — which beats every power of `log log N`.
  **That is exactly the repo's headline decay class**, so the route closes arithmetically.

## NEXT

1. `progression_avg_le_of_window` — the quantitative twin of
   `progression_avg_tendsto_of_window` (head + two boundary points + `Y = MJ+r`), giving an
   explicit `η_K`.
2. `KPointNaturalCorrelationNoExc` → explicit `Φ` (`min 1 (Cst(2 log a)^{-c}/M)`, guarded to be
   antitone at `a < 2`) and hence the quantitative depth-`K` rung.
3. Then the `sup_D` assembly into `QuantDepthElliottGen` with `C D = A_D e^{D²}`.

## Still refuted — DO NOT RETRY

Lap 80's list, plus: removing `E` from TT Thm 3.1 by varying `X` at a prescribed scale
(`exceptional_set_can_pin_a_scale`).
