# Handoff: Philipp 1967 ψ-mixing — **PROVED** (side quest complete)

**Date**: 2026-09-27 · **Branch**: `wip/philipp-psi-mixing`

## Result

`NormalNumbers.Literature.philipp_psi_mixing_holds`
(`src/NormalNumbers/LiteraturePhilipp.lean`) discharges the cited
`Literature.philipp_psi_mixing`, with `ρ = 79/100 < 0.8`.
`#print axioms` → `[propext, Classical.choice, Quot.sound]`.  Full `lake build`
green (9277 jobs).  The def and the theorem name were not touched; the statement
is **true as transcribed** (no counterexample — see the numerics below).

## Why the existing stack was not enough

`CFPin.abs_horizonIntegral_sub_gauss` gives `|G_k(t) − γ(A)| ≤ (9/10)^k·4|A|`,
i.e. `≤ 5.55·(9/10)^k·γ(A)`.  Philipp's statement is **constant-free**:
`≤ ρ^n·γ(A)·γ(I_u)` for *every* `n ≥ 1` with `ρ < 4/5`.  Since `9/10 > 4/5`,
`C·(9/10)^n ≤ ρ^n` fails for large `n` no matter how small `C` is, so the
*rate* had to improve — the `9/10` of `stepOp_lipschitz` is not slack, it is
a wall.  (And it is close to sharp in the `|t−t'|` metric: taking `φ(x) = −x`
gives `(Pφ)'(0) ≈ 0.757·L`, so no argument in that metric can reach `< 0.8`.)

## The move: change the metric

Measure the `t`-regularity of the horizon integrals in the **log metric**
`d(t,t') = |log(1+t) − log(1+t')|`, i.e. Lipschitz in `τ = log(1+t)`.  Three
things improve at once, and all three are needed:

1. **Contraction.**  `stepOp_logLipschitz` (`CFPsiPin.lean`): factor `3/4`
   (proved value `77/108 ≈ 0.713`; numerically the truth is `≈ 0.51`).  The gain
   is concentrated in the dominant branch `t ↦ 1/(1+t)`, which costs `≈ 1/2` in
   `|t−t'|` but only `≈ 1/4` in `d`.  The engine is the exact bound
   `|log(1+z_k) − log(1+z'_k)| ≤ (t−t')/((k+2+t)(k+1+t'))`
   (`abs_log_stepPt_sub_le`), from `log(1/R) ≤ 1/R − 1` on the cross-ratio
   `R = (k+2+t)(k+1+t')/((k+2+t')(k+1+t)) = 1 − (t−t')/((k+2+t')(k+1+t))`.
   Budget: A-series `1/4 + 2/27 + 1/18`, Abel-resummed B-series `1/6 + 1/6`.

2. **Base constant.**  `abs_tailDensity_sub_le_log`:
   `|h_t(y) − h_{t'}(y)| ≤ 2/(1+y)·d(t,t')`, from the exact numerator
   factorization `(t−t')·(1 − 2y − y²(t+t'+tt'))` and the two clean facts
   `(1+y)(1+t) ≤ 2P` (⇔ `(1−y)(1−t) ≥ 0`) and `2y + y²(t+t'+tt') − 1 ≤ P`,
   where `P = (1+ty)(1+t'y)`.  Sharp at `(y,t,t') = (1,0,0)` and `(0,1,1)`.
   Hence `G₀` is `2 log 2·γ(A)`-Lipschitz in `d`.

3. **Averaging factor.**  In `τ = log(1+s)` the Gauss measure on the tail
   parameter is **uniform on `[0, log 2]`**, so
   `∫ |a − τ| dτ/log 2 = (a² + (log 2 − a)²)/(2 log 2) ≤ log 2/2`
   (`integral_gaussDensity_mul_abs_log_sub_le`, by FTC with antiderivative
   `(a·log(1+s) − log(1+s)²/2)/log 2`).  The crude bound `log 2` would *not*
   have sufficed; the factor-2 gain here is what makes the head constant `< 1`.

Product of (2) and (3): `2 log 2 · (log 2)/2 = (log 2)² ≈ 0.48 < 1`.  So
`horizonIntegral_pin_geom : |G_k(t) − γ(A)| ≤ (3/4)^k·(log 2)²·γ(A) ≤ (79/100)^k·γ(A)`
— **constant-free**, which is exactly the shape the def demands.

## Plumbing (LiteraturePhilipp.lean)

* `gaussMeasure_cylinder_psi_mixing` — the `CFGammaMixing` mixture argument
  re-run with the new pin in place of `4|A|·(9/10)^g`.
* `gaussMeasure_inter_cfCylinderFrom` — `cfCylinderFrom m w` and
  `(0,1) ∩ T^{-m}(I_w)` differ only inside `range (ℚ → ℝ)` (an irrational orbit
  never leaves `(0,1)`), hence agree after intersecting and measuring.
* `gaussMeasure_cfCylinder_eq_zero` — a word with a `0` digit names a γ-null
  cylinder, so the inequality there is `0 ≤ 0`.  This covers the def's
  quantification over *all* `u, v : List ℕ`, junk words included.

## Numerics (why the def is true, not merely provable-with-slack)

`ψ(n) = sup_{t,y} |L^n h_t(y)/g(y) − 1|`.  At `n = 1`,
`L h_t(y)/g(y) = (1+t)(1+y) log 2 · ψ'(1+t+y)` (trigamma), maximized at
`t = y = 0`: `log 2 · π²/6 = 1.1402`, so `ψ(1) ≈ 0.140`.  `ψ(n)` then decays
like Wirsing's `0.3036^n`.  `ρ = 79/100` has room to spare at every `n`; the
def's `ρ < 0.8` is Lévy's classical rate, not a typo.

## Leftovers / opportunities

* The proved contraction factor `3/4` is loose by ~50%; `stepOp_logLipschitz`
  could be sharpened toward `0.51` if a tighter Gauss–Kuzmin rate is ever wanted
  elsewhere.  Nothing downstream needs it.
* `CFMixing.cylinder_mixing` / `CFPin.abs_horizonIntegral_sub_gauss` still carry
  the old `(9/10)^k·4|A|` bound.  They are used by the W4 assembly and are left
  untouched; anything wanting a constant-free rate should call
  `horizonIntegral_pin_geom` instead.
* No `Maze.lean` row cites Philipp (checked), so nothing to repoint there; the
  `Literature.lean` docstring is marked **VERIFIED** with a pointer to the theorem.
