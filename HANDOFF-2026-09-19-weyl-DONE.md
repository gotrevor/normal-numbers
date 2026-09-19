# HANDOFF 2026-09-19 — W3 (Weyl's criterion) PROVED, one lap

`src/NormalNumbers/WeylCriterion.lean` is sorry-free; `NormalNumbers.equidistributed_of_weyl`
depends only on `[propext, Classical.choice, Quot.sound]`.  Statement unchanged (frozen).
Module wired into `src/NormalNumbers.lean`; full `lake build` green (9091 jobs).

## What is in the file (reusable)

| name | content |
|---|---|
| `cMean u f n`, `cInt f`, `CGood u f` | Cesàro mean of `f : C(AddCircle 1, ℂ)` along `↑(u k)`, its one-period integral `∫₀¹ f ↑x`, and "mean → integral" |
| `norm_cMean_le`, `norm_cInt_le` | both functionals are `≤ ‖f‖` — the uniform bounds that make ε/3 work |
| `cInt_fourier_ne`, `cInt_fourier_zero`, `cMean_eq_fourierMean` | `∫₀¹ e_h = 0` for `h ≠ 0` (`integral_exp_mul_complex` + `Complex.exp_int_mul_two_pi_mul_I`); `cMean u (fourier h) = fourierMean u h` |
| `cgood_span` | `Submodule.span_induction` over `span ℂ (range fourier)` |
| `cgood_all` | ε/3 against `span_fourier_closure_eq_top` (density via `Submodule.topologicalClosure_coe` + `Metric.mem_closure_iff`) |
| `cgood_real` | real-valued form, through `intervalIntegral_re` and `Complex.continuous_re` |
| `trapUp a c δ`, `trapLo a c δ` | continuous circle trapezoids `min 1 (max 0 ((r ± δ − ‖y − ↑m‖)/δ))`, `m = (a+c)/2`, `r = (c−a)/2` |
| `integral_trapUp_le`, `le_integral_trapLo` | integrals within `2δ` of `c − a` |
| `le_abs_sub_int`, `norm_coe_ge`, `norm_coe_le`, `norm_coe_sub` | the circle-norm toolkit for the pointwise squeeze |

## The two design choices that made it one lap

1. **Never leave `C(AddCircle 1, ℂ)` for the Haar measure.**  The target functional is the
   elementary `∫ x in (0:ℝ)..1, f ↑x`; linearity, the `‖·‖`-bound and the value on `fourier h`
   are all interval-integral lemmas.  No `haarAddCircle`, no `fourierCoeff`.
2. **Build the trapezoids from the circle norm, not by periodising an ℝ-trapezoid.**
   `fun y => min 1 (max 0 ((r + δ − ‖y − ↑m‖)/δ))` is continuous on the circle by `fun_prop`
   with no `liftIco` side conditions, and it makes the `a = 0` / `c = 1` boundary cases
   disappear (the arc through `0` is handled exactly like any other).  The integral bound then
   comes from `Function.Periodic.intervalIntegral_add_eq`, shifting the period to
   `[m − 1/2, m + 1/2]` where `‖↑x − ↑m‖ = |x − m|` (`AddCircle.norm_coe_eq_abs_iff`), and a
   three-piece `integral_add_adjacent_intervals` split (outer pieces vanish identically).

## Next (per DESIGN-2026-09-19-bcr-wiring.md §2)

W4 (dyadic → prefix, elementary), then L1 (Mertens upper bound) and the L4 assembly.
W3 is no longer a blocker for either wiring theorem.
