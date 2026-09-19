# KICKOFF 2026-09-19 — W3: Weyl's criterion, one lap

Operator: Ren (attended session, Trevor said "Fire!" at ~17:50 EDT 2026-09-19).  Engine Opus/low.
Branch `wip/g5-prime-subset`.  Design: `DESIGN-2026-09-19-bcr-wiring.md` §2 row W3 and §3b.

## The one target

`src/NormalNumbers/WeylCriterion.lean` — `NormalNumbers.equidistributed_of_weyl`, statement
FROZEN (do not change the statement; do not rename; it is guarded by name):

```lean
theorem equidistributed_of_weyl (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fourierMean u h) atTop (𝓝 0)) :
    Equidistributed u
```

`Equidistributed` is `RealDefs.lean`: for every `0 ≤ a ≤ c ≤ 1`, `visitCount u a c n / n → c − a`.
Done when the file is sorry-free and the lib builds.  Pure analysis; no number theory.

## Route (follow it; decompose into named `sorry` leaves and commit the compiling skeleton first)

1. `cesaro_fourier_tendsto`: for `n ≠ 0`, the Cesàro mean of `fun k => fourier n (u k : AddCircle 1)`
   tends to `0` (unfold `fourier` on `AddCircle 1`: `fourier n x = exp(2πi n x)` up to the coercion —
   `fourier_coe_apply`), and for `n = 0` it is `1`.  Hence for every trigonometric polynomial
   `P ∈ span ℂ (range fourier)` the Cesàro mean of `P ∘ u` tends to `∫ P` (= its constant term; use
   `fourierCoeff` / `integral_fourier` style lemmas, or just linearity over the finite span).
2. `cesaro_continuous_tendsto`: for every `f : C(AddCircle 1, ℂ)`, the Cesàro mean of `f ∘ u` tends
   to `∫ f dμ` (Haar, `haarAddCircle`, total mass 1).  Proof: `ε/3` with
   `span_fourier_closure_eq_top` giving a trig polynomial `P` with `‖f − P‖ < ε` uniformly.
3. `indicator_squeeze`: for `0 ≤ a ≤ c ≤ 1` and `δ > 0`, continuous `1`-periodic real trapezoids
   `g₋ ≤ 1_{[a,c)} ≤ g₊` on `[0,1)` with `∫ g₊ − ∫ g₋ ≤ δ` (build with `max`/`min` of affine pieces; or
   use `Metric`/`ContinuousMap` Urysohn-type lemmas on `AddCircle`).  Lift to `C(AddCircle 1, ℝ)`
   via `AddCircle.liftIco`/the quotient map, or define them directly on the circle.
4. Assemble: `visitCount u a c n / n` is the Cesàro mean of the indicator; it is squeezed between
   the Cesàro means of `g₋`, `g₊`, which tend to `∫ g₋`, `∫ g₊` within `δ` of `c − a`.

Mathlib pointers: `Mathlib/Analysis/Fourier/AddCircle.lean` (`fourier`, `fourier_coe_apply`,
`span_fourier_closure_eq_top` at line 245, `fourierCoeff`), `Mathlib/Topology/Instances/AddCircle`
(`AddCircle.liftIco`, `AddCircle.equivIco`), `Mathlib/MeasureTheory/Integral/Periodic.lean`
(`AddCircle.volume_eq_smul_haarAddCircle`, `intervalIntegral` over a period).

## Rules
- Report the advance, not the sorry count.  `native_decide`/deprecation warnings are fine.
- Finish with `box done --green` when the file is sorry-free; if stuck, commit named leaves and write
  `HANDOFF-2026-09-19-weyl-lapNN.md` naming the leaf and the exact mathlib gap.
- Banked, do not touch: everything else in the repo.
