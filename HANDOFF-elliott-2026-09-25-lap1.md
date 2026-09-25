# HANDOFF elliott 2026-09-25 lap1 — the ladder, and the affine generalisation PROVED

Branch `wip/elliott-port`.  Target: `NormalNumbers.ElliottGeneral.nonasymptoticLogElliott`
(= `Erdos67b.NonasymptoticLogElliott`, Tao 2016 Thm 1.3).

## The crux

`NormalNumbers.ElliottLadder.dilatedCMLogElliott` (`src/NormalNumbers/ElliottLadder.lean`):
two **independent** completely multiplicative **unimodular** `f₁, f₂`, non-pretentiousness on `f₁`
only, and a pair of affine forms with a **common dilation** `a·n + c₁`, `a·n + c₂`, `c₁ ≠ c₂`.
This is the rung the dependency's analytic machinery has to be re-run for.

## This lap's advance

The general theorem was one opaque `sorry`.  It is now decomposed into exactly two named
obligations, and the third generalisation is **fully discharged, axiom-clean**:

* **PROVED** `affineCM_of_dilatedCM : DilatedCMLogElliott → AffineCMLogElliott`.
  Tao's full affine generality (independent dilations `a₁, a₂`) is *free* on the completely
  multiplicative unimodular rung.  Insight: `f₁(a₂·(a₁n+b₁)) = f₁(a₂)·f₁(a₁n+b₁)`, so multiplying
  the first form by `a₂` and the second by `a₁` converts `(a₁n+b₁, a₂n+b₂)` into the
  common-dilation pair `(a n + a₂b₁, a n + a₁b₂)` with `a = a₁a₂`, at the cost of the *unimodular*
  constant `f₁(a₂)f₂(a₁)` — which does not move the norm at all.  The determinant hypothesis
  `a₁b₂ − a₂b₁ ≠ 0` is *exactly* `a₂b₁ ≠ a₁b₂`, i.e. the two new shifts differ.  So generalisation
  (2) of the kickoff costs nothing, and the "dilate by `a₁a₂`, restrict to residue classes" route
  sketched in the kickoff is **not needed**: no AP-restricted machinery, no residue classes.
* **PROVED** `unitCircle_of_dilatedCM : DilatedCMLogElliott → Erdos67b.UnitCircleLogElliott`.
  Faithfulness anchor: the crux rung really does generalise the case the dependency proves.
* Supporting lemmas, both axiom-clean: `positiveIntExtension_natMul` (pull a positive natural
  factor out of the zero-extension of a completely multiplicative function, at *integer*
  arguments), `elliottLogCorrelation_common_dilation`.

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]`.

## Open leaves (`src/`, both disclosed with full route docstrings)

1. `dilatedCMLogElliott` — the crux.  Two changes to the proved proof:
   (i) pair observable `f₁(n)f₂(n+h)` instead of `f(n)conj f(n+h)`; the prime-dilation identity
   `Erdos67b.unit_pair_dilation` becomes `f₁(pn)f₂(pn+ph) = f₁(p)f₂(p)·f₁(n)f₂(n+h)` and
   `‖f₁(p)f₂(p)‖ = 1`, so dilation is still an isometry — this is *why* unimodularity (not
   `1`-boundedness) is the right hypothesis at this rung, and why generalisation (3) of the kickoff
   is structurally free too;  (ii) window/divisibility bookkeeping over `a·n+c`, with the graph step
   `n ↦ pn` sending `c₂−c₁` to `p(c₂−c₁)` — the same `h ↦ ph` step as the proved case.
   The two inputs to re-prove are `exists_logPairCorrelation_small_of_fourier_first_moments`
   (`PrimeGraphFourierUpper.lean`) and the wiring around
   `mrtModulatedShortIntervalUnrestricted` (`MRTComplete.lean`); the MRT input itself is applied to
   `f₁` alone and is unchanged.
2. `nonasymptotic_of_affineCM` — generalisation (1), `1`-bounded multiplicative → completely
   multiplicative unimodular.  Full route in the docstring: Hall/Wirsing dichotomy on
   `Σ(g₁) = ∑_{p≤X}(1−‖g₁(p)‖)/p`; Case A elementary (nonnegative mean-value bound, pointwise
   domination); Case B two convolution expansions with absolutely convergent `∑1/d` tails —
   `g = g̃ ⋆ u` with `u` supported on **squarefull** `d`, and `‖g̃‖ = 1 ⋆ v` with
   `∑‖v(d)‖/d ≤ exp(O(C))` convergent *precisely because* we are in Case B.  Crucially the
   divisibility constraints `d ∣ a_i n + b_i` these produce are *dilations of the affine form*, so
   they are absorbed by `AffineCMLogElliott` itself — again no AP-restricted machinery.
   Non-pretentiousness survives: `D(ĝ, χn^{it};X)² ≤ D(g̃, χn^{it};X)² + C` from
   `Re(ĝ(p)w) − Re(g̃(p)w) ≤ 1 − ‖g̃(p)‖`, and `C` is fixed while `A → ∞`.

## Confidence

That the *headline lands eventually*: the route is now fully specified with no step whose
feasibility is in doubt — leaf 2 is standard multiplicative-function technology, leaf 1 is a port of
proved machinery with an isometric twist.  Leaf 1 is labour (~20 dependency files' worth of
statements re-run in `src/`, never edited in place) rather than new mathematics.  Next lap: start
leaf 1 by restating `Erdos67b.logPairCorrelation` for a pair `(f₁,f₂)` and proving the two-function
`unit_pair_dilation` analogue in `src/`, which is the smallest compiler-grounded probe that the
"dilation is still an isometry" claim survives contact with the dependency's definitions.

## Build

`lake build NormalNumbers.ElliottGeneral` green (warm tree, ~60s after edit).  Never
`lake exe cache get`.  Files importing the dependency stay out of the `NormalNumbers` root.
