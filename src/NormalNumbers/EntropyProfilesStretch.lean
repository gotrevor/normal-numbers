/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.EntropyProfiles

/-!
# Entropy lane (E5): stretch conjectures

Believed statements beyond the frozen headline of `EntropyProfiles.lean`.  Each is a `sorry` with
its source, an English sketch and two confidences (true / tractable for us).  Audit:
`docs/ENTROPY-AUDIT-2026-10-04.md`.
-/

open MeasureTheory

namespace NormalNumbers.EntropyProfiles

/-- **Stretch 1: the bi-Lipschitz image can avoid normality in every base at once.**

Strengthens `exists_strictMono_biLipschitz_cantorSet_not_isNormal_two` (same Hochman–Shmerkin
question, §1.2.1 of arXiv:1302.5792).  Sketch: replace the fixed target `F` (no hex digit 15) by a
scale-dependent target: on the depth range `[N_j, N_{j+1})` of the nested-interval construction
use `F_{b_j} = {no base-b_j^{k} digit equal to b_j^{k} − 1}` with `(b_j)` listing every base
infinitely often and `N_{j+1}/N_j → ∞`, so that every point of `g(K)` has a long prefix missing a
digit in base `b_j^{k}` for infinitely many `j`.  The work is the switch between targets: the
current interval must meet the next target in a sub-window of comparable size, which needs the
gap estimate for `F_{b} ∩ F_{b'}`-type configurations near the switch.

Confidence: true 75%; tractable after the headline 45%. -/
theorem exists_strictMono_biLipschitz_cantorSet_absAbnormal :
    ∃ g : ℝ → ℝ, StrictMono g ∧ IsBiLipschitz g ∧
      ∀ x ∈ cantorSet, ∀ b : ℕ, 2 ≤ b → ¬ IsNormal b (g x) := by
  sorry

/-- **Stretch 2 (genuinely entropy-side, believed open): nonlinear images of `×p`-ergodic measures
are normal in the dependent base.**

For a `T_p`-ergodic measure `μ` of positive dimension, Hochman–Shmerkin Theorem 1.10 gives
`g μ` pointwise `m`-normal for `m ≁ p` and `g ∈ diff²`, but says nothing about `m = p`.  For
self-similar `μ` the base `p` is covered (Hochman–Shmerkin Theorem 1.7 for analytic non-affine
`g`; Baker–Banaji polynomial decay of `g μ`), and for Gibbs measures by the self-conformal theory
(Algom–Rodriguez Hertz–Wang).  For a general ergodic `μ` (no product or Gibbs structure, hence no
Fourier input after pushforward) we found no statement either way.

Sketch of the expected mechanism: `p^n g(x) mod 1 ≈ {p^n g(a_n/p^n)} + g'(x)·T_p^n x`, where
`a_n/p^n` is the base-`p` truncation; the second term is a `g'(x)`-dilate of a `μ`-generic orbit,
and the first is a translation driven by the curvature of `g`, which should randomise the phase
of the scenery eigenfunction that Hochman (2012) attaches to positive-entropy `×p` measures.

Confidence: true 70%; open 60%; tractable for us 5%. -/
theorem ae_isNormal_self_base_sq_of_timesP_ergodic (p : ℕ) (hp : 2 ≤ p) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hsupp : μ (Set.Ico 0 1)ᶜ = 0) (herg : Ergodic (timesMap p) μ)
    (hfrost : ∃ C δ : ℝ, 0 < δ ∧ ∀ x r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r ^ δ)) :
    ∀ᵐ x ∂μ, IsNormal p ((x + 1) ^ 2) := by
  sorry

end NormalNumbers.EntropyProfiles
