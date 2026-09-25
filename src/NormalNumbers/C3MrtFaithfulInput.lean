/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTTDefect
import NormalNumbers.C3MrtSlowSched

/-!
# The headline on FAITHFUL inputs

Lap 102 (`C3MrtTTDefect`) refuted the inputs the lap-90 headline rested on:
`TTNonPretentious` is free, so `KPointNoExcWith` is false, so `conjC3_of_geom_input` is vacuous.
Lap 103 threaded the archimedean hypothesis through the whole chain as a parameter
(`KPointNoExcFor Pnp`, `ArchSupply Pnp`), so the repair costs no new analysis of the window /
schedule / threshold algebra — only a substitution:

    conjC3_of_geom_input_at :
      (∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      (∀ b ≥ 3, ArchSupply (TTNonPretentiousAt A) b) → ConjC3          (0 < θ < 1, 0 < A)

with **both** hypotheses faithful to Tao–Teräväinen: the implied constant `A` is outside `X, L`,
the pretentious distance is an infimum over Dirichlet characters of modulus
`q ≤ (log X)^{1/125}` and over twists `|t| ≤ X²`.  Neither hypothesis is refuted by the
constant-one family (`const_one_not_faithful`), and neither is trivially satisfiable
(`not_ttNonPretentiousUnif_one`).

The honest ledger now reads: the C3 crux follows from **two** named open statements, the
`K`-point correlation input and the archimedean supply.  The second was previously *hidden* by
being discharged against a vacuous `Prop` (`archSupply_tt`, still in the build, now labelled
content-free); upgrading it — characters `q > 1`, twists up to `X²`, uniform constant — is the
real analytic debt, and `ttNonPretentious_of_uniformResonantMass` already supplies the uniform
constant for `q = 1` and `|t| ≤ (log X)^{1/125}`.
-/

open Filter Topology

namespace NormalNumbers

namespace CastingOut

/-- The faithful `K`-point input feeds the parametric chain. -/
theorem kPointNoExcFor_of_atWith {A : ℝ} {cK CstK : ℕ → ℝ} {K : ℕ}
    (h : KPointNoExcAtWith A cK CstK K) :
    KPointNoExcFor (TTNonPretentiousAt A) cK CstK K := by
  intro g hm hb X L hX
  refine h g hm hb X L ?_
  nlinarith [Real.exp_one_lt_d9]

/-- **`DepthDiagonalSlow b` on the faithful inputs.** -/
theorem depthDiagonalSlow_of_geom_at {b : ℕ} (hb : 2 ≤ b) {A c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ArchSupply (TTNonPretentiousAt A) b)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    DepthDiagonalSlow b :=
  depthDiagonalSlow_of_geom_for hb hc₀ hθ0 hθ m
    (fun K => kPointNoExcFor_of_atWith (hin K)) hsup hthr

/-- **THE C3 CRUX ON THE FAITHFUL INPUTS**, threshold data discharged. -/
theorem weylLambertTwist_of_geom_input_at {b : ℕ} (hb : 3 ≤ b) {A c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ArchSupply (TTNonPretentiousAt A) b) :
    WeylLambertTwist b :=
  weylLambertTwist_of_geom_input_for hb hc₀ hθ0 hθ m
    (fun K => kPointNoExcFor_of_atWith (hin K)) hsup

/-- **`ConjC3` ON THE FAITHFUL INPUTS** — the lap-90 headline, repaired.  Two named open
statements, neither vacuous, neither refuted by the constant-one family. -/
theorem conjC3_of_geom_input_at {A c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hsup : ∀ b : ℕ, 3 ≤ b → ArchSupply (TTNonPretentiousAt A) b) :
    ConjC3 :=
  conjC3_of_geom_input_for hc₀ hθ0 hθ m
    (fun b hb K => kPointNoExcFor_of_atWith (hin b hb K)) hsup

/-! ### Non-vacuity of the repaired headline's hypotheses -/

/-- The constant-one family does not satisfy the faithful archimedean supply's conclusion at
large `L`, so §2's refutation of the old input cannot be replayed against
`KPointNoExcAtWith`. -/
theorem const_one_not_archSupply_body {A X L : ℝ} (hA : Real.exp 1 ≤ X) (hAL : 1 < A * L) :
    ¬ TTNonPretentiousAt A (fun _ => (1 : ℂ)) X L :=
  not_ttNonPretentiousAt_one hA hAL

#print axioms kPointNoExcFor_of_atWith
#print axioms conjC3_of_geom_input_at

end CastingOut

end NormalNumbers
