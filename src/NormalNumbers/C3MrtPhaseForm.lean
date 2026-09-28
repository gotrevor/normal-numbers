/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTruncate

/-!
# The crux as a single Weyl sum, and its content-bearing range

Two moves on `DepthDyadicBound`.

## 1.  The crux is ONE Weyl sum, not a `K`-fold correlation

`depth_prod_eq_ee` (lap 99) says the depth product is a single additive character.  Define the
**depth phase**

    depthPhase b K n = ∑_{i<K} ω(n+i+1) / b^{i+1}       (a real number)

— up to the factor `h'` this is exactly the quantity whose equidistribution the C3 crux needs.
Then `depthDyadicBound_iff_phase` is an **equivalence**:

    DepthDyadicBound b h' κ cK CstK K  ↔  DepthPhaseBound b h' κ cK CstK K

where `DepthPhaseBound` asks the same numerical bound for `∑_{n} e(h'·depthPhase b K n)`.  So the
open statement is not intrinsically a `K`-fold Elliott correlation: it is the assertion that the
single real sequence `n ↦ h'·depthPhase b K n` is equidistributed mod 1 along the window, with a
quantitative rate.  (The `K`-fold correlation shape is one *route* to it — Tao–Teräväinen's — and
the route that lap 99 showed cannot be shortened by truncation.  This reformulation is offered as
a second attack surface: classical exponential-sum technology applies to a Weyl sum without
needing the correlation decomposition at all.)

## 2.  The crux restricted to its content-bearing range

Lap 98 proved the inequality is free when `M ≤ dyadicFactor`.  So the input may assume
`dyadicFactor < M`: `DepthDyadicBoundNT` ("non-trivial") is that restriction, and
`depthDyadicBound_of_nt` recovers the full statement.  This is the **seventh** free narrowing of
the crux, and it is the sharp form — every remaining instance asserts cancellation beyond the
trivial estimate.  `conjC3_of_dyadic_input_nt` is the corresponding headline.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- **The depth phase.**  `depthPhase b K n = ∑_{i<K} ω(n+i+1)/b^{i+1}`; the C3 crux is the
equidistribution of `h' · depthPhase b K ·` along dyadic windows. -/
noncomputable def depthPhase (b K n : ℕ) : ℝ :=
  ∑ i ∈ range K, (omegaNat (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

/-- The depth product is the additive character of `h' · depthPhase`. -/
theorem depth_prod_eq_ee_phase (b n K : ℕ) (h : ℤ) :
    ∏ i : Fin K, depthRoot b h i ^ omegaNat (n + (i : ℕ) + 1)
      = ee ((((h : ℝ) * depthPhase b K n : ℝ) : ℂ)) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => depthRoot b h i ^ omegaNat (n + i + 1)) K,
    depth_prod_eq_ee]
  congr 2
  rw [depthPhase, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- **The crux in Weyl-sum form.** -/
def DepthPhaseBound (b : ℕ) (h' : ℤ) (κ : ℝ) (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * cK K) →
    ∀ M r : ℕ, 0 < M → (M : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K) →
      ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
          ee ((((h' : ℝ) * depthPhase b K n : ℝ) : ℂ))‖
        ≤ CstK K * (2 * Real.log N) ^ (-(κ * cK K)) * (N : ℝ) / (M : ℝ)

open scoped Classical in
/-- **The crux IS a Weyl-sum statement** — not merely implied by one. -/
theorem depthDyadicBound_iff_phase {b : ℕ} {h' : ℤ} {κ : ℝ} {cK CstK : ℕ → ℝ} {K : ℕ} :
    DepthDyadicBound b h' κ cK CstK K ↔ DepthPhaseBound b h' κ cK CstK K := by
  classical
  have hrw : ∀ N M r : ℕ,
      (∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1))
      = ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
          ee ((((h' : ℝ) * depthPhase b K n : ℝ) : ℂ)) := by
    intro N M r
    exact Finset.sum_congr rfl fun n _ => depth_prod_eq_ee_phase b n K h'
  constructor
  · intro H N hN hthr M r hM hML
    rw [← hrw N M r]
    exact H N hN hthr M r hM hML
  · intro H N hN hthr M r hM hML
    rw [hrw N M r]
    exact H N hN hthr M r hM hML

/-- **The crux restricted to its content-bearing range** (lap 98: everything else is free). -/
def DepthDyadicBoundNT (b : ℕ) (h' : ℤ) (κ : ℝ) (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * cK K) →
    ∀ M r : ℕ, 0 < M → (M : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K) →
      dyadicFactor cK CstK κ K N < (M : ℝ) →
      ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
          ∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ CstK K * (2 * Real.log N) ^ (-(κ * cK K)) * (N : ℝ) / (M : ℝ)

/-- **Seventh free narrowing.**  Assuming the bound only where it is not already a theorem
suffices. -/
theorem depthDyadicBound_of_nt {b : ℕ} {h' : ℤ} {κ : ℝ} {cK CstK : ℕ → ℝ} {K : ℕ}
    (H : DepthDyadicBoundNT b h' κ cK CstK K) : DepthDyadicBound b h' κ cK CstK K := by
  intro N hN hthr M r hM hML
  rcases le_or_gt ((M : ℝ)) (dyadicFactor cK CstK κ K N) with htriv | hnt
  · exact dyadic_ineq_of_trivial hM htriv
  · exact H N hN hthr M r hM hML hnt

/-- `ConjC3` from the crux on its content-bearing range only. -/
theorem conjC3_of_dyadic_input_nt {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, DepthDyadicBoundNT b h' (ttExponent (depthRoot b h' 0))
        (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 :=
  conjC3_of_dyadic_input hc₀ hθ0 hθ m fun b hb h' hh' =>
    (hin b hb h' hh').mono fun _K hK => depthDyadicBound_of_nt hK

#print axioms NormalNumbers.CastingOut.depth_prod_eq_ee_phase
#print axioms NormalNumbers.CastingOut.depthDyadicBound_iff_phase
#print axioms NormalNumbers.CastingOut.depthDyadicBound_of_nt
#print axioms NormalNumbers.CastingOut.conjC3_of_dyadic_input_nt

end CastingOut

end NormalNumbers
