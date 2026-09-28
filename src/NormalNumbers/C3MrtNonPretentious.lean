/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtRungTwo
import NormalNumbers.G4MertensAP

/-!
# Non-pretentiousness of `ζ^Ω`: the unramified (`t = 0`) certificate

`initial_segment_bound_of_elliott` leaves its caller one arithmetic obligation:

    (A : ℝ) ≤ pretentiousDistSqToTwist (ζ₀^Ω) χ t X   for all q ≤ A, χ mod q, |t| ≤ A·X.

This file supplies it for `t = 0`, uniformly over **every** Dirichlet character, and identifies
the exact mechanism.

## The mechanism

`ζ^Ω` is *constant* on the primes: `Ω(p) = 1`, so `ζ^{Ω(p)} = ζ`.  A Dirichlet character cannot
be constantly `ζ ≠ 1`, because `χ(1) = 1`: on the primes `p ≡ 1 (mod q)` — a set of positive
Dirichlet density — the twist is `1` while our function is `ζ`, so each such prime contributes
the full `(1 − Re ζ)/p`.  Summing, Mertens in the class `1 (mod q)` gives

    dist ≥ (1 − Re ζ) · (c_q · log log X − C_q).

So the distance grows like `log log X`, and the Elliott hypothesis at level `A` is satisfiable
exactly from some threshold `X ≥ A^{i₀}` onwards — which is the shape lap 16 built the stack to
consume.  **The `log log X` growth is a ceiling, not an artefact**: every term of
`pretentiousDistSq` is `≤ 2/p`, so no bound better than `2 log log X + O(1)` is available, which
is why the threshold `i₀(A)` is unavoidable.

`ζ ≠ 1` is necessary, not a convenience: for `ζ = 1` the function `ζ^Ω` IS the principal
character, its distance to itself is `0`, and Elliott gives nothing — correctly, since the
correlation is then genuinely non-oscillating.

## What is NOT covered

The archimedean twist `t ≠ 0`.  There the competitor `p^{it}` is not constant on residue
classes and the argument above fails; the true statement (Granville–Soundararajan) needs the
Halász/Lipschitz machinery.  Recorded as the remaining analytic obligation.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- Every term of the pretentious distance is nonnegative when both functions are `1`-bounded. -/
theorem pretentiousTerm_nonneg {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (p : ℕ) : 0 ≤ Erdos67b.pretentiousTerm f g p := by
  rw [Erdos67b.pretentiousTerm]
  have hre : (f p * (starRingEnd ℂ) (g p)).re ≤ 1 := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_one₀ (hf p) (norm_nonneg _) (hg p)
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have : (0 : ℝ) ≤ 1 - (f p * (starRingEnd ℂ) (g p)).re := by linarith
  positivity

/-- At `t = 0` the twist is just `χ`. -/
theorem dirichletArchimedeanTwist_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    Erdos67b.dirichletArchimedeanTwist χ 0 n = χ n := by
  rw [Erdos67b.dirichletArchimedeanTwist, Erdos67b.archimedeanTwist]
  simp

/-- **The unramified certificate.**  The pretentious distance from `ζ^Ω` to any Dirichlet
character (no archimedean twist) is at least `(1 − Re ζ)` times the reciprocal sum of the
primes `p ≡ 1 (mod q)` up to `X`. -/
theorem pretentiousDistSq_ge_class_sum {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz : ‖z‖ = 1) (X : ℕ) :
    (1 - z.re) * ∑ p ∈ (Erdos67b.primesUpTo X).filter (fun p : ℕ => ((p : ZMod q) = 1)), ((p : ℝ))⁻¹
      ≤ Erdos67b.pretentiousDistSq (Erdos67b.restrictToNat (zOmInt z))
          (Erdos67b.dirichletArchimedeanTwist χ 0) X := by
  have hf : ∀ n, ‖Erdos67b.restrictToNat (zOmInt z) n‖ ≤ 1 := by
    intro n
    rw [Erdos67b.restrictToNat]
    exact norm_zOmInt_le_one hz _
  have hg : ∀ n, ‖Erdos67b.dirichletArchimedeanTwist χ 0 n‖ ≤ 1 := by
    intro n
    rw [dirichletArchimedeanTwist_zero]
    exact χ.norm_le_one _
  rw [Erdos67b.pretentiousDistSq]
  have hsub : (Erdos67b.primesUpTo X).filter (fun p : ℕ => ((p : ZMod q) = 1)) ⊆
      Erdos67b.primesUpTo X := Finset.filter_subset _ _
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => pretentiousTerm_nonneg hf hg p))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter, Erdos67b.mem_primesUpTo] at hp
  obtain ⟨⟨hpp, hpX⟩, hpq⟩ := hp
  have hfp : Erdos67b.restrictToNat (zOmInt z) p = z := by
    rw [Erdos67b.restrictToNat, zOmInt, Erdos67b.positiveIntExtension_natCast hpp.pos,
      ArithmeticFunction.cardFactors_apply_prime hpp, pow_one]
  have hgp : Erdos67b.dirichletArchimedeanTwist χ 0 p = 1 := by
    rw [dirichletArchimedeanTwist_zero, hpq, map_one]
  rw [Erdos67b.pretentiousTerm, hfp, hgp, map_one, mul_one]
  rw [div_eq_mul_inv]

/-- **`ζ ≠ 1` is exactly what makes the certificate nontrivial**: the constant `1 − Re ζ` is
positive iff `z ≠ 1` for unimodular `z`. -/
theorem one_sub_re_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < 1 - z.re := by
  have hnorm : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at h
    simpa using h.symm
  rcases lt_or_eq_of_le (Complex.re_le_norm z) with h | h
  · rw [hz] at h; linarith
  · exfalso
    apply hz1
    have hre : z.re = 1 := by rw [h, hz]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    exact Complex.ext hre him

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.pretentiousDistSq_ge_class_sum
#print axioms NormalNumbers.CastingOut.one_sub_re_pos
