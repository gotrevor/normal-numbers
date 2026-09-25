import NormalNumbers.ElliottRandomize

/-!
# The pretentious transfer to the two-point cover

Leaf 2 (`NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM`), Case B, step (1).

`NormalNumbers.ElliottRandomize.exists_cover_pair_ge` replaces a pair of `1`-bounded
multiplicative functions `g₁, g₂` by a pair of *unimodular* multiplicative functions `u₁, u₂`
with a larger correlation.  To feed the unimodular pair into the dependency's proved unit-circle
theorem we must also carry across the *non-pretentiousness* hypothesis.  That is what this file
does.

Two obstacles, both handled here.

1. **The dependency's triangle inequality is unusable.**  `Erdos67b.pretentiousTerm_triangle_sq`
   assumes all three functions are unimodular at `p`.  Here the middle-man `g₁` is only
   `1`-bounded, and the target `χ · n^{it}` is not unimodular either (it vanishes at `p ∣ q`).
   `pretentiousTerm_triangle_bounded` re-proves it for `1`-bounded arguments, with constant `3`:
   writing `u = 1 - Re(a b̄)`, `v = 1 - Re(b c̄)`,
   `1 - Re(a c̄) = [1 - (‖a‖²+‖c‖²)/2] + ‖a-c‖²/2 ≤ (u + v) + 2(u + v)`,
   using `1 - x² ≤ 2(1-x)` on `[0,1]`, `Re(a b̄) ≤ ‖a‖‖b‖ ≤ ‖a‖`, and
   `‖a-c‖² ≤ 2(‖a-b‖² + ‖b-c‖²)` with `‖a-b‖² ≤ 2u`.

2. **The distance from `g` to its cover is deterministic.**  Because the lift's perturbation is
   orthogonal to `z`, `(u p * conj (g p)).re = ‖g p‖²` for *every* `ω`, so
   `pretentiousDistSq g u X = ∑_{p ≤ X} (1 - ‖g p‖²)/p ≤ 2 ∑_{p ≤ X} (1 - ‖g p‖)/p`.
   There is no Markov step and no good event: the bound holds for all covers simultaneously.

Combining, a Case-B hypothesis `∑_{p ≤ X}(1 - ‖g p‖)/p ≤ D₀` upgrades
`MRTNonpretentious g A X` to `MRTNonpretentious u A' X` for any `A' ≤ A/3 - 2 D₀`.

## Main results

* `pretentiousTerm_triangle_bounded`, `pretentiousDistSq_triangle_bounded`
* `pretentiousDistSq_cover_eq`, `pretentiousDistSq_cover_le`
* `mrtNonpretentious_transfer`
-/

open scoped BigOperators ComplexConjugate
open Finset Erdos67b

namespace NormalNumbers.ElliottPretentiousTransfer

/-! ## A `1`-bounded triangle inequality -/

/-- The scalar heart of the `1`-bounded triangle inequality.  Note the constant `3` rather than
the unimodular `2`: the extra slack pays for the defect `1 - ‖a‖²`. -/
theorem one_sub_re_le_three {a b c : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    1 - (a * conj c).re ≤ 3 * ((1 - (a * conj b).re) + (1 - (b * conj c).re)) := by
  have key : ∀ x y : ℂ, ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * conj y).re := by
    intro x y
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
  have hac := key a c
  have hab := key a b
  have hbc := key b c
  -- `Re (x * conj y) ≤ ‖x‖ * ‖y‖`
  have hre : ∀ x y : ℂ, (x * conj y).re ≤ ‖x‖ * ‖y‖ := by
    intro x y
    calc (x * conj y).re ≤ ‖x * conj y‖ := Complex.re_le_norm _
      _ = ‖x‖ * ‖y‖ := by rw [norm_mul, RCLike.norm_conj]
  have h1 := hre a b
  have h2 := hre b c
  have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by ring_nf
      _ ≤ ‖a - b‖ + ‖b - c‖ := norm_add_le _ _
  have hsq : ‖a - c‖ ^ 2 ≤ 2 * (‖a - b‖ ^ 2 + ‖b - c‖ ^ 2) := by
    nlinarith [norm_nonneg (a - c), norm_nonneg (a - b), norm_nonneg (b - c),
      sq_nonneg (‖a - b‖ - ‖b - c‖)]
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c,
    norm_nonneg (a - b), norm_nonneg (b - c), norm_nonneg (a - c)]

theorem pretentiousTerm_triangle_bounded {f g h : ℕ → ℂ} {p : ℕ}
    (hf : ‖f p‖ ≤ 1) (hg : ‖g p‖ ≤ 1) (hh : ‖h p‖ ≤ 1) :
    pretentiousTerm f h p ≤ 3 * (pretentiousTerm f g p + pretentiousTerm g h p) := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · simp [pretentiousTerm, hp0]
  have hpden : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  rw [pretentiousTerm, pretentiousTerm, pretentiousTerm]
  have hrw : 3 * ((1 - (f p * conj (g p)).re) / (p : ℝ) + (1 - (g p * conj (h p)).re) / (p : ℝ))
      = (3 * ((1 - (f p * conj (g p)).re) + (1 - (g p * conj (h p)).re))) / (p : ℝ) := by ring
  rw [hrw]
  gcongr
  exact one_sub_re_le_three hf hg hh

theorem pretentiousDistSq_triangle_bounded {f g h : ℕ → ℂ} {x : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (hh : ∀ p, p.Prime → ‖h p‖ ≤ 1) :
    pretentiousDistSq f h x ≤ 3 * (pretentiousDistSq f g x + pretentiousDistSq g h x) := by
  rw [pretentiousDistSq, pretentiousDistSq, pretentiousDistSq, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := (mem_primesUpTo.mp hp).1
  exact pretentiousTerm_triangle_bounded (hf p hp') (hg p hp') (hh p hp')

/-! ## The deterministic distance from `g` to its cover -/

/-- If `u` is a lift of `g` at every prime `≤ x` — which the two-point cover is, for **every**
`ω` — then the pretentious distance from `g` to `u` is the completely explicit
`∑_{p ≤ x} (1 - ‖g p‖²)/p`. -/
theorem pretentiousDistSq_cover_eq {g u : ℕ → ℂ} {x : ℕ}
    (hlift : ∀ p : ℕ, p.Prime → p ≤ x → (u p * conj (g p)).re = ‖g p‖ ^ 2) :
    pretentiousDistSq g u x = ∑ p ∈ primesUpTo x, (1 - ‖g p‖ ^ 2) / (p : ℝ) := by
  rw [pretentiousDistSq]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp', hpx⟩ := mem_primesUpTo.mp hp
  rw [pretentiousTerm]
  congr 1
  rw [← Complex.conj_re (g p * conj (u p))]
  simp only [map_mul, RCLike.conj_conj]
  rw [mul_comm, hlift p hp' hpx]

/-- The Case-B bound: `1 - r² ≤ 2 (1 - r)` for `r ∈ [0,1]` turns the explicit distance into
twice the Case-B sum `∑_{p ≤ x}(1 - ‖g p‖)/p`. -/
theorem pretentiousDistSq_cover_le {g u : ℕ → ℂ} {x : ℕ} (hg : ∀ n : ℕ, ‖g n‖ ≤ 1)
    (hlift : ∀ p : ℕ, p.Prime → p ≤ x → (u p * conj (g p)).re = ‖g p‖ ^ 2) :
    pretentiousDistSq g u x ≤ 2 * ∑ p ∈ primesUpTo x, (1 - ‖g p‖) / (p : ℝ) := by
  rw [pretentiousDistSq_cover_eq hlift, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.pos
  rw [← mul_div_assoc]
  gcongr
  nlinarith [hg p, norm_nonneg (g p)]

/-! ## The transfer -/

/-- **The pretentious hypothesis transfers to the cover.**  `A'` absorbs the triangle constant `3`
and twice the Case-B sum; nothing here depends on `ω`. -/
theorem mrtNonpretentious_transfer {g u : ℕ → ℂ} {A A' X : ℕ} {D₀ : ℝ}
    (hg : ∀ n : ℕ, ‖g n‖ ≤ 1) (hu : ∀ n : ℕ, ‖u n‖ = 1)
    (hlift : ∀ p : ℕ, p.Prime → p ≤ X → (u p * conj (g p)).re = ‖g p‖ ^ 2)
    (hcaseB : ∑ p ∈ primesUpTo X, (1 - ‖g p‖) / (p : ℝ) ≤ D₀)
    (hA : MRTNonpretentious g A X)
    (hA'le : A' ≤ A) (hA' : (A' : ℝ) ≤ (A : ℝ) / 3 - 2 * D₀) :
    MRTNonpretentious u A' X := by
  intro q hq hqA' χ t ht
  have hqA : q ≤ A := le_trans hqA' hA'le
  have htA : |t| ≤ (A : ℝ) * X := by
    refine le_trans ht ?_
    have : (A' : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA'le
    exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
  have hlow := hA q hq hqA χ t htA
  -- triangle: `d(g,χ) ≤ 3 (d(g,u) + d(u,χ))`
  have hgb : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1 := fun p _ => hg p
  have hub : ∀ p : ℕ, p.Prime → ‖u p‖ ≤ 1 := fun p _ => (hu p).le
  have hχb : ∀ p : ℕ, p.Prime → ‖dirichletArchimedeanTwist χ t p‖ ≤ 1 := by
    intro p hp
    rw [dirichletArchimedeanTwist, norm_mul, norm_archimedeanTwist hp.pos, mul_one]
    exact χ.norm_le_one _
  have htri := pretentiousDistSq_triangle_bounded (f := g)
    (g := u) (h := dirichletArchimedeanTwist χ t) (x := X) hgb hub hχb
  have hgu := pretentiousDistSq_cover_le (x := X) hg hlift
  have hD : pretentiousDistSq g u X ≤ 2 * D₀ := by
    refine le_trans hgu ?_
    linarith
  rw [pretentiousDistSqToTwist]
  rw [pretentiousDistSqToTwist] at hlow
  linarith

end NormalNumbers.ElliottPretentiousTransfer
