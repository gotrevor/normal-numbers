import NormalNumbers.ElliottPretentiousTransfer

/-!
# Descending the scale of the non-pretentiousness hypothesis

Leaf 2, Case B.  The substitutions of `ElliottRestricted` produce correlations at the reduced
scale `X' ≈ X/d`, so `AffineCMLogElliott` must be fed `MRTNonpretentious f A'' X'` while the
hypothesis of `NonasymptoticLogElliott` supplies it only at the *full* scale `X`.

Non-pretentiousness does **not** descend for free — the distance is a sum over `p ≤ x`, so
shrinking `x` can only decrease it.  But it decreases by at most the reciprocal mass of the primes
in `(X', X]`, and once `X ≤ X'^2` that mass is an absolute constant by Mertens
(`Erdos67b.PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add`, the same square-block
argument as `expWeightedPrimeTail_le_log_two_add`).  So `A'' = A − 2(log 2 + 2B)` works, and
`X ≤ X'^2` is guaranteed by taking the threshold `A₀ ≥ d²` — legitimate because `d ≤ D` is fixed
before `A₀`.

## Main results

* `reciprocalPrimeInterval_le_log_two_add` — the square-block Mertens bound.
* `pretentiousDistSq_descend` — the distance loses at most `2·(that mass)`.
* `mrtNonpretentious_descend` — the descent, with the absolute constant `mrtDescentCost`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottScaleDescent

open Erdos67b Erdos67b.PrimeEstimates

noncomputable section

/-- The absolute cost of halving the logarithm of the scale. -/
def mrtDescentCost : ℝ := 2 * (Real.log 2 + 2 * mertensBound)

theorem mrtDescentCost_nonneg : 0 ≤ mrtDescentCost := by
  rw [mrtDescentCost]
  have := mertensBound_nonneg
  have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- **The square-block Mertens bound.**  If `X ≤ X'^2` then the primes in `(X', X]` carry an
absolute reciprocal mass. -/
theorem reciprocalPrimeInterval_le_log_two_add {X' X : ℕ} (h2 : 2 ≤ X') (hXY : X' ≤ X)
    (hsq : X ≤ X' ^ 2) :
    reciprocalPrimeInterval X' X ≤ Real.log 2 + 2 * mertensBound := by
  have hmass := reciprocalPrimeInterval_le_log_log_sub_add h2 hXY
  have hlogX : 0 < Real.log (X' : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X' by omega))
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXsqpos : (0 : ℝ) < ((X' ^ 2 : ℕ) : ℝ) := by positivity
  have hlogYle : Real.log (X : ℝ) ≤ Real.log ((X' ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log hXpos (by exact_mod_cast hsq)
  have hlogYpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hloglogYle : Real.log (Real.log (X : ℝ)) ≤ Real.log (Real.log ((X' ^ 2 : ℕ) : ℝ)) :=
    Real.log_le_log hlogYpos hlogYle
  have hsquare : Real.log (Real.log ((X' ^ 2 : ℕ) : ℝ)) - Real.log (Real.log (X' : ℝ))
      = Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    rw [Real.log_mul (by norm_num) hlogX.ne']
    ring
  linarith

/-- **The distance descends up to the prime mass of the gap.** -/
theorem pretentiousDistSq_descend {f g : ℕ → ℂ}
    (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    {X' X : ℕ} (hXY : X' ≤ X) :
    pretentiousDistSq f g X ≤ pretentiousDistSq f g X' + 2 * reciprocalPrimeInterval X' X := by
  classical
  have hsplit : primesUpTo X = primesUpTo X' ∪ primesInInterval X' X := by
    ext p
    simp only [mem_primesUpTo, Finset.mem_union, mem_primesInInterval]
    constructor
    · rintro ⟨hp, hpX⟩
      by_cases hpX' : p ≤ X'
      · exact Or.inl ⟨hp, hpX'⟩
      · exact Or.inr ⟨by omega, hpX, hp⟩
    · rintro (⟨hp, h⟩ | ⟨h1, h2, hp⟩)
      · exact ⟨hp, by omega⟩
      · exact ⟨hp, h2⟩
  have hdisj : Disjoint (primesUpTo X') (primesInInterval X' X) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 := (mem_primesUpTo.mp hp).2
    have h2 := (mem_primesInInterval.mp hp').1
    omega
  rw [pretentiousDistSq, hsplit, Finset.sum_union hdisj]
  have hterm : ∀ p ∈ primesInInterval X' X, pretentiousTerm f g p ≤ 2 * (p : ℝ)⁻¹ := by
    intro p hp
    have hpp : p.Prime := (mem_primesInInterval.mp hp).2.2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    rw [pretentiousTerm]
    have hre : -(1 : ℝ) ≤ (f p * conj (g p)).re := by
      have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
        rw [norm_mul, RCLike.norm_conj]
        calc ‖f p‖ * ‖g p‖ ≤ 1 * 1 :=
              mul_le_mul (hf p hpp) (hg p hpp) (norm_nonneg _) (by norm_num)
          _ = 1 := by ring
      have := Complex.abs_re_le_norm (f p * conj (g p))
      have habs : |(f p * conj (g p)).re| ≤ 1 := le_trans this hnorm
      cases abs_le.mp habs with
      | intro h1 h2 => exact h1
    rw [div_le_iff₀ hppos]
    have : (2 : ℝ) * (p : ℝ)⁻¹ * (p : ℝ) = 2 := by field_simp
    rw [this]
    linarith
  have hbd : ∑ p ∈ primesInInterval X' X, pretentiousTerm f g p
      ≤ 2 * reciprocalPrimeInterval X' X := by
    rw [reciprocalPrimeInterval, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  rw [pretentiousDistSq]
  linarith

/-- **The descent.**  Non-pretentiousness at scale `X` with parameter `A` gives it at the reduced
scale `X'` with parameter `A''`, provided `X ≤ X'^2` and `A'' ≤ A − mrtDescentCost`. -/
theorem mrtNonpretentious_descend {f : ℕ → ℂ} (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1)
    {A A'' X X' : ℕ} (hMRT : MRTNonpretentious f A X)
    (h2 : 2 ≤ X') (hXY : X' ≤ X) (hsq : X ≤ X' ^ 2)
    (hAle : A'' ≤ A) (hA : (A'' : ℝ) ≤ (A : ℝ) - mrtDescentCost) :
    MRTNonpretentious f A'' X' := by
  intro q hq hqA χ t ht
  have hqA' : q ≤ A := le_trans hqA hAle
  have htA : |t| ≤ (A : ℝ) * X := by
    refine le_trans ht ?_
    have h1 : (A'' : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAle
    have h2' : (X' : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXY
    have hA0 : (0 : ℝ) ≤ (A'' : ℝ) := by positivity
    have hX0 : (0 : ℝ) ≤ (X' : ℝ) := by positivity
    calc (A'' : ℝ) * X' ≤ (A : ℝ) * X' := by nlinarith
      _ ≤ (A : ℝ) * X := by nlinarith [Nat.cast_nonneg (α := ℝ) A]
  have hlow := hMRT q hq hqA' χ t htA
  have hχb : ∀ p : ℕ, p.Prime → ‖dirichletArchimedeanTwist χ t p‖ ≤ 1 := by
    intro p hp
    rw [dirichletArchimedeanTwist, norm_mul, norm_archimedeanTwist hp.pos, mul_one]
    exact χ.norm_le_one _
  have hdesc := pretentiousDistSq_descend hf hχb (X' := X') (X := X) hXY
  have hmass := reciprocalPrimeInterval_le_log_two_add h2 hXY hsq
  rw [pretentiousDistSqToTwist] at hlow ⊢
  rw [mrtDescentCost] at hA
  linarith

end

end NormalNumbers.ElliottScaleDescent
