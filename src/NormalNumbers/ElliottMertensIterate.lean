import NormalNumbers.ElliottScaleDescent
import NormalNumbers.ElliottHall

/-!
# Iterating the square-block Mertens bound

Leaf 2, Case B.  `ElliottScaleDescent.reciprocalPrimeInterval_le_log_two_add` bounds the prime mass
of `(X', X]` by the absolute `log 2 + 2B` **when `X ≤ X'^2`**.  The Case-B repair of the
dichotomy-scale obstruction (see `PENDING_WORK.md`, laps 71–75) needs the same statement for
`X ≤ X'^(2^k)`, with the bound `k(log 2 + 2B)` — still absolute once `k` is fixed by `ε`.

The iteration is the obvious one: `X'`, `X'^2`, `X'^4`, … each step squares the scale, so `k`
steps reach `X'^(2^k)`; the chain is set up by `reciprocalPrimeInterval_add`.

## Main results

* `reciprocalPrimeInterval_add` — additivity over a split point.
* `reciprocalPrimeInterval_iter` — `≤ k(log 2 + 2B)` when `X ≤ X'^(2^k)`.
* `primeDefect_le_add` — `Σ_X ≤ Σ_L + (prime mass of `(L,X]`)`: the Case-B sum grows by at most the
  reciprocal mass, which is what the repair needs.
* `mrtNonpretentious_descend_iter` — the descent over `k` squarings.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottMertensIterate

open Erdos67b Erdos67b.PrimeEstimates NormalNumbers.ElliottScaleDescent
open NormalNumbers.ElliottEulerBound

noncomputable section

theorem reciprocalPrimeInterval_add {X' M X : ℕ} (h1 : X' ≤ M) (h2 : M ≤ X) :
    reciprocalPrimeInterval X' X
      = reciprocalPrimeInterval X' M + reciprocalPrimeInterval M X := by
  classical
  have hsplit : primesInInterval X' X = primesInInterval X' M ∪ primesInInterval M X := by
    ext p
    simp only [mem_primesInInterval, Finset.mem_union]
    constructor
    · rintro ⟨hlo, hhi, hp⟩
      by_cases hpM : p ≤ M
      · exact Or.inl ⟨hlo, hpM, hp⟩
      · exact Or.inr ⟨by omega, hhi, hp⟩
    · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
      · exact ⟨a, by omega, c⟩
      · exact ⟨by omega, b, c⟩
  have hdisj : Disjoint (primesInInterval X' M) (primesInInterval M X) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have := (mem_primesInInterval.mp hp).2.1
    have := (mem_primesInInterval.mp hp').1
    omega
  rw [reciprocalPrimeInterval, reciprocalPrimeInterval, reciprocalPrimeInterval, hsplit,
    Finset.sum_union hdisj]

theorem reciprocalPrimeInterval_nonneg (X' X : ℕ) : 0 ≤ reciprocalPrimeInterval X' X := by
  rw [reciprocalPrimeInterval]
  exact Finset.sum_nonneg fun p _ => by positivity

/-- **The iterated square-block bound.** -/
theorem reciprocalPrimeInterval_iter {k : ℕ} : ∀ {X' X : ℕ}, 2 ≤ X' → X' ≤ X →
    X ≤ X' ^ (2 ^ k) → reciprocalPrimeInterval X' X ≤ (k : ℝ) * (Real.log 2 + 2 * mertensBound) := by
  induction k with
  | zero =>
      intro X' X h2 hXY hsq
      simp only [pow_zero, pow_one] at hsq
      have hXeq : X = X' := le_antisymm hsq hXY
      subst hXeq
      have : primesInInterval X X = ∅ := by
        ext p
        simp only [mem_primesInInterval, Finset.notMem_empty, iff_false]
        rintro ⟨h1, h2, -⟩
        omega
      rw [reciprocalPrimeInterval, this]
      simp
  | succ k ih =>
      intro X' X h2 hXY hsq
      set M : ℕ := min X (X' ^ 2) with hM
      have hX'M : X' ≤ M := by
        refine le_min hXY ?_
        calc X' = X' ^ 1 := (pow_one X').symm
          _ ≤ X' ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hMX : M ≤ X := min_le_left _ _
      have hMsq : M ≤ X' ^ 2 := min_le_right _ _
      have hM2 : 2 ≤ M := le_trans h2 hX'M
      have hstep : reciprocalPrimeInterval X' M ≤ Real.log 2 + 2 * mertensBound :=
        NormalNumbers.ElliottScaleDescent.reciprocalPrimeInterval_le_log_two_add h2 hX'M hMsq
      have hrest : X ≤ M ^ (2 ^ k) := by
        rcases le_or_gt X (X' ^ 2) with hle | hgt
        · have hMeq : M = X := by omega
          rw [hMeq]
          calc X = X ^ 1 := (pow_one X).symm
            _ ≤ X ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
        · have hMeq : M = X' ^ 2 := by omega
          rw [hMeq, ← pow_mul]
          calc X ≤ X' ^ (2 ^ (k + 1)) := hsq
            _ = X' ^ (2 * 2 ^ k) := by rw [pow_succ']
      have hIH := ih hM2 hMX hrest
      rw [reciprocalPrimeInterval_add hX'M hMX]
      push_cast
      linarith

/-- **The Case-B sum grows by at most the reciprocal prime mass.** -/
theorem primeDefect_le_add {g : ℤ → ℂ} (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {L X : ℕ} (h : L ≤ X) :
    primeDefect (NormalNumbers.ElliottCaseA.normDivArith g) X
      ≤ primeDefect (NormalNumbers.ElliottCaseA.normDivArith g) L
        + reciprocalPrimeInterval L X := by
  classical
  set f := NormalNumbers.ElliottCaseA.normDivArith g with hf
  have hsplit : Nat.primesLE X = Nat.primesLE L ∪ primesInInterval L X := by
    ext p
    simp only [Nat.primesLE, Nat.mem_primesBelow, mem_primesInInterval, Finset.mem_union]
    constructor
    · rintro ⟨hlt, hp⟩
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨by omega, hp⟩
      · exact Or.inr ⟨by omega, by omega, hp⟩
    · rintro (⟨a, b⟩ | ⟨a, b, c⟩)
      · exact ⟨by omega, b⟩
      · exact ⟨by omega, c⟩
  have hdisj : Disjoint (Nat.primesLE L) (primesInInterval L X) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 := (Nat.mem_primesBelow.mp hp).1
    have h2 := (mem_primesInInterval.mp hp').1
    omega
  rw [primeDefect, primeDefect, hsplit, Finset.sum_union hdisj, reciprocalPrimeInterval]
  have hterm : ∀ p ∈ primesInInterval L X, ((p : ℝ)⁻¹ - f p) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hpp : p.Prime := (mem_primesInInterval.mp hp).2.2
    have hnn : 0 ≤ f p := by
      rw [hf]
      exact NormalNumbers.ElliottCaseA.normDivArith_nonneg g p
    linarith
  have := Finset.sum_le_sum hterm
  linarith

/-- **The descent over `k` squarings.** -/
theorem mrtNonpretentious_descend_iter {f : ℕ → ℂ} (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1)
    {A A'' X X' k : ℕ} (hMRT : MRTNonpretentious f A X)
    (h2 : 2 ≤ X') (hXY : X' ≤ X) (hsq : X ≤ X' ^ (2 ^ k))
    (hAle : A'' ≤ A) (hA : (A'' : ℝ) ≤ (A : ℝ) - (k : ℝ) * mrtDescentCost) :
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
  have hmass := reciprocalPrimeInterval_iter (k := k) h2 hXY hsq
  rw [pretentiousDistSqToTwist] at hlow ⊢
  rw [mrtDescentCost] at hA
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  nlinarith [hmass, hdesc, hA, hlow]

end

end NormalNumbers.ElliottMertensIterate
