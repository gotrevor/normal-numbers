import NormalNumbers.ElliottLadder
import NormalNumbers.ElliottMultStatement

open NormalNumbers.ElliottMultStatement

/-!
# From an integer-indexed `g` to the zero-extension of its natural restriction

Leaf 2, Case B, step zero.  `Erdos67b.NonasymptoticLogElliott` quantifies over `g : ℤ → ℂ` whose
values at **nonpositive** integers are unconstrained (only `‖g z‖ ≤ 1`), whereas the whole Case-B
machinery (`ElliottRandomize`, `ElliottExpand`, `ElliottRestricted`, `AffineCMLogElliott`) is stated
for `positiveIntExtension` of a natural-indexed function.

The two correlations differ only at those `n` in the window where `a₁n+b₁ ≤ 0` or `a₂n+b₂ ≤ 0`.
Since `aᵢ ≥ 1` and `n ≥ 1`, such `n` satisfy `n ≤ |bᵢ|`, so there are at most `|b₁| + |b₂|` of them
and each contributes at most `2·harmonicWeight n ≤ 2`.  The difference is therefore bounded by the
**absolute** constant `2(|b₁|+|b₂|)`, which the threshold `A₀` absorbs (`W ≥ A₀` makes
`2(|b₁|+|b₂|) ≤ (ε/4) log W`).

## Main results

* `norm_sub_posExt_le` — the `2(|b₁|+|b₂|)` comparison.
* `completelyMultiplicative_restrictToNat` — `IsCoprimeMultOnPosInt g` (which has *no*
  coprimality hypothesis, hence is complete multiplicativity) descends to `restrictToNat g`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottZeroExt

open Erdos67b

noncomputable section

/-- `IsCoprimeMultOnPosInt` is complete multiplicativity, and it restricts. -/
theorem completelyMultiplicative_restrictToNat {g : ℤ → ℂ} (hm : IsMultiplicativeOnPositiveInt g) :
    IsCompletelyMultiplicativeOnPositive (restrictToNat g) := by
  refine ⟨?_, ?_⟩
  · simpa [restrictToNat] using hm.1
  · intro m n hm' hn'
    simpa [restrictToNat] using hm.2 m n hm' hn'

/-- The restriction is `1`-bounded, and multiplicative on coprime pairs (a fortiori). -/
theorem coprime_mul_restrictToNat {g : ℤ → ℂ} (hm : IsCoprimeMultOnPosInt g)
    (x y : ℕ) (hxy : Nat.Coprime x y) :
    restrictToNat g (x * y) = restrictToNat g x * restrictToNat g y := by
  have hone : restrictToNat g 1 = 1 := by simpa [restrictToNat] using hm.1
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.coprime_zero_left] at hxy
    subst hxy
    rw [Nat.mul_one, hone, mul_one]
  · rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [Nat.coprime_zero_right] at hxy
      subst hxy
      rw [Nat.one_mul, hone, one_mul]
    · simpa [restrictToNat] using hm.2 x y hx hy hxy

/-- **The comparison.**  Replacing `gᵢ` by the zero-extension of its natural restriction changes the
correlation by at most the absolute constant `2(|b₁|+|b₂|)`. -/
theorem norm_sub_posExt_le {g₁ g₂ : ℤ → ℂ} (h₁ : ∀ z : ℤ, ‖g₁ z‖ ≤ 1) (h₂ : ∀ z : ℤ, ‖g₂ z‖ ≤ 1)
    {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (b₁ b₂ : ℤ) (X W : ℕ) :
    ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W
      - elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
          (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W‖
      ≤ 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := by
  classical
  set P₁ : ℤ → ℂ := positiveIntExtension (restrictToNat g₁) with hP₁
  set P₂ : ℤ → ℂ := positiveIntExtension (restrictToNat g₂) with hP₂
  have hP₁b : ∀ z : ℤ, ‖P₁ z‖ ≤ 1 := by
    intro z; rw [hP₁, positiveIntExtension]
    split_ifs with h
    · simpa [restrictToNat] using h₁ (z.toNat : ℤ)
    · simp
  have hP₂b : ∀ z : ℤ, ‖P₂ z‖ ≤ 1 := by
    intro z; rw [hP₂, positiveIntExtension]
    split_ifs with h
    · simpa [restrictToNat] using h₂ (z.toNat : ℤ)
    · simp
  set S : Finset ℕ := (elliottLogWindow X W).filter
    (fun n => ¬ (0 < integerAffine a₁ b₁ n ∧ 0 < integerAffine a₂ b₂ n)) with hS
  have hdiff : elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W
      - elliottLogCorrelation P₁ P₂ a₁ a₂ b₁ b₂ X W
      = ∑ n ∈ elliottLogWindow X W,
          ((harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) * g₂ (integerAffine a₂ b₂ n)
            - (harmonicWeight n : ℂ) * P₁ (integerAffine a₁ b₁ n) * P₂ (integerAffine a₂ b₂ n)) := by
    rw [elliottLogCorrelation, elliottLogCorrelation, ← Finset.sum_sub_distrib]
  have hzero : ∀ n ∈ elliottLogWindow X W, n ∉ S →
      (harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) * g₂ (integerAffine a₂ b₂ n)
        - (harmonicWeight n : ℂ) * P₁ (integerAffine a₁ b₁ n) * P₂ (integerAffine a₂ b₂ n) = 0 := by
    intro n hn hnS
    have hgood : 0 < integerAffine a₁ b₁ n ∧ 0 < integerAffine a₂ b₂ n := by
      by_contra hc
      exact hnS (Finset.mem_filter.mpr ⟨hn, hc⟩)
    have e₁ : P₁ (integerAffine a₁ b₁ n) = g₁ (integerAffine a₁ b₁ n) := by
      rw [hP₁, positiveIntExtension, if_pos hgood.1, restrictToNat,
        Int.toNat_of_nonneg hgood.1.le]
    have e₂ : P₂ (integerAffine a₂ b₂ n) = g₂ (integerAffine a₂ b₂ n) := by
      rw [hP₂, positiveIntExtension, if_pos hgood.2, restrictToNat,
        Int.toNat_of_nonneg hgood.2.le]
    rw [e₁, e₂, sub_self]
  rw [hdiff, ← Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnS => hzero n hn hnS)]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ S,
      ‖(harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) * g₂ (integerAffine a₂ b₂ n)
        - (harmonicWeight n : ℂ) * P₁ (integerAffine a₁ b₁ n) * P₂ (integerAffine a₂ b₂ n)‖
      ≤ 2 := by
    intro n hn
    have hnpos : 0 < n := (mem_elliottLogWindow.mp (Finset.mem_filter.mp hn).1).1
    have hw : ‖(harmonicWeight n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (harmonicWeight_nonneg n)]
      rw [harmonicWeight]
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      rw [inv_le_one_iff₀]; right; exact this
    have hA : ‖(harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) *
        g₂ (integerAffine a₂ b₂ n)‖ ≤ 1 := by
      rw [norm_mul, norm_mul]
      have hstep := mul_le_mul (mul_le_mul hw (h₁ (integerAffine a₁ b₁ n)) (norm_nonneg _)
        zero_le_one) (h₂ (integerAffine a₂ b₂ n)) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1 * 1)
      linarith [hstep]
    have hB : ‖(harmonicWeight n : ℂ) * P₁ (integerAffine a₁ b₁ n) *
        P₂ (integerAffine a₂ b₂ n)‖ ≤ 1 := by
      rw [norm_mul, norm_mul]
      have hstep := mul_le_mul (mul_le_mul hw (hP₁b (integerAffine a₁ b₁ n)) (norm_nonneg _)
        zero_le_one) (hP₂b (integerAffine a₂ b₂ n)) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1 * 1)
      linarith [hstep]
    calc ‖_ - _‖ ≤ ‖(harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) *
          g₂ (integerAffine a₂ b₂ n)‖ + ‖(harmonicWeight n : ℂ) * P₁ (integerAffine a₁ b₁ n) *
          P₂ (integerAffine a₂ b₂ n)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : S.card ≤ b₁.natAbs + b₂.natAbs := by
    have hsub : S ⊆ Finset.Icc 1 (b₁.natAbs + b₂.natAbs) := by
      intro n hn
      obtain ⟨hnw, hbad⟩ := Finset.mem_filter.mp hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp hnw).1
      refine Finset.mem_Icc.mpr ⟨hnpos, ?_⟩
      have ha₁z : (1 : ℤ) ≤ (a₁ : ℤ) := by exact_mod_cast ha₁
      have ha₂z : (1 : ℤ) ≤ (a₂ : ℤ) := by exact_mod_cast ha₂
      have hnz : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
      have h1 : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
      have h2 : (b₂.natAbs : ℤ) = |b₂| := (Int.abs_eq_natAbs b₂).symm
      have hgoal : (n : ℤ) ≤ (b₁.natAbs : ℤ) + (b₂.natAbs : ℤ) := by
        rcases not_and_or.mp hbad with hc | hc
        · have hle : integerAffine a₁ b₁ n ≤ 0 := by omega
          rw [integerAffine] at hle
          have : (n : ℤ) ≤ -b₁ := by nlinarith
          have hb : -b₁ ≤ |b₁| := neg_le_abs b₁
          rw [h1, h2]
          have : (0 : ℤ) ≤ |b₂| := abs_nonneg b₂
          linarith
        · have hle : integerAffine a₂ b₂ n ≤ 0 := by omega
          rw [integerAffine] at hle
          have : (n : ℤ) ≤ -b₂ := by nlinarith
          have hb : -b₂ ≤ |b₂| := neg_le_abs b₂
          rw [h1, h2]
          have : (0 : ℤ) ≤ |b₁| := abs_nonneg b₁
          linarith
      exact_mod_cast hgoal
    have := Finset.card_le_card hsub
    simpa using this
  have hcardR : (S.card : ℝ) ≤ ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := by exact_mod_cast hcard
  calc (S.card : ℝ) * 2 = 2 * (S.card : ℝ) := by ring
    _ ≤ 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := by linarith

end

end NormalNumbers.ElliottZeroExt
