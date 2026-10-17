/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsBoundary

/-!
# Algebra for one prime Stoneham class

The two-generator specialization of the cyclotomic rank condition.  Two powers of a primitive
`d`-th root are rationally linearly independent exactly when their exponent difference does not
become a sign after doubling.
-/

namespace NormalNumbers.StonehamPrimeClass

/-- Equality of the squares of two powers of a primitive root is the corresponding doubled
exponent congruence. -/
lemma primitiveRoot_two_mul_sub_dvd_iff_sq_pow_eq_sq_pow
    {d m₁ m₂ : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) (hd : d ≠ 0) :
    ((d : ℤ) ∣ 2 * ((m₂ : ℤ) - m₁)) ↔ (ζ ^ m₂) ^ 2 = (ζ ^ m₁) ^ 2 := by
  let u : ℂˣ := (hζ.isUnit hd).unit
  have hu : IsPrimitiveRoot u d := hζ.isUnit_unit hd
  have huOrder : orderOf u = d := hu.eq_orderOf.symm
  have hcoe : (u : ℂ) = ζ := by simp [u]
  constructor
  · intro hdvd
    have hdvd' : (d : ℤ) ∣ ((2 * m₂ : ℕ) : ℤ) - ((2 * m₁ : ℕ) : ℤ) := by
      convert hdvd using 1 <;> push_cast <;> ring
    have hmod : 2 * m₁ ≡ 2 * m₂ [MOD d] := (Nat.modEq_iff_dvd).2 hdvd'
    have hupow : u ^ (2 * m₁) = u ^ (2 * m₂) := by
      rw [(hu.isOfFinOrder hd).pow_eq_pow_iff_modEq, huOrder]
      exact hmod
    have hpow : ζ ^ (2 * m₁) = ζ ^ (2 * m₂) := by
      simpa only [← hcoe, Units.val_pow_eq_pow_val] using congrArg Units.val hupow
    simpa [mul_comm, pow_mul] using hpow.symm
  · intro h
    have hpow : ζ ^ (2 * m₁) = ζ ^ (2 * m₂) := by
      simpa [mul_comm, pow_mul] using h.symm
    have hupow : u ^ (2 * m₁) = u ^ (2 * m₂) := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, hcoe] using hpow
    have hmod : 2 * m₁ ≡ 2 * m₂ [MOD d] := by
      rw [← huOrder, ← (hu.isOfFinOrder hd).pow_eq_pow_iff_modEq]
      exact hupow
    have hdvd' : (d : ℤ) ∣ ((2 * m₂ : ℕ) : ℤ) - ((2 * m₁ : ℕ) : ℤ) :=
      (Nat.modEq_iff_dvd).mp hmod
    convert hdvd' using 1 <;> push_cast <;> ring

/-- Two powers of a nontrivial-order primitive complex root are rationally linearly independent
exactly when the root order does not divide twice their exponent difference. -/
lemma linearIndependent_two_powers_iff
    {d m₁ m₂ : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) (hd : d ≠ 0) :
    LinearIndependent ℚ ![ζ ^ m₁, ζ ^ m₂] ↔
      ¬ ((d : ℤ) ∣ 2 * ((m₂ : ℤ) - m₁)) := by
  letI : NeZero d := ⟨hd⟩
  rw [primitiveRoot_two_mul_sub_dvd_iff_sq_pow_eq_sq_pow hζ hd, linearIndependent_fin2]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, ne_eq]
  constructor
  · rintro ⟨_, hli⟩ hsq
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with heq | heq
    · exact hli 1 (by simpa [Algebra.smul_def] using heq)
    · apply hli (-1)
      rw [Algebra.smul_def]
      norm_num
      rw [heq]
      ring
  · intro hsq
    refine ⟨pow_ne_zero _ (hζ.ne_zero hd), ?_⟩
    intro a ha
    apply hsq
    have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hd
    have hnorm₁ : ‖ζ ^ m₁‖ = 1 := by
      rw [norm_pow, hnorm, one_pow]
    have hnorm₂ : ‖ζ ^ m₂‖ = 1 := by
      rw [norm_pow, hnorm, one_pow]
    have habs : ‖(a : ℂ)‖ = 1 := by
      have hn := congrArg norm ha
      simpa [Algebra.smul_def, norm_mul, hnorm₁, hnorm₂] using hn
    have ha2 : (a : ℂ) ^ 2 = 1 := by
      rw [Complex.norm_ratCast] at habs
      norm_cast at habs ⊢
      nlinarith [sq_abs a]
    have hpow := congrArg (fun z : ℂ => z ^ 2) ha
    calc
      (ζ ^ m₂) ^ 2 = 1 * (ζ ^ m₂) ^ 2 := by ring
      _ = (a : ℂ) ^ 2 * (ζ ^ m₂) ^ 2 := by rw [ha2]
      _ = ((a : ℂ) * ζ ^ m₂) ^ 2 := by rw [mul_pow]
      _ = (ζ ^ m₁) ^ 2 := hpow

/-- A canonical primitive complex root realizes the two-power criterion.  Packaging its
construction keeps analytic consumers independent of the exponential normalization details. -/
lemma exists_primitiveRoot_linearIndependent_two_powers_iff
    (d m₁ m₂ : ℕ) (hd : d ≠ 0) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ d ∧
      (LinearIndependent ℚ ![ζ ^ m₁, ζ ^ m₂] ↔
        ¬ ((d : ℤ) ∣ 2 * ((m₂ : ℤ) - m₁))) := by
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / d)
  have hζ : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp d hd
  exact ⟨ζ, hζ, linearIndependent_two_powers_iff hζ hd⟩

end NormalNumbers.StonehamPrimeClass
