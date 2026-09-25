/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiChase

/-!
# The `K`-point rung from `KPointLogElliott`

`initial_segment_bound_of_elliott` (`C3MrtRungTwo`) converts the dependency's nonasymptotic
two-point Elliott input into a bound on the initial segment `(0, A^m]`: the head `(0, A^{i₀}]`
costs its harmonic mass `1 + log A^{i₀}`, and each dyadic-in-`A` window `(A^{i-1}, A^i]` is
*exactly* one `elliottLogCorrelation` at `X = A^i`, `W = A`, so it costs `ε·log A`.

This file is the `K`-point transcription.  Nothing in the argument is two-point: the window
decomposition (`elliottLogWindow_pow`, `norm_sum_Ioc_pow_le_from`), the head bound
(`norm_head_le`) and the harmonic weight are all blind to the number of factors, and
`kPointLogCorrelation` is *defined* as the sum over `elliottLogWindow` of the same weight times
the product.  The only `K`-sensitive points are:

* `‖∏_i zOmInt (z i) (…)‖ ≤ 1` (each factor is unimodular);
* the non-pretentiousness hypothesis, which `KPointLogElliott` imposes on the FIRST factor only
  — so the archimedean certificate `nonPretentious_zOm` of laps 18–21 carries over verbatim,
  with no new archimedean work at any `K`.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-- **The initial-segment bound at `K` points.**  The `K`-point
`initial_segment_bound_of_elliott`. -/
theorem initial_segment_bound_of_kElliott {K : ℕ} (hK : 0 < K)
    (helliott : KPointLogElliott K) (c b : Fin K → ℕ)
    (hnd : NondegenerateForms c (fun i => ((b i : ℕ) : ℤ)))
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∀ i₀ : ℕ,
      (∀ i : ℕ, i₀ < i → ∀ q : ℕ, 0 < q → q ≤ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
          |t| ≤ (A : ℝ) * (A ^ i : ℕ) →
            (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
              (Erdos67b.restrictToNat (zOmInt (z 0))) χ t (A ^ i)) →
      ∀ m : ℕ, i₀ ≤ m →
        ‖∑ j ∈ Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
            ∏ i : Fin K, zOmInt (z i) (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖
          ≤ (1 + Real.log (A ^ i₀ : ℕ)) + (m : ℝ) * (ε * Real.log A) := by
  obtain ⟨A₀, hA₀2, hA₀⟩ := helliott c (fun i => ((b i : ℕ) : ℤ)) hnd ε hε
  refine ⟨A₀, hA₀2, fun A hA i₀ hpret m him => ?_⟩
  have hA1 : 1 ≤ A := by omega
  set f : ℕ → ℂ := fun j => (Erdos67b.harmonicWeight j : ℂ) *
    ∏ i : Fin K, zOmInt (z i) (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j) with hf
  have hprodnorm : ∀ j : ℕ,
      ‖∏ i : Fin K, zOmInt (z i) (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖ ≤ 1 := by
    intro j
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => norm_zOmInt_le_one (hz i) _)
  have hwin : ∀ i ∈ Icc (i₀ + 1) m, ‖∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j‖ ≤ ε * Real.log A := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi1 : 1 ≤ i := by omega
    have hWX : A ≤ A ^ i := by
      calc A = A ^ 1 := (pow_one A).symm
        _ ≤ A ^ i := Nat.pow_le_pow_right hA1 hi1
    have hcorr : ∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j
        = kPointLogCorrelation (fun i => zOmInt (z i)) c (fun i => ((b i : ℕ) : ℤ))
            (A ^ i) A := by
      rw [kPointLogCorrelation, ← elliottLogWindow_pow (by omega) hi1]
    rw [hcorr]
    refine hA₀ A (A ^ i) A hA (le_refl A) hWX (fun i => zOmInt (z i))
      (fun i => isMultiplicativeOnPositiveInt_zOmInt (z i))
      (fun i n => norm_zOmInt_le_one (hz i) n) ?_
    intro ii hi0 q hq hqA χ t ht
    rw [show ((ii : ℕ)) = 0 from hi0]
    exact hpret i (by omega) q hq hqA χ t (by exact_mod_cast ht)
  have hhead : ‖∑ j ∈ Ioc 0 (A ^ i₀), f j‖ ≤ 1 + Real.log (A ^ i₀ : ℕ) := by
    refine norm_head_le f 0 ?_
    intro j hj
    rw [hf]
    simp only []
    rw [norm_mul]
    have h1 : ‖((Erdos67b.harmonicWeight j : ℝ) : ℂ)‖ = ((j : ℝ))⁻¹ := by
      rw [Erdos67b.harmonicWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [h1]
    calc ((j : ℝ))⁻¹ * ‖∏ i : Fin K, zOmInt (z i)
          (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖
        ≤ ((j : ℝ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hprodnorm j) (by positivity)
      _ = ((j : ℝ))⁻¹ := by ring
  have hBnn : (0 : ℝ) ≤ ε * Real.log A := by
    have : (0 : ℝ) ≤ Real.log A := Real.log_natCast_nonneg A
    positivity
  exact norm_sum_Ioc_pow_le_from hA1 f i₀ m him _ _ hBnn hhead hwin

#print axioms initial_segment_bound_of_kElliott


/-- **The `K` linear forms of a tuple are pairwise nondegenerate.**  Lap 39's `multi_forms_det`
in the shape `KPointLogElliott` asks for: the determinant of forms `i ≠ j` is
`L(j−i)/(d_i d_j) ≠ 0`.  No coprimality, no arithmetic hypothesis beyond what the CRT supplies
by construction. -/
theorem nondegenerateForms_of_tuple {K : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) {a : ℕ}
    (ha : ∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) :
    NondegenerateForms (fun i : Fin K => (Finset.univ : Finset (Fin K)).lcm d / d i)
      (fun i : Fin K => (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ)) := by
  set L : ℕ := (Finset.univ : Finset (Fin K)).lcm d with hLdef
  have hL : 0 < L := univLcm_pos d hd
  have hdvd : ∀ i : Fin K, d i ∣ L := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  refine ⟨fun i => Nat.div_pos (Nat.le_of_dvd hL (hdvd i)) (hd i), fun i j hij hdet => ?_⟩
  have hkey := multi_forms_det (L := L) (a := a) (di := d i) (dj := d j)
    (i := (i : ℕ)) (j := (j : ℕ)) (hdvd i) (hdvd j) (ha i) (ha j)
  rw [hdet, mul_zero] at hkey
  have hLZ : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hne : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≠ 0 := by
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    omega
  exact absurd hkey.symm (mul_ne_zero hLZ hne)

/-- **The `K`-point rung from the named inputs.**  `rung_two_of_named_inputs` at `K` points:
`KPointLogElliott K` supplies the correlation, `TwistedPrimeSumSavingAllLevels` +
`nonPretentious_zOm` the archimedean certificate for the first factor. -/
theorem rung_multi_of_named_inputs {K : ℕ} (hK : 0 < K) (helliott : KPointLogElliott K)
    (hsave : TwistedPrimeSumSavingAllLevels) (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1)
    (c b : Fin K → ℕ) (hnd : NondegenerateForms c (fun i => ((b i : ℕ) : ℤ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∃ i₀ : ℕ, ∀ m : ℕ, i₀ ≤ m →
      ‖∑ j ∈ Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
          ∏ i : Fin K, zOmInt (z i) (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖
        ≤ (1 + Real.log (A ^ i₀ : ℕ)) + (m : ℝ) * (ε * Real.log A) := by
  obtain ⟨A₀, hA₀2, hA₀⟩ := initial_segment_bound_of_kElliott hK helliott c b hnd z hz ε hε
  refine ⟨A₀, hA₀2, fun A hA => ?_⟩
  obtain ⟨T, hT⟩ := hsave A
  obtain ⟨X₀, hX₀⟩ := nonPretentious_zOm (hz 0) hz01 hT
  refine ⟨X₀, fun m hm => hA₀ A hA X₀ (fun i hi q hq hqA χ t ht => ?_) m hm⟩
  have hA2 : 2 ≤ A := le_trans hA₀2 hA
  have hpow : X₀ ≤ A ^ i := by
    have h1 : i < 2 ^ i := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ i ≤ A ^ i := Nat.pow_le_pow_left hA2 i
    omega
  exact hX₀ (A ^ i) hpow q hq hqA χ t (by exact_mod_cast ht)

#print axioms nondegenerateForms_of_tuple
#print axioms rung_multi_of_named_inputs

end CastingOut

end NormalNumbers
