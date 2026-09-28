/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultElliott
import NormalNumbers.C3MrtMultiRung

/-!
# The initial-segment rung on the merely-multiplicative anchor

`C3MrtMultElliott` showed that the class-restricted `K`-point correlation of `ζ^ω` **is** a
`kPointLogCorrelation` along the forms `M₀·n + (r+i+1)`.  This file runs the window
decomposition on it, producing the rung in exactly the shape the `ε`-chase consumes.

* `initial_segment_bound_of_kElliottMult` — `initial_segment_bound_of_kElliott_gen` (lap 50)
  transcribed onto `KPointLogElliottMult`.  The window decomposition never looked at *which*
  multiplicativity the family had, so the transcription is verbatim; only the hypothesis
  on `g` changes.
* **`rung_class_of_named_inputs_mult`** — the rung for `ζ^ω` along a residue class, on
  `KPointLogElliottMult K` + `TwistedPrimeSumSavingAllLevels` alone.

## What is NOT here, and that is the point

The route this replaces needs, between `KPointLogElliott` and the same conclusion:

* `C3MrtOmegaBridge` — the `z^ω = z^Ω ⋆ g` expansion over the powerful numbers;
* `C3MrtMultiForms`/`MultiMass`/`MultiTupleMass` — the joint class of a divisor tuple, its
  harmonic mass with both gains, and `prod_le_lcm_mul_pow`'s `K^{K²}`;
* `C3MrtMultiTrunc`/`ProgTrunc` — truncation of the tuple sum at `Y`;
* `C3MrtMultiInner`/`ProgInner` — the per-tuple inner layer;
* `rung_multi_uniform_prog` — `exists_common_threshold` twice, to find ONE `A` and ONE `I`
  serving every tuple `(d, a)` at once.

Here there are no tuples, so there is nothing to truncate, nothing to take a common threshold
over, and no budget: `rung_class_of_named_inputs_mult` already produces the single `A`, `i₀` the
chase needs.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-- **The initial-segment bound at `K` points on Elliott's own hypothesis class.**
`initial_segment_bound_of_kElliott_gen` with `IsCoprimeMultiplicativeInt` in place of the
dependency's complete-multiplicativity predicate.  The window decomposition is untouched. -/
theorem initial_segment_bound_of_kElliottMult {K : ℕ} (hK : 0 < K)
    (helliott : KPointLogElliottMult K) (c b : Fin K → ℕ)
    (hnd : NondegenerateForms c (fun i => ((b i : ℕ) : ℤ)))
    (g : Fin K → ℤ → ℂ) (hgmul : ∀ i, IsCoprimeMultiplicativeInt (g i))
    (hgn : ∀ i, ∀ n : ℤ, ‖g i n‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∀ i₀ : ℕ,
      (∀ i : ℕ, i₀ < i → ∀ q : ℕ, 0 < q → q ≤ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
          |t| ≤ (A : ℝ) * (A ^ i : ℕ) →
            (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
              (Erdos67b.restrictToNat (g ⟨0, hK⟩)) χ t (A ^ i)) →
      ∀ m : ℕ, i₀ ≤ m →
        ‖∑ j ∈ Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
            ∏ i : Fin K, g i (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖
          ≤ (1 + Real.log (A ^ i₀ : ℕ)) + (m : ℝ) * (ε * Real.log A) := by
  obtain ⟨A₀, hA₀2, hA₀⟩ := helliott c (fun i => ((b i : ℕ) : ℤ)) hnd ε hε
  refine ⟨A₀, hA₀2, fun A hA i₀ hpret m him => ?_⟩
  have hA1 : 1 ≤ A := by omega
  set f : ℕ → ℂ := fun j => (Erdos67b.harmonicWeight j : ℂ) *
    ∏ i : Fin K, g i (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j) with hf
  have hprodnorm : ∀ j : ℕ,
      ‖∏ i : Fin K, g i (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖ ≤ 1 := by
    intro j
    rw [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hgn i _)
  have hwin : ∀ i ∈ Icc (i₀ + 1) m, ‖∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j‖ ≤ ε * Real.log A := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi1 : 1 ≤ i := by omega
    have hWX : A ≤ A ^ i := by
      calc A = A ^ 1 := (pow_one A).symm
        _ ≤ A ^ i := Nat.pow_le_pow_right hA1 hi1
    have hcorr : ∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j
        = kPointLogCorrelation g c (fun i => ((b i : ℕ) : ℤ)) (A ^ i) A := by
      rw [kPointLogCorrelation, ← elliottLogWindow_pow (by omega) hi1]
    rw [hcorr]
    refine hA₀ A (A ^ i) A hA (le_refl A) hWX g hgmul hgn ?_
    intro ii hi0 q hq hqA χ t ht
    have hii : ii = (⟨0, hK⟩ : Fin K) := Fin.ext hi0
    rw [hii]
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
    calc ((j : ℝ))⁻¹ * ‖∏ i : Fin K, g i
          (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)‖
        ≤ ((j : ℝ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hprodnorm j) (by positivity)
      _ = ((j : ℝ))⁻¹ := by ring
  have hBnn : (0 : ℝ) ≤ ε * Real.log A := by
    have : (0 : ℝ) ≤ Real.log A := Real.log_natCast_nonneg A
    positivity
  exact norm_sum_Ioc_pow_le_from hA1 f i₀ m him _ _ hBnn hhead hwin

/-- **The rung for `ζ^ω` along a residue class, on two named inputs and nothing else.**
`KPointLogElliottMult K` supplies the window bound; `TwistedPrimeSumSavingAllLevels` supplies
the archimedean certificate, through `nonPretentious_zOmega` — which is laps 18–21 verbatim,
because the pretentious distance sees a function only at the primes.

This is `rung_multi_of_named_inputs` **and** `rung_multi_uniform_prog` at once: the single `A`
and the single `i₀` come out directly, with no `exists_common_threshold` over divisor tuples,
because there are no divisor tuples. -/
theorem rung_class_of_named_inputs_mult {K : ℕ} (hK : 0 < K)
    (helliott : KPointLogElliottMult K) (hsave : TwistedPrimeSumSavingAllLevels)
    {Mo : ℕ} (hMo : 0 < Mo) (r : ℕ)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∃ i₀ : ℕ, ∀ m : ℕ, i₀ ≤ m →
      ‖∑ j ∈ Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
          ∏ i : Fin K, (z (i : ℕ)) ^ omegaNat (Mo * j + (r + (i : ℕ) + 1))‖
        ≤ (1 + Real.log (A ^ i₀ : ℕ)) + (m : ℝ) * (ε * Real.log A) := by
  obtain ⟨A₀, hA₀2, hA₀⟩ := initial_segment_bound_of_kElliottMult hK helliott
    (fun _ : Fin K => Mo) (fun i : Fin K => r + (i : ℕ) + 1)
    (nondegenerateForms_class (K := K) hMo r)
    (fun i : Fin K => zOmegaInt (z (i : ℕ)))
    (fun i => isCoprimeMultiplicativeInt_zOmegaInt _)
    (fun i n => norm_zOmegaInt_le_one (hz _) n) ε hε
  refine ⟨A₀, hA₀2, fun A hA => ?_⟩
  obtain ⟨T, hT⟩ := hsave A
  obtain ⟨X₀, hX₀⟩ := nonPretentious_zOmega (hz 0) hz01 hT
  refine ⟨X₀, fun m hm => ?_⟩
  have hbound := hA₀ A hA X₀ (fun i hi q hq hqA χ t ht => ?_) m hm
  · refine le_trans (le_of_eq ?_) hbound
    refine congrArg norm (Finset.sum_congr rfl fun j _ => ?_)
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Erdos67b.integerAffine]
    have hcast : (Mo : ℤ) * (j : ℤ) + ((r + (i : ℕ) + 1 : ℕ) : ℤ)
        = ((Mo * j + (r + (i : ℕ) + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, zOmegaInt_natCast _ (by positivity)]
  · have hA2 : 2 ≤ A := le_trans hA₀2 hA
    have hpow : X₀ ≤ A ^ i := by
      have h1 : i < 2 ^ i := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ i ≤ A ^ i := Nat.pow_le_pow_left hA2 i
      omega
    exact hX₀ (A ^ i) hpow q hq hqA χ t (by exact_mod_cast ht)

#print axioms initial_segment_bound_of_kElliottMult
#print axioms rung_class_of_named_inputs_mult

end CastingOut

end NormalNumbers
