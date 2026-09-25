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

/-- **The initial-segment bound at `K` points, for an ARBITRARY multiplicative family.**
`initial_segment_bound_of_kElliott` with `zOmInt (z i)` replaced by a free family
`g : Fin K → ℤ → ℂ`.  Nothing in the window decomposition cared which multiplicative functions
were being correlated — `KPointLogElliott` is itself stated for a free `g` — so the generalisation
is free, and it is what the `ω_{>P}` side of the ledger needs: `depthAvg` correlates
`ζ_i^{ω_{>P}}`, which is multiplicative (not completely) and NOT of the form `z^Ω`.

The non-pretentiousness hypothesis is imposed on `g ⟨0, hK⟩` only, exactly as
`KPointLogElliott` imposes it on its first factor. -/
theorem initial_segment_bound_of_kElliott_gen {K : ℕ} (hK : 0 < K)
    (helliott : KPointLogElliott K) (c b : Fin K → ℕ)
    (hnd : NondegenerateForms c (fun i => ((b i : ℕ) : ℤ)))
    (g : Fin K → ℤ → ℂ) (hgmul : ∀ i, Erdos67b.IsMultiplicativeOnPositiveInt (g i))
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

#print axioms initial_segment_bound_of_kElliott_gen


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


/-- **The `K`-point rung, uniformly over the admissible tuples below `Y`.**  The `K`-point
`rung_two_uniform` (`C3MrtArchimedean`): `rung_multi_of_named_inputs` produces a base `A₀` and a
starting exponent `i₀` that both depend on the tuple `(d, a)`, while the `ε`-chase
(`multi_correlation_of_uniform_rung`) needs ONE `A` and ONE `I` serving every tuple at once.
Both are extracted by `exists_common_threshold` over the finite index set

    Fintype.piFinset (fun _ : Fin K => range (Y+1)) ×ˢ range (Y^K + 1)

— admissible because `d i ≤ Y` for every `i` and `a < lcm d ≤ Y^K` (`univLcm_le_pow`).
Degenerate tuples (some `d i = 0`, or `a` not in the joint class) get the dummy witness `2`;
their branch of the conclusion is vacuous. -/
theorem rung_multi_uniform {K : ℕ} (hK : 0 < K) (helliott : KPointLogElliott K)
    (hsave : TwistedPrimeSumSavingAllLevels) (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1)
    (εr : ℝ) (hεr : 0 < εr) (Y : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∃ I : ℕ,
      ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
        (∃ n₀ : ℕ, ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) →
        ∀ a : ℕ, a < (Finset.univ : Finset (Fin K)).lcm d →
          (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) → ∀ m : ℕ, I ≤ m →
          ‖∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine ((Finset.univ : Finset (Fin K)).lcm d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖
            ≤ (1 + Real.log ((A ^ I : ℕ) : ℝ)) + (m : ℝ) * (εr * Real.log A) := by
  classical
  set s : Finset ((Fin K → ℕ) × ℕ) :=
    (Fintype.piFinset fun _ : Fin K => Finset.range (Y + 1)) ×ˢ Finset.range (Y ^ K + 1) with hs
  have hmem : ∀ (d : Fin K → ℕ) (a : ℕ), (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
      a < (Finset.univ : Finset (Fin K)).lcm d → ((d, a) : (Fin K → ℕ) × ℕ) ∈ s := by
    intro d a hdY hdpos ha
    have hle : (Finset.univ : Finset (Fin K)).lcm d ≤ Y ^ K := univLcm_le_pow d hdpos hdY
    simp only [hs, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => Nat.lt_succ_of_le (hdY i), by omega⟩
  -- the per-tuple bound, abbreviated
  set B : (Fin K → ℕ) × ℕ → ℕ → ℕ → ℕ → Prop := fun p A i m =>
    ‖∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
        ∏ k : Fin K, zOmInt (z k)
          (Erdos67b.integerAffine ((Finset.univ : Finset (Fin K)).lcm p.1 / p.1 k)
            (((p.2 + (k : ℕ) + 1) / p.1 k : ℕ) : ℤ) j)‖
      ≤ (1 + Real.log ((A ^ i : ℕ) : ℝ)) + (m : ℝ) * (εr * Real.log A) with hB
  have hBmono : ∀ (p : (Fin K → ℕ) × ℕ) (A i i' m : ℕ), 1 ≤ A → i ≤ i' →
      B p A i m → B p A i' m := by
    intro p A i i' m hA1 hii h
    have : Real.log ((A ^ i : ℕ) : ℝ) ≤ Real.log ((A ^ i' : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (by positivity))
      exact_mod_cast Nat.pow_le_pow_right hA1 hii
    rw [hB] at h ⊢
    linarith
  -- Step 1: a common base `A`.
  obtain ⟨A₁, hA₁⟩ := exists_common_threshold s
    (fun p A₀ => 2 ≤ A₀ ∧ ((∀ i, 0 < p.1 i) → (∀ i : Fin K, p.1 i ∣ p.2 + (i : ℕ) + 1) →
      ∀ A : ℕ, A₀ ≤ A → ∃ i₀ : ℕ, ∀ m : ℕ, i₀ ≤ m → B p A i₀ m))
    (by
      intro p _ m n hmn hm
      exact ⟨le_trans hm.1 hmn, fun h1 h2 A hA => hm.2 h1 h2 A (le_trans hmn hA)⟩)
    (by
      intro p _
      by_cases h1 : ∀ i, 0 < p.1 i
      · by_cases h2 : ∀ i : Fin K, p.1 i ∣ p.2 + (i : ℕ) + 1
        · obtain ⟨A₀, hA₀2, hA₀⟩ := rung_multi_of_named_inputs hK helliott hsave z hz hz01
            (fun i => (Finset.univ : Finset (Fin K)).lcm p.1 / p.1 i)
            (fun i => ((p.2 + (i : ℕ) + 1) / p.1 i : ℕ))
            (nondegenerateForms_of_tuple p.1 h1 h2) εr hεr
          exact ⟨A₀, hA₀2, fun _ _ A hA => hA₀ A hA⟩
        · exact ⟨2, le_rfl, fun _ h => absurd h h2⟩
      · exact ⟨2, le_rfl, fun h _ => absurd h h1⟩)
  set A : ℕ := max 2 A₁ with hAdef
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA1A : A₁ ≤ A := le_max_right _ _
  have hA1 : 1 ≤ A := by omega
  -- Step 2: a common starting exponent `I`.
  obtain ⟨I, hI⟩ := exists_common_threshold s
    (fun p i => (∀ j, 0 < p.1 j) → (∀ j : Fin K, p.1 j ∣ p.2 + (j : ℕ) + 1) →
      ∀ m : ℕ, i ≤ m → B p A i m)
    (by
      intro p _ i i' hii hi h1 h2 m hm
      exact hBmono p A i i' m hA1 hii (hi h1 h2 m (le_trans hii hm)))
    (by
      intro p hp
      by_cases h1 : ∀ j, 0 < p.1 j
      · by_cases h2 : ∀ j : Fin K, p.1 j ∣ p.2 + (j : ℕ) + 1
        · obtain ⟨i₀, hi₀⟩ := (hA₁ p hp).2 h1 h2 A hA1A
          exact ⟨i₀, fun _ _ m hm => hi₀ m hm⟩
        · exact ⟨0, fun _ h => absurd h h2⟩
      · exact ⟨0, fun h => absurd h h1⟩)
  refine ⟨A, hA2, I, fun d hdY hdpos _ a ha hadvd m hm => ?_⟩
  exact hI (d, a) (hmem d a hdY hdpos ha) hdpos hadvd m hm

#print axioms rung_multi_uniform


/-- **The `K`-point correlation bound from the named inputs — the `D ≥ 3` rung.**  The `K`-point
`rung_two_correlation`: composing the uniform rung with the `K`-fold `ε`-chase, the log-averaged
`K`-point correlation of `z_i^{Ω}` at the consecutive shifts `n+1, …, n+K` is `o(log N)`, on
`KPointLogElliott K` (= Tao–Teräväinen's product log-Elliott at `K` points) and
`TwistedPrimeSumSavingAllLevels` (the Vinogradov–Korobov-type input) ALONE.

This closes the `K`-fold assembly: every other ingredient of the `D ≥ 3` route is now a proved
theorem of this repository. -/
theorem rung_multi_correlation {K : ℕ} (hK : 0 < K) (helliott : KPointLogElliott K)
    (hsave : TwistedPrimeSumSavingAllLevels) (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ n ∈ Finset.range N, ((((n : ℝ) + 1)⁻¹ : ℝ)) •
          ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N :=
  multi_correlation_of_uniform_rung hK z hz
    (fun εr hεr Y => rung_multi_uniform hK helliott hsave z hz hz01 εr hεr Y) ε hε

#print axioms rung_multi_correlation

end CastingOut

end NormalNumbers
