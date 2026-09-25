/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiTupleMass

/-!
# The per-tuple bound: step 4's analytic half

`inner_pair_bound` (`C3MrtTwoShift`) turns the rung's bound `R` on the Elliott window into the
per-pair bound `1 + (3 + R + log A)/(de)` that `full_sum_bound` consumes.  This file does the
same at `K` points, for `multi_full_sum_bound`.

The three ingredients of the `K = 2` proof are all *blind to the number of shifts* — they only
use `‖G j‖ ≤ 1` for the phase `G` — so they are extracted here in generic form and then applied
to `G j = ∏_{i<K} z_i^{Ω(c_i j + b_i)}`:

* `inner_harmonic_le_generic` — peel `j = 0` and transfer the weight `(Lj+a+1)^{-1} → L^{-1}j^{-1}`
  (`weight_transfer`), cost `(a+1)^{-1} + 2/L`;
* `window_gap_generic` — the gap between the rung's window `(0, A^{⌊log_A J⌋}]` and the cutoff
  `(0, J]` has harmonic mass `≤ 1 + log A` (`harmonic_gap_le_log`);
* `progression_sum_bound_generic` — their composition, the generic `progression_sum_bound`.

Only then does the `K`-dependence enter, through `multi_rung_spelling` (our weighted sum IS the
`K`-point correlation `kPointLogCorrelation` is stated with) and `inner_sum_multi_forms` (the
joint progression IS a single class, reindexed to linear forms).
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **Weight transfer, generic in the phase.**  `joint_inner_harmonic_le` with an arbitrary
unimodular-bounded `G`; the two-shift proof never used the shape of the phase. -/
theorem inner_harmonic_le_generic {L a : ℕ} (hL : 0 < L) (haL : a + 1 ≤ L) (J : ℕ)
    (G : ℕ → ℂ) (hG : ∀ j, ‖G j‖ ≤ 1) :
    ‖∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ (((a : ℝ) + 1)⁻¹ + 2 / (L : ℝ))
        + (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
  classical
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hsplit : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 J := by simp
  rw [hsplit, Finset.sum_insert h0]
  have hwt : ∀ j : ℕ, (((L * j + a : ℕ) : ℝ) + 1)⁻¹ = (((L * j + (a + 1) : ℕ) : ℝ))⁻¹ := by
    intro j; push_cast; ring
  have hrw : ∑ j ∈ Finset.Icc 1 J, ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j
      = ∑ j ∈ Finset.Icc 1 J, ((((L * j + (a + 1) : ℕ) : ℝ))⁻¹ : ℝ) • G j :=
    Finset.sum_congr rfl fun j _ => by rw [hwt j]
  have htrans := weight_transfer (L := L) (a := a + 1) hL haL J G hG
  have hhead : ‖((((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G 0‖ ≤ ((a : ℝ) + 1)⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hcast : (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ = ((a : ℝ) + 1)⁻¹ := by norm_num
    rw [hcast, abs_of_nonneg (by positivity)]
    calc ((a : ℝ) + 1)⁻¹ * ‖G 0‖ ≤ ((a : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hG 0) (by positivity)
      _ = ((a : ℝ) + 1)⁻¹ := mul_one _
  have htail : ‖∑ j ∈ Finset.Icc 1 J, ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ 2 / (L : ℝ) + (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
    rw [hrw]
    have hsub := norm_sub_norm_le
      (∑ j ∈ Finset.Icc 1 J, ((((L * j + (a + 1) : ℕ) : ℝ))⁻¹ : ℝ) • G j)
      ((L : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j)
    have hnsm : ‖(L : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖
        = (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnsm] at hsub
    have := le_trans hsub htrans
    linarith
  refine le_trans (norm_add_le _ _) ?_
  linarith [hhead, htail]

/-- **The window gap, generic in the phase.**  Extending the rung's window `(0, A^{⌊log_A J⌋}]`
to the cutoff `(0, J]` costs at most `1 + log A`, an `N`-independent constant. -/
theorem window_gap_generic {A J : ℕ} (hA : 2 ≤ A) (hJ1 : 1 ≤ J) (G : ℕ → ℂ)
    (hG : ∀ j, ‖G j‖ ≤ 1) {R : ℝ}
    (hrung : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R) :
    ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R + (1 + Real.log A) := by
  set m := Nat.log A J with hm
  set Z : ℕ → ℂ := fun j => (((j : ℝ))⁻¹ : ℝ) • G j with hZ
  have hlow : A ^ m ≤ J := Nat.pow_log_le_self A (by omega)
  have hsplit := Finset.sum_Ioc_consecutive Z (Nat.zero_le (A ^ m)) hlow
  have hgap : ‖∑ j ∈ Finset.Ioc (A ^ m) J, Z j‖ ≤ 1 + Real.log A := by
    have hterm : ∀ j ∈ Finset.Ioc (A ^ m) J, ‖Z j‖ ≤ ((j : ℝ))⁻¹ := by
      intro j _
      rw [hZ]
      simp only []
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ((j : ℝ))⁻¹ * ‖G j‖ ≤ ((j : ℝ))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hG j) (by positivity)
        _ = ((j : ℝ))⁻¹ := mul_one _
    exact le_trans (norm_sum_le _ _)
      (le_trans (Finset.sum_le_sum hterm) (harmonic_gap_le_log hA hJ1))
  have hset : Finset.Icc 1 J = Finset.Ioc 0 J := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hset, ← hsplit]
  exact le_trans (norm_add_le _ _) (add_le_add hrung hgap)

/-- **The generic `progression_sum_bound`.**  Weight transfer plus window gap. -/
theorem progression_sum_bound_generic {L a A J : ℕ} (hL : 0 < L) (haL : a + 1 ≤ L)
    (hA : 2 ≤ A) (hJ1 : 1 ≤ J) (G : ℕ → ℂ) (hG : ∀ j, ‖G j‖ ≤ 1) {R : ℝ}
    (hrung : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R) :
    ‖∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ (((a : ℝ) + 1)⁻¹ + 2 / (L : ℝ)) + (L : ℝ)⁻¹ * (R + (1 + Real.log A)) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h1 := inner_harmonic_le_generic hL haL J G hG
  have h2 := window_gap_generic hA hJ1 G hG hrung
  have h3 : (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖
      ≤ (L : ℝ)⁻¹ * (R + (1 + Real.log A)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

#print axioms inner_harmonic_le_generic
#print axioms window_gap_generic
#print axioms progression_sum_bound_generic


/-- **The rung's spelling, at `K` points.**  Our weighted sum over the progression variable is
literally the summand of `kPointLogCorrelation`. -/
theorem multi_rung_spelling {K : ℕ} (z : ℕ → ℂ) (c b : Fin K → ℕ) (hc : ∀ i, 0 < c i) (J : ℕ) :
    ∑ j ∈ Finset.Ioc 0 J, (((j : ℝ))⁻¹ : ℝ) •
        ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors (c i * j + b i)
      = ∑ j ∈ Finset.Ioc 0 J, (Erdos67b.harmonicWeight j : ℂ) *
          ∏ i : Fin K, zOmInt (z i) (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j) := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Ioc.1 hj).1
  have hprod : ∏ i : Fin K, zOmInt (z i) (Erdos67b.integerAffine (c i) ((b i : ℕ) : ℤ) j)
      = ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors (c i * j + b i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have hpos : 0 < c i * j + b i := by
      have : 0 < c i * j := Nat.mul_pos (hc i) (by omega)
      omega
    exact zOmInt_integerAffine (z i) (c i) (b i) j hpos
  rw [hprod, Erdos67b.harmonicWeight, Complex.real_smul]

open scoped Classical in
/-- **The per-tuple bound.**  Granting the `K`-point rung's bound `R` on the Elliott window, the
harmonically weighted inner sum over the joint progression of a positive, solvable tuple `d`
satisfies exactly `multi_full_sum_bound`'s hypothesis:

    ‖Inner d‖  ≤  1 + (3 + R + log A) / lcm(d) .

This is `inner_pair_bound` at `K` points.  Note there is **no coprimality hypothesis**: the
joint progression is one class mod `lcm(d)` whatever the pairwise gcds are. -/
theorem inner_multi_bound {K N A : ℕ} (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (hA : 2 ≤ A) {R : ℝ} (hR0 : 0 ≤ R)
    (hrung : ∀ a : ℕ, a < (Finset.univ : Finset (Fin K)).lcm d →
      (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) →
      ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A
            ((N - 1 - a) / (Finset.univ : Finset (Fin K)).lcm d)),
          (Erdos67b.harmonicWeight j : ℂ) *
            ∏ i : Fin K, zOmInt (z i)
              (Erdos67b.integerAffine ((Finset.univ : Finset (Fin K)).lcm d / d i)
                (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖ ≤ R) :
    ‖∑ n ∈ (range N).filter (fun n => ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
        harmW n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)‖
      ≤ 1 + (3 + R + Real.log A) / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ) := by
  classical
  set L : ℕ := (Finset.univ : Finset (Fin K)).lcm d with hLdef
  have hL : 0 < L := univLcm_pos d hd
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  have hRHS : 0 ≤ (3 + R + Real.log A) / (L : ℝ) := by positivity
  obtain ⟨a, haL, hadvd, heq⟩ := inner_sum_multi_forms (N := N) d hd hn₀ z harmW
  rw [heq]
  by_cases haN : a < N
  · rw [filter_linear_lt_eq_range hL haN]
    set J := (N - 1 - a) / L with hJ
    set G : ℕ → ℂ := fun j =>
      ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((L / d i) * j + (a + (i : ℕ) + 1) / d i)
      with hG
    have hGnorm : ∀ j, ‖G j‖ ≤ 1 := by
      intro j
      rw [hG]
      simp only []
      rw [norm_prod]
      refine le_of_eq ?_
      refine Finset.prod_eq_one fun i _ => ?_
      rw [norm_pow, hz i, one_pow]
    have hrw : ∑ j ∈ Finset.range (J + 1), harmW (L * j + a) * G j
        = ∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j :=
      Finset.sum_congr rfl fun j _ => harmW_smul _ _
    show ‖∑ j ∈ Finset.range (J + 1), harmW (L * j + a) * G j‖ ≤ _
    rw [hrw]
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ1
    · rw [hJ0]
      have hone : Finset.range (0 + 1) = ({0} : Finset ℕ) := by
        ext j; simp only [Finset.mem_range, Finset.mem_singleton]; omega
      rw [hone, Finset.sum_singleton]
      have hnorm : ‖((((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G 0‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          have : (0 : ℝ) ≤ ((L * 0 + a : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        calc (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ * ‖G 0‖
            ≤ 1 * 1 := mul_le_mul h1 (hGnorm 0) (norm_nonneg _) zero_le_one
          _ = 1 := by ring
      linarith
    · have hspell := multi_rung_spelling z (fun i => L / d i)
        (fun i => (a + (i : ℕ) + 1) / d i)
        (fun i => Nat.div_pos (Nat.le_of_dvd hL (Finset.dvd_lcm (Finset.mem_univ i)))
          (hd i))
        (A ^ Nat.log A J)
      have hrung' : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R := by
        rw [hG]
        simp only []
        rw [hspell]
        exact hrung a haL hadvd
      have hbound := progression_sum_bound_generic (L := L) (a := a) (A := A) (J := J)
        hL (by omega) hA hJ1 G hGnorm hrung'
      refine le_trans hbound ?_
      have h1 : ((a : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        linarith
      have heq2 : 2 / (L : ℝ) + (L : ℝ)⁻¹ * (R + (1 + Real.log A))
          = (3 + R + Real.log A) / (L : ℝ) := by
        field_simp
        ring
      linarith
  · have hempty : (Finset.range N).filter (fun j => L * j + a < N) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
      have := (Finset.mem_filter.1 hj).2
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    linarith

#print axioms multi_rung_spelling
#print axioms inner_multi_bound

end CastingOut

end NormalNumbers
