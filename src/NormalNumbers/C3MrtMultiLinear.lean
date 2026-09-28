/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiForms

/-!
# The `K`-point inner sum, as a correlation along `K` linear forms

This is the `K`-fold `inner_sum_linear_forms` (`C3MrtLinearForms`, `D = 2`).  After
`sum_pow_omega_multi_eq` (lap 36) expands the `K`-fold bridge, each tuple `d : Fin K → ℕ`
contributes an inner sum over the joint progression `{n : ∀ i, d i ∣ n + i + 1}`.  Lap 39's
`joint_class_multi` says that progression is a single class mod `L = lcm(d_i)` — with **no**
coprimality hypothesis, which is exactly why the `K ≥ 3` case works at all.  Reindexing
`n = L·j + a` therefore turns the inner sum into

    ∑_j F(Lj + a) · ∏_{i<K} z_i^{Ω((L/d_i)·j + (a+i+1)/d_i)} ,

a `K`-point correlation of the completely multiplicative `z_i^Ω` along the `K` linear forms
`(L/d_i)·X + (a+i+1)/d_i`.  Lap 39's `multi_forms_det` already shows those forms are pairwise
nondegenerate (determinant `L(j−i)/(d_i d_j) ≠ 0`), so this is verbatim the hypothesis shape of
`KPointLogElliott K` / `ProductLogElliott K`.

The index set of the `j`-sum is `{j : L·j + a < N}`, which `filter_linear_lt_eq_range`
(`C3MrtTwoShift`) identifies with `range ((N−1−a)/L + 1)` — an initial segment, as the Elliott
input requires.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- Positivity of the joint modulus, in the `Fin K` convention lap 39 uses. -/
theorem univLcm_pos {K : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) :
    0 < (Finset.univ : Finset (Fin K)).lcm d := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [Finset.lcm_eq_zero_iff] at h0
  obtain ⟨i, _, hzero⟩ := h0
  exact absurd hzero (hd i).ne'

/-- **The `i`-th linear form.**  With `d i ∣ L`, reindexing `n = L·j + a` sends the `i`-th
argument `(n + i + 1)/d_i` to `(L/d_i)·j + (a+i+1)/d_i`. -/
theorem shift_div_eq_linear_multi {L a di k : ℕ} (hdi : 0 < di) (hdiL : di ∣ L) (j : ℕ) :
    (L * j + a + k + 1) / di = (L / di) * j + (a + k + 1) / di := by
  have hLd : di * (L / di) = L := Nat.mul_div_cancel' hdiL
  have h : L * j + a + k + 1 = (a + k + 1) + di * ((L / di) * j) := by
    rw [← mul_assoc, hLd]; ring
  rw [h, Nat.add_mul_div_left _ _ hdi, Nat.add_comm]

/-- **The base point of the joint class is representable below `L`.** -/
theorem joint_base_mod {K : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) :
    ∀ i : Fin K, d i ∣ n₀ % (Finset.univ : Finset (Fin K)).lcm d + (i : ℕ) + 1 := by
  intro i
  have hdiL : d i ∣ (Finset.univ : Finset (Fin K)).lcm d := Finset.dvd_lcm (Finset.mem_univ i)
  have hmod : n₀ % (Finset.univ : Finset (Fin K)).lcm d ≡ n₀
      [MOD (Finset.univ : Finset (Fin K)).lcm d] := Nat.mod_modEq _ _
  have hmodi : n₀ % (Finset.univ : Finset (Fin K)).lcm d ≡ n₀ [MOD d i] := hmod.of_dvd hdiL
  have hshift : n₀ % (Finset.univ : Finset (Fin K)).lcm d + (i : ℕ) + 1
      ≡ n₀ + (i : ℕ) + 1 [MOD d i] := (hmodi.add_right _).add_right 1
  have hzero : n₀ + (i : ℕ) + 1 ≡ 0 [MOD d i] := (Nat.modEq_zero_iff_dvd).2 (hn₀ i)
  exact (Nat.modEq_zero_iff_dvd).1 (hshift.trans hzero)

/-- **The `K`-point inner sum, as a `K`-point correlation along `K` linear forms.**

The `K`-fold `inner_sum_linear_forms`.  No coprimality is needed anywhere: `joint_class_multi`
supplies the class, and `multi_forms_det` supplies the nondegeneracy. -/
theorem inner_sum_multi_forms {K N : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (z : ℕ → ℂ) (F : ℕ → ℂ) :
    ∃ a : ℕ, a < (Finset.univ : Finset (Fin K)).lcm d ∧
      (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) ∧
      ∑ n ∈ (range N).filter (fun n => ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
          F n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)
        = ∑ j ∈ (range N).filter
              (fun j => (Finset.univ : Finset (Fin K)).lcm d * j + a < N),
            F ((Finset.univ : Finset (Fin K)).lcm d * j + a) *
              ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors
                (((Finset.univ : Finset (Fin K)).lcm d / d i) * j + (a + (i : ℕ) + 1) / d i) := by
  classical
  set L : ℕ := (Finset.univ : Finset (Fin K)).lcm d with hLdef
  have hL : 0 < L := univLcm_pos d hd
  set a : ℕ := n₀ % L with ha
  have haL : a < L := Nat.mod_lt _ hL
  have hadvd : ∀ i : Fin K, d i ∣ a + (i : ℕ) + 1 := joint_base_mod d hd hn₀
  refine ⟨a, haL, hadvd, ?_⟩
  have hfil : (range N).filter (fun n => ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1)
      = (range N).filter (fun n => n % L = a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hdvd⟩
      refine ⟨hn, ?_⟩
      have hmodn := (joint_class_multi d hn₀ n).1 hdvd
      rw [ha]
      exact hmodn
    · rintro ⟨hn, hmodn⟩
      refine ⟨hn, (joint_class_multi d hn₀ n).2 ?_⟩
      rw [ha] at hmodn
      exact hmodn
  rw [hfil, sum_over_class_eq hL haL]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [shift_div_eq_linear_multi (hd i) (Finset.dvd_lcm (Finset.mem_univ i)) j]

/-- **The degenerate tuple contributes nothing.**  If the joint progression has no solution at
all, the inner sum is empty.  Together with `inner_sum_multi_forms` this covers every tuple. -/
theorem inner_sum_multi_empty {K N : ℕ} (d : Fin K → ℕ)
    (hno : ¬ ∃ n₀ : ℕ, ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (z : ℕ → ℂ) (F : ℕ → ℂ) :
    ∑ n ∈ (range N).filter (fun n => ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
        F n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)
      = 0 := by
  classical
  refine Finset.sum_eq_zero fun n hn => ?_
  exact absurd ⟨n, (Finset.mem_filter.1 hn).2⟩ hno

#print axioms univLcm_pos
#print axioms shift_div_eq_linear_multi
#print axioms joint_base_mod
#print axioms inner_sum_multi_forms
#print axioms inner_sum_multi_empty

end CastingOut

end NormalNumbers
