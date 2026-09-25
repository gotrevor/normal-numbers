/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiLinear

/-!
# The `K`-fold joint harmonic mass, with BOTH gains

This is the `K`-point `joint_progression_harmonic_mass` (`C3MrtTwoShift`, `K = 2`), and it is
the quantitative heart of the `K`-fold truncation.

**The trap it avoids.**  The naive iteration of `offset_truncation_bound_of_mass` bounds the
mass of the joint progression by the mass of ONE of its congruences, `≍ (1+log N)/d_m`.  Summing
the resulting error over the already-truncated moduli then costs
`∏_{j>m} (∑_{d ≤ Y} ‖sqfW z_j d‖) = ∏_{j>m} sqfWPartial z_j Y`, which GROWS with `Y` like
`Y^{(K-m-1)/2}` while `bridgeTail z_m Y` only decays like `Y^{-1/2}`.  For `K − m ≥ 3` the
product diverges and the truncation is worthless.

The fix, exactly as at `K = 2`: use the FULL joint modulus.  The joint progression is one class
mod `L = lcm(d_s)` (`joint_class_range`), so `class_harmonic_mass` bounds its mass by
`(a+1)⁻¹ + (1+log N)/L`; then lap 37's `prod_le_lcm_mul_pow` converts `1/L` into
`K^{K²}/∏_s d_s`.  The `log N`-carrying term therefore comes with the CONVERGENT weight
`∏_j sqfWMass z_j`, not with `sqfWPartial`, and the head `(a+1)⁻¹ ≤ (m+1)/d_0` carries no
`log N` at all — so it contributes only an `N`-independent constant, which the `1/log N`
normalisation kills.

The offset `m` is carried because the telescope peels shifts from the top: at stage `m` the
block of congruences in play is `d_s ∣ n + m + s + 1` for `s < K`, a CONSECUTIVE block, which is
what lets `prod_le_lcm_mul_pow` apply verbatim at the shifted base point `n + m`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **The joint progression is one class, range-indexed.**  The forward half of
`joint_class_multi` in the `range K` / `ℕ → ℕ` convention that `prod_le_lcm_mul_pow` and
`prod_div_lcm_le` use — this is the bridge lap 38 flagged as the indexing debt. -/
theorem joint_class_range {K : ℕ} (d : ℕ → ℕ) {n₀ n : ℕ}
    (h₀ : ∀ i, i < K → d i ∣ n₀ + i + 1) (h : ∀ i, i < K → d i ∣ n + i + 1) :
    n ≡ n₀ [MOD (range K).lcm d] := by
  rw [Nat.modEq_iff_dvd]
  have hdiff : ∀ i, i < K → (d i : ℤ) ∣ (n₀ : ℤ) - (n : ℤ) := by
    intro i hi
    have hz₀ : (d i : ℤ) ∣ (n₀ : ℤ) + (i : ℤ) + 1 := by
      have hc : ((d i : ℕ) : ℤ) ∣ ((n₀ + i + 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (h₀ i hi)
      push_cast at hc
      exact hc
    have hz : (d i : ℤ) ∣ (n : ℤ) + (i : ℤ) + 1 := by
      have hc : ((d i : ℕ) : ℤ) ∣ ((n + i + 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (h i hi)
      push_cast at hc
      exact hc
    have h1 := dvd_sub hz₀ hz
    have heq : ((n₀ : ℤ) + (i : ℤ) + 1) - ((n : ℤ) + (i : ℤ) + 1) = (n₀ : ℤ) - (n : ℤ) := by
      ring
    rwa [heq] at h1
  have hnat : ∀ i, i < K → d i ∣ ((n₀ : ℤ) - (n : ℤ)).natAbs := by
    intro i hi
    have := hdiff i hi
    rwa [Int.natCast_dvd] at this
  have hlcm : (range K).lcm d ∣ ((n₀ : ℤ) - (n : ℤ)).natAbs :=
    Finset.lcm_dvd fun i hi => hnat i (Finset.mem_range.1 hi)
  rwa [Int.natCast_dvd]

/-- **The `K`-fold joint harmonic mass, with both gains.**  A set `S ⊆ range M` on which the
consecutive block of congruences `d_s ∣ n + m + s + 1` (`s < K`) holds has

    ∑_{n ∈ S} ‖F n‖  ≤  (m+1)/d_0  +  (1 + log M)·K^{K²} / ∏_{s<K} d_s .

The first term carries no `log M`; the second carries the full product weight `1/∏ d_s`, which
is what makes the tuple sum absolutely convergent (`tuple_mass_le`). -/
theorem joint_multi_harmonic_mass {F : ℕ → ℂ} (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹)
    {S : Finset ℕ} {M m K : ℕ} (hS : ∀ n ∈ S, n < M) (hK : 0 < K)
    (d : ℕ → ℕ) (hd : ∀ s, s < K → 0 < d s)
    (hmem : ∀ n ∈ S, ∀ s, s < K → d s ∣ n + m + s + 1) :
    ∑ n ∈ S, ‖F n‖
      ≤ ((m : ℝ) + 1) / (d 0 : ℝ)
        + (1 + Real.log M) * (K : ℝ) ^ (K * K) / (∏ s ∈ range K, (d s : ℝ)) := by
  classical
  have hd0 : 0 < d 0 := hd 0 hK
  have hd0R : (0 : ℝ) < (d 0 : ℝ) := by exact_mod_cast hd0
  have hprodpos : (0 : ℝ) < ∏ s ∈ range K, (d s : ℝ) :=
    Finset.prod_pos fun s hs => by
      have := hd s (Finset.mem_range.1 hs); exact_mod_cast this
  rcases Finset.eq_empty_or_nonempty S with rfl | ⟨n₀, hn₀S⟩
  · simp only [Finset.sum_empty]
    have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
    have hKpow : (0 : ℝ) ≤ (K : ℝ) ^ (K * K) := by positivity
    have h1 : (0 : ℝ) ≤ ((m : ℝ) + 1) / (d 0 : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (1 + Real.log M) * (K : ℝ) ^ (K * K) / (∏ s ∈ range K, (d s : ℝ)) := by
      apply div_nonneg _ hprodpos.le
      exact mul_nonneg (by linarith) hKpow
    linarith
  -- `M ≥ 1`, so `log M ≥ 0`
  have hM1 : 1 ≤ M := by have := hS n₀ hn₀S; omega
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
  set L : ℕ := (range K).lcm d with hLdef
  have hL : 0 < L := finsetLcm_pos d hd
  set a : ℕ := n₀ % L with ha
  -- every element of `S` is in the class `a mod L`
  have hcl : ∀ n ∈ S, n % L = a := by
    intro n hnS
    have hmod : (n + m) ≡ (n₀ + m) [MOD L] :=
      joint_class_range d (fun i hi => by
          have := hmem n₀ hn₀S i hi
          simpa [Nat.add_right_comm, Nat.add_assoc] using this)
        (fun i hi => by
          have := hmem n hnS i hi
          simpa [Nat.add_right_comm, Nat.add_assoc] using this)
    have hcancel : n ≡ n₀ [MOD L] := Nat.ModEq.add_right_cancel' m hmod
    rw [ha]
    exact hcancel
  have hmass := class_harmonic_mass hF hS hL hcl
  -- the head: `d 0 ∣ a + m + 1`
  have hdvd0 : d 0 ∣ a + m + 1 := by
    have hdL : d 0 ∣ L := Finset.dvd_lcm (Finset.mem_range.2 hK)
    have hmodL : a ≡ n₀ [MOD L] := by rw [ha]; exact Nat.mod_modEq _ _
    have hmod0 : a ≡ n₀ [MOD d 0] := hmodL.of_dvd hdL
    have hshift : a + m + 1 ≡ n₀ + m + 1 [MOD d 0] := (hmod0.add_right _).add_right 1
    have hz : n₀ + m + 1 ≡ 0 [MOD d 0] := by
      refine (Nat.modEq_zero_iff_dvd).2 ?_
      have := hmem n₀ hn₀S 0 hK
      simpa using this
    exact (Nat.modEq_zero_iff_dvd).1 (hshift.trans hz)
  have hd0le : (d 0 : ℝ) ≤ (a : ℝ) + (m : ℝ) + 1 := by
    have : d 0 ≤ a + m + 1 := Nat.le_of_dvd (by omega) hdvd0
    exact_mod_cast this
  have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hhead : ((a : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1) / (d 0 : ℝ) := by
    have hstep1 : ((a : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1) / ((a : ℝ) + (m : ℝ) + 1) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hstep2 : ((m : ℝ) + 1) / ((a : ℝ) + (m : ℝ) + 1) ≤ ((m : ℝ) + 1) / (d 0 : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hd0R hd0le
    linarith
  -- the main term: `1/L ≤ K^{K²}/∏ d_s`
  have hprod := prod_le_lcm_mul_pow (K := K) d hd (n := n₀ + m)
    (fun i hi => by
      have := hmem n₀ hn₀S i hi
      simpa [Nat.add_right_comm, Nat.add_assoc] using this)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hprodR : (∏ s ∈ range K, (d s : ℝ)) ≤ (L : ℝ) * (K : ℝ) ^ (K * K) := by
    have hcast : ((∏ s ∈ range K, d s : ℕ) : ℝ) = ∏ s ∈ range K, (d s : ℝ) := by push_cast; rfl
    have h := hprod
    have hR : ((∏ s ∈ range K, d s : ℕ) : ℝ) ≤ (((range K).lcm d * K ^ (K * K) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hcast] at hR
    push_cast at hR
    exact hR
  have hmain : (1 + Real.log M) / (L : ℝ)
      ≤ (1 + Real.log M) * (K : ℝ) ^ (K * K) / (∏ s ∈ range K, (d s : ℝ)) := by
    rw [div_le_div_iff₀ hLR hprodpos]
    have h1 : (0 : ℝ) ≤ 1 + Real.log M := by linarith
    nlinarith [hprodR, h1, hLR.le]
  linarith [hmass, hhead, hmain]

#print axioms joint_class_range
#print axioms joint_multi_harmonic_mass

end CastingOut

end NormalNumbers
