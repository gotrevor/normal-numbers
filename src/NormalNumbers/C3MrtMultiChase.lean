/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiInner

/-!
# The `K`-fold ε-chase

`rung_two_correlation` (`C3MrtArchimedean`, lap 33) is the `K = 2` case: given the rung
*uniformly* over the finitely many admissible pairs below `Y`, the quantifier order
`ε → εr → Y → A → I → N₀` converts it into `‖correlation‖ ≤ C + ε·log N`.

This file does the same at `K` points, on top of `multi_bound_of_rung`.  The chase itself is
**independent of where the rung comes from**: it is stated against a hypothesis
`hrungU` of exactly the shape `rung_two_uniform` delivers, generalised to `K` linear forms.  So
the remaining obligation of the `D ≥ 3` route is precisely `hrungU` — i.e. `KPointLogElliott K`
plus the archimedean certificate — and nothing else.

Budget bookkeeping (`ε` split in two):

* `K^{K²}·truncB z Y K ≤ ε/2` fixes `Y` (`truncB_tendsto`; this is the term that would have
  diverged had the truncation used one congruence instead of the joint modulus);
* `εr·K^{K²}·∏_i sqfWMass z_i ≤ ε/2` fixes the rung's own `ε`;
* `N₀ = Y^K·A^I + Y^K + 2` guarantees `Nat.log A ((N−1−a)/L) ≥ I` for every admissible tuple,
  using `lcm(d) ≤ ∏ d_i ≤ Y^K`;
* `m·log A = log(A^m) ≤ log J ≤ log N` turns the rung's per-window `m·εr·log A` into `εr·log N`.

Everything else is `N`-independent and lands in `C`.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-- The joint modulus of a tuple is at most the product of its entries. -/
theorem univLcm_le_prod {K : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) :
    (Finset.univ : Finset (Fin K)).lcm d ≤ ∏ i : Fin K, d i := by
  refine Nat.le_of_dvd (Finset.prod_pos fun i _ => hd i) ?_
  exact Finset.lcm_dvd fun i _ => Finset.dvd_prod_of_mem d (Finset.mem_univ i)

/-- `lcm(d) ≤ Y^K` for a tuple with all entries `≤ Y`. -/
theorem univLcm_le_pow {K Y : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) (hdY : ∀ i, d i ≤ Y) :
    (Finset.univ : Finset (Fin K)).lcm d ≤ Y ^ K := by
  refine le_trans (univLcm_le_prod d hd) ?_
  calc ∏ i : Fin K, d i ≤ ∏ _i : Fin K, Y := Finset.prod_le_prod' fun i _ => hdY i
    _ = Y ^ K := by simp

open scoped Classical in
/-- **The `K`-fold ε-chase.**  Granting the rung uniformly over the admissible tuples below each
`Y` — the shape `rung_two_uniform` delivers at `K = 2` — the harmonically weighted `K`-point
correlation of `z_i^ω` at the shifts `n+1, …, n+K` is `o(log N)`.

This is the `K`-point `rung_two_correlation`, and (with `multi_bound_of_rung`) it is the whole
`D ≥ 3` assembly: the only hypothesis left is `hrungU`. -/
theorem multi_correlation_of_uniform_rung {K : ℕ} (hK : 0 < K) (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1)
    (hrungU : ∀ εr : ℝ, 0 < εr → ∀ Y : ℕ, ∃ A : ℕ, 2 ≤ A ∧ ∃ I : ℕ,
      ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
        (∃ n₀ : ℕ, ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) →
        ∀ a : ℕ, a < (Finset.univ : Finset (Fin K)).lcm d →
          (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) → ∀ m : ℕ, I ≤ m →
          ‖∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine ((Finset.univ : Finset (Fin K)).lcm d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖
            ≤ (1 + Real.log ((A ^ I : ℕ) : ℝ)) + (m : ℝ) * (εr * Real.log A))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ n ∈ Finset.range N, ((((n : ℝ) + 1)⁻¹ : ℝ)) •
          ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N := by
  classical
  have hKpow : (0 : ℝ) ≤ (K : ℝ) ^ (K * K) := by positivity
  have hMass : (0 : ℝ) ≤ ∏ i : Fin K, sqfWMass (z i) :=
    Finset.prod_nonneg fun i _ => sqfWMass_nonneg (z i)
  set M : ℝ := (K : ℝ) ^ (K * K) * ∏ i : Fin K, sqfWMass (z i) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  -- the rescaled ε for the rung
  obtain ⟨εr, hεr0, hεrM⟩ : ∃ r : ℝ, 0 < r ∧ r * M ≤ ε / 2 := by
    refine ⟨ε / (2 * (M + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hε.le, hM0]
  -- the truncation cutoff `Y`
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, (K : ℝ) ^ (K * K) * truncB z Y K ≤ ε / 2 := by
    have t : Filter.Tendsto (fun Y : ℕ => (K : ℝ) ^ (K * K) * truncB z Y K)
        Filter.atTop (nhds 0) := by
      simpa using (truncB_tendsto z K).const_mul ((K : ℝ) ^ (K * K))
    obtain ⟨Y, hy⟩ := (t.eventually_lt_const (by positivity : (0 : ℝ) < ε / 2)).exists
    exact ⟨Y, hy.le⟩
  obtain ⟨A, hA2, I, hrU⟩ := hrungU εr hεr0 Y
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  have hlogAI : 0 ≤ Real.log ((A ^ I : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  refine ⟨(K : ℝ) * truncA z Y K + ε / 2 + (∏ i : Fin K, sqfWPartial (z i) Y)
      + (3 + (1 + Real.log ((A ^ I : ℕ) : ℝ)) + Real.log A) * M,
    Y ^ K * A ^ I + Y ^ K + 2, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg hNR
  set R : ℝ := (1 + Real.log ((A ^ I : ℕ) : ℝ)) + εr * Real.log N with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  -- the rung bound at the windows the assembly uses
  have hrung : ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
      (∃ n₀ : ℕ, ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) →
      ∀ a : ℕ, a < (Finset.univ : Finset (Fin K)).lcm d →
        (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) →
        ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A
              ((N - 1 - a) / (Finset.univ : Finset (Fin K)).lcm d)),
            (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine ((Finset.univ : Finset (Fin K)).lcm d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖ ≤ R := by
    intro d hdY hdpos hsolv a ha hadvd
    set L : ℕ := (Finset.univ : Finset (Fin K)).lcm d with hLdef
    have hL : 0 < L := univLcm_pos d hdpos
    have hLY : L ≤ Y ^ K := univLcm_le_pow d hdpos hdY
    have haY : a < Y ^ K := lt_of_lt_of_le ha hLY
    set J : ℕ := (N - 1 - a) / L with hJdef
    have hJge : A ^ I ≤ J := by
      rw [hJdef, Nat.le_div_iff_mul_le hL]
      have h1 : A ^ I * L ≤ Y ^ K * A ^ I := by
        rw [mul_comm]; exact Nat.mul_le_mul_right _ hLY
      omega
    have hJpos : 0 < J := lt_of_lt_of_le (Nat.one_le_pow _ _ (by omega)) hJge
    set m : ℕ := Nat.log A J with hmdef
    have hmI : I ≤ m := by
      rw [hmdef]
      calc I = Nat.log A (A ^ I) := (Nat.log_pow (by omega) I).symm
        _ ≤ Nat.log A J := Nat.log_mono_right hJge
    refine le_trans (hrU d hdY hdpos hsolv a ha hadvd m hmI) ?_
    have hAmJ : A ^ m ≤ J := Nat.pow_log_le_self A (by omega)
    have hJN : J ≤ N := le_trans (Nat.div_le_self _ _) (by omega)
    have hcast : ((A : ℝ)) ^ m ≤ (N : ℝ) := by exact_mod_cast le_trans hAmJ hJN
    have hlogpow : (m : ℝ) * Real.log A ≤ Real.log N := by
      have := Real.log_le_log (by positivity) hcast
      rwa [Real.log_pow] at this
    have hfin : (m : ℝ) * (εr * Real.log A) ≤ εr * Real.log N := by
      have h := mul_le_mul_of_nonneg_left hlogpow hεr0.le
      calc (m : ℝ) * (εr * Real.log A) = εr * ((m : ℝ) * Real.log A) := by ring
        _ ≤ εr * Real.log N := h
    rw [hRdef]
    linarith
  have hmain := multi_bound_of_rung hK z hz Y N A hA2 hR0 hrung
  have hgoal : ∑ n ∈ Finset.range N, ((((n : ℝ) + 1)⁻¹ : ℝ)) •
      ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)
      = ∑ n ∈ Finset.range N, harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1) :=
    Finset.sum_congr rfl fun n _ => (harmW_smul n _).symm
  rw [hgoal]
  refine le_trans hmain ?_
  have hTB : 0 ≤ truncB z Y K := truncB_nonneg z Y K
  have h1 : ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K
      ≤ (1 + Real.log N) * (ε / 2) := by
    have := mul_le_mul_of_nonneg_left hY (by linarith : (0 : ℝ) ≤ 1 + Real.log N)
    calc ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K
        = (1 + Real.log N) * ((K : ℝ) ^ (K * K) * truncB z Y K) := by ring
      _ ≤ (1 + Real.log N) * (ε / 2) := this
  have h2 : (3 + R + Real.log A) * M
      ≤ (3 + (1 + Real.log ((A ^ I : ℕ) : ℝ)) + Real.log A) * M + (ε / 2) * Real.log N := by
    have hstep : (3 + R + Real.log A) * M
        = (3 + (1 + Real.log ((A ^ I : ℕ) : ℝ)) + Real.log A) * M
          + (εr * M) * Real.log N := by rw [hRdef]; ring
    have hlast : (εr * M) * Real.log N ≤ (ε / 2) * Real.log N :=
      mul_le_mul_of_nonneg_right hεrM hL0
    linarith
  rw [hM] at h2 ⊢
  linarith

#print axioms univLcm_le_prod
#print axioms multi_correlation_of_uniform_rung

end CastingOut

end NormalNumbers
