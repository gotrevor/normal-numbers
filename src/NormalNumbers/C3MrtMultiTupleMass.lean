/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiTrunc

/-!
# The `K`-fold tuple mass in ONE convention — lap 38's indexing debt, paid

`tuple_mass_le` is stated over `Fin K` (forced by `Fintype.piFinset`, which is how
`sum_pow_omega_multi_eq` indexes its tuple sum); `prod_div_lcm_le` is stated over `range K` with
`ℕ → ℕ` tuples (forced by lap 37's `prod_le_lcm_mul_pow`).  This file fixes the `Fin K`
convention, transports the `range K` results across the extension `extendFin`, and composes them
into the single inequality the per-tuple assembly needs:

    ∑_{d : Fin K → ℕ, all d_i ≤ Y, positive, jointly solvable}
        (∏_i ‖sqfW z_i (d_i)‖) / lcm(d_i)   ≤   K^{K²} · ∏_i sqfWMass z_i ,

**uniformly in `Y` and in `N`**.  The left side is exactly the total weight the `K`-fold bridge
expansion puts on the `1/L`-sized inner sums (`inner_sum_multi_forms` produces `≍ N/L` terms),
so this is the `K`-point `pair_mass_le` — the inequality the whole assembly rests on.  The
`K^{K²}` is lap 37's, and `C3MrtBudget.kfold_budget_le_exp_cube` is what pays for it.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- The `ℕ → ℕ` extension of a `Fin K`-indexed tuple, by `1` outside the range (`1` is the
`lcm`-neutral value, so it changes neither the joint modulus nor the product). -/
def extendFin {K : ℕ} (d : Fin K → ℕ) : ℕ → ℕ := fun i => if h : i < K then d ⟨i, h⟩ else 1

lemma extendFin_apply {K : ℕ} (d : Fin K → ℕ) (i : Fin K) : extendFin d (i : ℕ) = d i := by
  rw [extendFin]
  simp only [i.isLt, dif_pos]

lemma extendFin_pos {K : ℕ} {d : Fin K → ℕ} (hd : ∀ i, 0 < d i) :
    ∀ i, i < K → 0 < extendFin d i := by
  intro i hi
  rw [extendFin]
  simp only [hi, dif_pos]
  exact hd _

/-- The two joint moduli agree. -/
theorem range_lcm_extendFin {K : ℕ} (d : Fin K → ℕ) :
    (range K).lcm (extendFin d) = (Finset.univ : Finset (Fin K)).lcm d := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine Finset.lcm_dvd fun i hi => ?_
    have hiK : i < K := Finset.mem_range.1 hi
    have : extendFin d i = d ⟨i, hiK⟩ := by rw [extendFin]; simp only [hiK, dif_pos]
    rw [this]
    exact Finset.dvd_lcm (Finset.mem_univ _)
  · refine Finset.lcm_dvd fun i _ => ?_
    have := Finset.dvd_lcm (f := extendFin d) (Finset.mem_range.2 i.isLt)
    rwa [extendFin_apply] at this

/-- The `Fin K` form of `prod_div_lcm_le`. -/
theorem prod_div_univLcm_le {K : ℕ} (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i) (d : Fin K → ℕ)
    (hd : ∀ i, 0 < d i) {n : ℕ} (hn : ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) :
    (∏ i : Fin K, w i) / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ)
      ≤ ((K : ℝ) ^ (K * K)) * ∏ i : Fin K, (w i / (d i : ℝ)) := by
  classical
  set w' : ℕ → ℝ := fun i => if h : i < K then w ⟨i, h⟩ else 1 with hw'
  have hw'apply : ∀ i : Fin K, w' (i : ℕ) = w i := by
    intro i; rw [hw']; simp only [i.isLt, dif_pos]
  have hprodw : ∏ i ∈ range K, w' i = ∏ i : Fin K, w i := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => w' i) K]
    exact Finset.prod_congr rfl fun i _ => hw'apply i
  have hprodd : ∏ i ∈ range K, (w' i / (extendFin d i : ℝ)) = ∏ i : Fin K, (w i / (d i : ℝ)) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => w' i / (extendFin d i : ℝ)) K]
    exact Finset.prod_congr rfl fun i _ => by rw [hw'apply i, extendFin_apply]
  have h := prod_div_lcm_le (K := K) w'
    (fun i hi => by rw [hw']; simp only [hi, dif_pos]; exact hw _)
    (extendFin d) (extendFin_pos hd) (n := n)
    (fun i hi => by
      have := hn ⟨i, hi⟩
      have he : extendFin d i = d ⟨i, hi⟩ := by rw [extendFin]; simp only [hi, dif_pos]
      rw [he]
      simpa using this)
  rw [hprodw, hprodd, range_lcm_extendFin] at h
  exact h

open scoped Classical in
/-- **The `K`-point `pair_mass_le`.**  The total weight the bridge expansion puts on the
`1/lcm`-sized inner sums is bounded by `K^{K²}·∏_i sqfWMass z_i`, uniformly in `Y` (and with no
`N` anywhere).  The sum runs over the tuples that actually contribute: positive entries and a
nonempty joint progression. -/
theorem kfold_lcm_mass_le {K : ℕ} (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (Y : ℕ)
    (sol : (Fin K → ℕ) → Prop)
    (hsol : ∀ d, sol d → (∀ i, 0 < d i) ∧ ∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) :
    ∑ d ∈ (Fintype.piFinset (fun _ : Fin K => range (Y + 1))).filter sol,
        (∏ i : Fin K, ‖sqfW (z i) (d i)‖) / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ)
      ≤ ((K : ℝ) ^ (K * K)) * ∏ i : Fin K, sqfWMass (z i) := by
  classical
  have hKpow : (0 : ℝ) ≤ (K : ℝ) ^ (K * K) := by positivity
  calc ∑ d ∈ (Fintype.piFinset (fun _ : Fin K => range (Y + 1))).filter sol,
        (∏ i : Fin K, ‖sqfW (z i) (d i)‖) / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ)
      ≤ ∑ d ∈ (Fintype.piFinset (fun _ : Fin K => range (Y + 1))).filter sol,
          ((K : ℝ) ^ (K * K)) * ∏ i : Fin K, (‖sqfW (z i) (d i)‖ / (d i : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hpos, n, hn⟩ := hsol d (Finset.mem_filter.1 hd).2
        exact prod_div_univLcm_le (fun i => ‖sqfW (z i) (d i)‖) (fun i => norm_nonneg _) d hpos hn
    _ ≤ ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
          ((K : ℝ) ^ (K * K)) * ∏ i : Fin K, (‖sqfW (z i) (d i)‖ / (d i : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro d _ _
        refine mul_nonneg hKpow (Finset.prod_nonneg fun i _ => ?_)
        positivity
    _ = ((K : ℝ) ^ (K * K)) * ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
          ∏ i : Fin K, (‖sqfW (z i) (d i)‖ / (d i : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((K : ℝ) ^ (K * K)) * ∏ i : Fin K, sqfWMass (z i) :=
        mul_le_mul_of_nonneg_left (tuple_mass_le z hz Y) hKpow

#print axioms range_lcm_extendFin
#print axioms prod_div_univLcm_le
#print axioms kfold_lcm_mass_le


open scoped Classical in
/-- **The `K`-fold `full_sum_bound`.**  If every contributing tuple `d` (positive entries, joint
progression nonempty) satisfies the shape `progression_sum_bound` produces,
`‖Inner d‖ ≤ 1 + R/lcm(d)`, and the non-contributing tuples give `Inner d = 0`, then the whole
weighted tuple sum is at most

    ∏_i sqfWPartial z_i Y  +  R · K^{K²} · ∏_i sqfWMass z_i .

The first summand is `N`-independent (it grows with `Y`, harmlessly — it is killed by the
`1/log N` normalisation); the second is where the `ε·log N` inside `R` meets a FINITE constant
instead of the divergent `∑_d ∏_i ‖sqfW z_i (d_i)‖`.  This is the `K`-point `full_sum_bound`,
and `kfold_lcm_mass_le` is what makes it true. -/
theorem multi_full_sum_bound {K : ℕ} (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (Y : ℕ)
    (Inner : (Fin K → ℕ) → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (sol : (Fin K → ℕ) → Prop)
    (hsol : ∀ d, sol d → (∀ i, 0 < d i) ∧ ∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1)
    (hzero : ∀ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)), ¬ sol d → Inner d = 0)
    (hbound : ∀ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)), sol d →
      ‖Inner d‖ ≤ 1 + R / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ)) :
    ‖∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
        (∏ i : Fin K, sqfW (z i) (d i)) * Inner d‖
      ≤ (∏ i : Fin K, sqfWPartial (z i) Y)
        + R * ((K : ℝ) ^ (K * K) * ∏ i : Fin K, sqfWMass (z i)) := by
  classical
  set P := Fintype.piFinset (fun _ : Fin K => range (Y + 1)) with hP
  have hterm : ∀ d ∈ P, ‖(∏ i : Fin K, sqfW (z i) (d i)) * Inner d‖
      ≤ (if sol d then (∏ i : Fin K, ‖sqfW (z i) (d i)‖)
            + R * ((∏ i : Fin K, ‖sqfW (z i) (d i)‖) /
              (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ)) else 0) := by
    intro d hd
    by_cases h : sol d
    · simp only [h, if_true]
      rw [norm_mul, norm_prod]
      have hw : (0 : ℝ) ≤ ∏ i : Fin K, ‖sqfW (z i) (d i)‖ :=
        Finset.prod_nonneg fun i _ => norm_nonneg _
      calc (∏ i : Fin K, ‖sqfW (z i) (d i)‖) * ‖Inner d‖
          ≤ (∏ i : Fin K, ‖sqfW (z i) (d i)‖) *
              (1 + R / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hbound d hd h) hw
        _ = _ := by ring
    · simp only [h, if_false, hzero d hd h, mul_zero, norm_zero]
      exact le_refl 0
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
  rw [← Finset.sum_filter, Finset.sum_add_distrib]
  have h1 : ∑ d ∈ P.filter sol, (∏ i : Fin K, ‖sqfW (z i) (d i)‖)
      ≤ ∏ i : Fin K, sqfWPartial (z i) Y := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => Finset.prod_nonneg fun i _ => norm_nonneg _)) ?_
    rw [hP, Finset.sum_prod_piFinset (range (Y + 1))
      (fun (i : Fin K) (j : ℕ) => ‖sqfW (z i) j‖)]
    exact le_of_eq rfl
  have h2 : ∑ d ∈ P.filter sol, R * ((∏ i : Fin K, ‖sqfW (z i) (d i)‖) /
        (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ))
      ≤ R * ((K : ℝ) ^ (K * K) * ∏ i : Fin K, sqfWMass (z i)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (kfold_lcm_mass_le z hz Y sol hsol) hR
  linarith

#print axioms multi_full_sum_bound

end CastingOut

end NormalNumbers
