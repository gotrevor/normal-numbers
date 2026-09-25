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

end CastingOut

end NormalNumbers
