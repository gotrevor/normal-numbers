/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtJointModulus

/-!
# The tuple mass: the `K`-fold `pair_mass_le`

`pair_mass_le` (`C3MrtTwoShift`) is the inequality the whole two-shift assembly rests on:
`∑_{d,e ≤ Y} ‖g_0(d)‖‖g_1(e)‖/(de) ≤ sqfWMass z_0 · sqfWMass z_1 < ∞`, independently of `Y`.
This file supplies its `K`-fold analogue, in two pieces:

* `tuple_mass_le` — with the *product* weight `1/∏ d_i`, the tuple sum factors completely
  (`Finset.sum_prod_piFinset`) and is bounded by `∏_i sqfWMass z_i`, uniformly in `Y`.
* `prod_div_lcm_le` — the pointwise conversion from the *joint modulus* `lcm(d_i)`, which is what
  the `K`-fold CRT actually produces, to the product weight, at the cost of the `K^{K²}` of
  `prod_le_lcm_mul_pow` (lap 37).

Composing them gives `∑_{(d_i) ≤ Y} (∏_i‖g_i(d_i)‖)/lcm(d_i) ≤ K^{K²} ∏_i sqfWMass z_i` over any
set of tuples that are positive and jointly solvable — the tuples that actually contribute.

### Indexing note

`tuple_mass_le` is stated over `Fin K` (forced by `Fintype.piFinset`, which is how lap 36's
`sum_pow_omega_multi_eq` indexes its tuple sum); `prod_div_lcm_le` is stated over `range K` with
`ℕ → ℕ` tuples (forced by lap 37's `prod_le_lcm_mul_pow`).  The assembly lap that composes them
must fix one convention; `Fin.prod_univ_eq_prod_range` is the bridge for the products, and the
`lcm` should then be taken as `Finset.lcm (range K)` of the `ℕ → ℕ` extension.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **The tuple mass is bounded independently of `Y`.**  The `K`-fold `pair_mass_le`: with the
product weight the tuple sum factors into `K` one-dimensional sums, each `≤ sqfWMass z_i`. -/
theorem tuple_mass_le {K : ℕ} (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (Y : ℕ) :
    ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
        ∏ i : Fin K, ‖sqfW (z i) (d i)‖ / ((d i : ℝ))
      ≤ ∏ i : Fin K, sqfWMass (z i) := by
  classical
  rw [Finset.sum_prod_piFinset (range (Y + 1))
    (fun (i : Fin K) (j : ℕ) => ‖sqfW (z i) j‖ / (j : ℝ))]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · exact Finset.sum_nonneg fun j _ => by positivity
  · exact sum_norm_sqfW_div_le_mass (hz i) Y

/-- Positivity of the joint modulus. -/
theorem finsetLcm_pos {K : ℕ} (d : ℕ → ℕ) (hd : ∀ i, i < K → 0 < d i) :
    0 < (range K).lcm d := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [Finset.lcm_eq_zero_iff] at h0
    obtain ⟨i, hi, hzero⟩ := h0
    have hiK : i < K := by simpa using hi
    exact absurd hzero (hd i hiK).ne'

/-- **From the joint modulus to the product weight.**  For any nonnegative weights `w` and any
tuple whose joint progression is nonempty,

    (∏_{i<K} w_i) / lcm(d_i)  ≤  K^{K²} · ∏_{i<K} (w_i / d_i) .

This is the pointwise form of the `1/lcm → 1/∏ d_i` exchange; the `K^{K²}` is exactly
`prod_le_lcm_mul_pow`'s, and it is `K`-dependent only. -/
theorem prod_div_lcm_le {K : ℕ} (w : ℕ → ℝ) (hw : ∀ i, i < K → 0 ≤ w i) (d : ℕ → ℕ)
    (hd : ∀ i, i < K → 0 < d i) {n : ℕ} (hn : ∀ i, i < K → d i ∣ n + i + 1) :
    (∏ i ∈ range K, w i) / (((range K).lcm d : ℕ) : ℝ)
      ≤ ((K : ℝ) ^ (K * K)) * ∏ i ∈ range K, (w i / (d i : ℝ)) := by
  have hL : 0 < (((range K).lcm d : ℕ) : ℝ) := by
    exact_mod_cast finsetLcm_pos d hd
  have hDpos : 0 < ((∏ i ∈ range K, d i : ℕ) : ℝ) := by
    have : 0 < ∏ i ∈ range K, d i :=
      Finset.prod_pos fun i hi => hd i (Finset.mem_range.1 hi)
    exact_mod_cast this
  have hP0 : 0 ≤ ∏ i ∈ range K, w i :=
    Finset.prod_nonneg fun i hi => hw i (Finset.mem_range.1 hi)
  have hsplit : (∏ i ∈ range K, (w i / (d i : ℝ)))
      = (∏ i ∈ range K, w i) / ((∏ i ∈ range K, d i : ℕ) : ℝ) := by
    rw [Finset.prod_div_distrib]
    congr 1
    push_cast
    rfl
  have hDle : ((∏ i ∈ range K, d i : ℕ) : ℝ)
      ≤ ((K : ℝ) ^ (K * K)) * (((range K).lcm d : ℕ) : ℝ) := by
    have h := prod_le_lcm_mul_pow d hd hn
    have : ((∏ i ∈ range K, d i : ℕ) : ℝ)
        ≤ (((range K).lcm d * K ^ (K * K) : ℕ) : ℝ) := by exact_mod_cast h
    calc ((∏ i ∈ range K, d i : ℕ) : ℝ)
        ≤ (((range K).lcm d * K ^ (K * K) : ℕ) : ℝ) := this
      _ = ((K : ℝ) ^ (K * K)) * (((range K).lcm d : ℕ) : ℝ) := by push_cast; ring
  rw [hsplit, mul_div_assoc', div_le_div_iff₀ hL hDpos]
  nlinarith [hP0, hDle, hL.le, hDpos.le]

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.tuple_mass_le
#print axioms NormalNumbers.CastingOut.finsetLcm_pos
#print axioms NormalNumbers.CastingOut.prod_div_lcm_le
