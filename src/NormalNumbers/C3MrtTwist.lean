/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtBudget

/-!
# The additive twist costs only a factor `Q`

`depthAvg b P Q j h D N` carries the additive twist `e(jn/Q)` alongside the `D`-point
root-of-unity correlation `∏_{i<D} ζ_i^{ω_{>P}(n+i+1)}`.  The `K`-fold assembly
(`rung_multi_correlation`) bounds the *untwisted* correlation, so the twist has to be disposed of
before the two can meet.

**The observation of this file.**  `e(jn/Q)` is `Q`-periodic in `n`, hence *constant* on each
residue class mod `Q`.  Splitting `range N` into its `Q` classes therefore factors the twist out
completely and costs only the triangle inequality:

    ‖∑_{n<N} e(jn/Q) F n‖ ≤ ∑_{r<Q} ‖∑_{n<N, n ≡ r} F n‖ .

`Q` is FIXED (it is quantified before `N` in `QuantDepthElliott`), so this is an
`N`-independent constant.  Re-indexing each class by `n = Qm + r` turns `ω_{>P}(n+i+1)` into
`ω_{>P}(Qm + (r+i+1))` — the `D` linear forms `Q·X + (r+i+1)`, `i < D`, whose pairwise
determinants are `Q·(i'−i) ≠ 0`.  So **the twisted depth average is a sum of `Q` untwisted
`D`-point correlations along arithmetic progressions**, exactly the objects
`KPointLogElliott D` governs.  No new analytic input is needed for the twist.

This is the first of the three gaps between `rung_multi_correlation` and
`weylLambertTwist_of_kfold_bound`; the other two are log-average → natural-average and the
`Ω` vs `ω_{>P}` bookkeeping.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-- `ee` is invariant under integer shifts. -/
lemma ee_add_intCast (x : ℂ) (k : ℤ) : ee (x + (k : ℂ)) = ee x := by
  rw [ee, ee, mul_add, Complex.exp_add]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from rfl]
  simp [Complex.exp_int_mul_two_pi_mul_I]

/-- **The twist is constant on residue classes.**  If `n ≡ r (mod Q)` then
`e(jn/Q) = e(jr/Q)`. -/
lemma ee_twist_mod {Q : ℕ} (hQ : 0 < Q) (j : ℕ) {n r : ℕ} (hn : n % Q = r) :
    ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) = ee ((((j : ℝ) * r / Q : ℝ) : ℂ)) := by
  set q : ℕ := n / Q with hq
  have hdec : Q * q + r = n := by rw [hq, ← hn]; exact Nat.div_add_mod n Q
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  have hreal : ((j : ℝ) * n / Q : ℝ) = ((j : ℝ) * r / Q : ℝ) + ((j * q : ℕ) : ℝ) := by
    have hnR : ((n : ℝ)) = (Q : ℝ) * (q : ℝ) + (r : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hdec.symm
    rw [hnR]
    push_cast
    field_simp
    ring
  have hcast : (((j : ℝ) * n / Q : ℝ) : ℂ)
      = (((j : ℝ) * r / Q : ℝ) : ℂ) + ((((j * q : ℕ) : ℤ) : ℂ)) := by
    rw [hreal]; push_cast; ring
  rw [hcast, ee_add_intCast]

/-- **The twist splits into `Q` untwisted class sums.**  Purely the triangle inequality after
factoring the (class-constant) twist out of each class. -/
theorem norm_sum_twist_le {Q : ℕ} (hQ : 0 < Q) (j N : ℕ) (F : ℕ → ℂ) :
    ‖∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * F n‖
      ≤ ∑ r ∈ range Q, ‖∑ n ∈ (range N).filter (fun n => n % Q = r), F n‖ := by
  classical
  have hmaps : ∀ n ∈ range N, n % Q ∈ range Q := fun n _ =>
    Finset.mem_range.2 (Nat.mod_lt _ hQ)
  have hsplit : ∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * F n
      = ∑ r ∈ range Q, ee ((((j : ℝ) * r / Q : ℝ) : ℂ)) *
          ∑ n ∈ (range N).filter (fun n => n % Q = r), F n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun n => ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * F n)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ee_twist_mod hQ j (Finset.mem_filter.1 hn).2]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, norm_ee_real, one_mul]

/-- **Each class sum is an untwisted correlation along an arithmetic progression.**
Re-indexing `n = Qm + r`. -/
theorem class_sum_reindex {Q : ℕ} (hQ : 0 < Q) {r : ℕ} (hr : r < Q) (N : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ (range N).filter (fun n => n % Q = r), F n
      = ∑ m ∈ (range N).filter (fun m => Q * m + r < N), F (Q * m + r) := by
  classical
  have hdiv : ∀ m : ℕ, (Q * m + r) / Q = m := by
    intro m
    rw [Nat.mul_add_div hQ, Nat.div_eq_of_lt hr, Nat.add_zero]
  have hmod : ∀ m : ℕ, (Q * m + r) % Q = r := by
    intro m
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hrec : ∀ n : ℕ, n % Q = r → Q * (n / Q) + r = n := by
    intro n hn
    rw [← hn]; exact Nat.div_add_mod n Q
  refine Finset.sum_nbij' (fun n => n / Q) (fun m => Q * m + r) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (Nat.div_le_self n Q) hn.1, by rw [hrec n hn.2]; exact hn.1⟩
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hm.2, hmod m⟩
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact hrec n hn.2
  · intro m _
    exact hdiv m
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [hrec n hn.2]

/-- **The twisted depth average, reduced to `Q` untwisted progression correlations.**
The route-relevant consequence: any bound on the `D`-point correlation of `ζ_i^{ω_{>P}}` along
the progressions `Q·X + (r+i+1)` transfers to `depthAvg` at a cost of the FIXED factor `Q`. -/
theorem norm_depthAvg_le_progressions {Q : ℕ} (hQ : 0 < Q) (b P j : ℕ) (hh : ℤ) (D N : ℕ) :
    ‖depthAvg b P Q j hh D N‖
      ≤ (∑ r ∈ range Q, ‖∑ m ∈ (range N).filter (fun m => Q * m + r < N),
            ∏ i ∈ range D, depthRoot b hh i ^ omegaLarge P (Q * m + r + i + 1)‖) / N := by
  classical
  have hnum : ‖∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
        * ee ((((hh : ℝ) * tailDepth P b D n : ℝ) : ℂ))‖
      ≤ ∑ r ∈ range Q, ‖∑ m ∈ (range N).filter (fun m => Q * m + r < N),
            ∏ i ∈ range D, depthRoot b hh i ^ omegaLarge P (Q * m + r + i + 1)‖ := by
    refine le_trans (norm_sum_twist_le hQ j N
      (fun n => ee ((((hh : ℝ) * tailDepth P b D n : ℝ) : ℂ))))
      (Finset.sum_le_sum fun r hr => ?_)
    rw [class_sum_reindex hQ (Finset.mem_range.1 hr) N]
    refine le_of_eq (congrArg norm (Finset.sum_congr rfl fun m _ => ?_))
    exact ee_tailDepth_eq_prod b P D (Q * m + r) hh
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [depthAvg]
  · rw [depthAvg, norm_div, Complex.norm_natCast]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hnum

#print axioms ee_add_intCast
#print axioms ee_twist_mod
#print axioms norm_sum_twist_le
#print axioms class_sum_reindex
#print axioms norm_depthAvg_le_progressions

end CastingOut

end NormalNumbers
