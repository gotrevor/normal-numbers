/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtShape
import NormalNumbers.DelangeSlot

/-!
# Rung 1 of `DepthElliott`: the one-point twisted correlation, PROVED

`C3MrtShape` reduced the C3 crux to `DepthElliott b`: a twisted `D`-point correlation of the
multiplicative functions `ζ_i^{ω_{>P}}`, `ζ_i = e(h/b^{i+1})`, along a depth schedule
`D_N = O(log log N)`.  Its **`D = 1`** case is exactly the Leaf-B Delange slot already proved in
this repo (`DelangeSlot.twisted_omegaLarge_mean_tendsto_zero`, axiom-clean):

    (1/N) ∑_{m≤N} e(jm/Q) · z^{ω_{>P}(m)} → 0     for `‖z‖ = 1`, `z ≠ 1`.

This file wires that in, giving `depthAvg_one_tendsto`: the base rung of `DepthElliott` holds,
in **natural** density, with no MRT and no log-averaging.  So the difficulty of `DepthElliott` is
entirely the *multi-point* structure, not the twist and not the non-pretentiousness input.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- The two `ω_{>P}` definitions in the repo agree. -/
lemma omegaLarge_eq_delange (P m : ℕ) : omegaLarge P m = DelangeSlot.omegaLarge P m := by
  rw [omegaLarge, DelangeSlot.omegaLarge]
  exact congrArg Finset.card (Finset.filter_congr fun p _ => by simp [not_le])

lemma norm_depthRoot (b : ℕ) (h : ℤ) (i : ℕ) : ‖depthRoot b h i‖ = 1 := by
  rw [depthRoot]; exact norm_ee_real _

lemma tailDepth_one (P b n : ℕ) :
    tailDepth P b 1 n = (omegaLarge P (n + 1) : ℝ) / (b : ℝ) ^ 1 := by
  simp [tailDepth]

/-- Reindex `range N` to `Icc 1 N` by `n ↦ n + 1`. -/
lemma sum_range_shift_eq_sum_Icc {M : Type*} [AddCommMonoid M] (F : ℕ → M) (N : ℕ) :
    ∑ n ∈ range N, F (n + 1) = ∑ m ∈ Icc 1 N, F m := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- **Rung 1 of `DepthElliott`, proved.**  The one-point twisted correlation
`(1/N) ∑_{n<N} e(jn/Q) ζ_0^{ω_{>P}(n+1)}` tends to `0` whenever `ζ_0 = e(h/b) ≠ 1`. -/
theorem depthAvg_one_tendsto (b P Q j : ℕ) (h : ℤ) (hQ : 0 < Q)
    (hζ : depthRoot b h 0 ≠ 1) :
    Tendsto (fun N : ℕ => depthAvg b P Q j h 1 N) atTop (𝓝 0) := by
  set z : ℂ := depthRoot b h 0 with hzdef
  -- the summand, in one-point form
  have hsummand : ∀ n : ℕ,
      ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * ee ((((h : ℝ) * tailDepth P b 1 n : ℝ) : ℂ))
        = ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * z ^ omegaLarge P (n + 1) := by
    intro n
    rw [ee_tailDepth_eq_prod]
    simp [hzdef]
  -- the Delange form
  set F : ℕ → ℂ := fun m => Complex.exp (2 * Real.pi * Complex.I * (j : ℤ) * m / Q)
    * z ^ DelangeSlot.omegaLarge P m with hF
  set c : ℂ := ee (((-(j : ℝ) / Q : ℝ) : ℂ)) with hc
  have hstep : ∀ n : ℕ,
      ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * z ^ omegaLarge P (n + 1) = c * F (n + 1) := by
    intro n
    simp only [hF, hc, omegaLarge_eq_delange]
    have hQ0 : (Q : ℂ) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : Q ≠ 0)
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (j : ℤ) * ((n : ℕ) + 1 : ℕ) / Q)
        = ee ((((j : ℝ) * (n + 1) / Q : ℝ) : ℂ)) := by
      rw [ee]
      congr 1
      push_cast
      field_simp
    rw [hexp, ee, ee, ee, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have hdel := DelangeSlot.twisted_omegaLarge_mean_tendsto_zero P Q hQ (j : ℤ) z
    (norm_depthRoot b h 0) hζ
  have hdel' : Tendsto (fun N : ℕ => (∑ m ∈ Icc 1 N, F m) / (N : ℂ)) atTop (𝓝 0) := by
    simpa [hF] using hdel
  have := hdel'.const_mul c
  rw [mul_zero] at this
  refine this.congr fun N => ?_
  rw [depthAvg, mul_div_assoc']
  congr 1
  rw [Finset.mul_sum, ← sum_range_shift_eq_sum_Icc]
  exact Finset.sum_congr rfl fun n _ => by rw [hsummand n, hstep n]

end CastingOut

end NormalNumbers
