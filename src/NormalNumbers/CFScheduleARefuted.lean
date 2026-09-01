/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFScheduleA

/-!
# The refuted node `VarianceBlockCountPsiPushed`, kernel-checked 🚫

`VarianceBlockCountPsiPushed` (`CFScheduleA.lean`) is the second-moment brick the
abandoned single-stream B6 schedule route rested on: for every genuine base cylinder
`wx'`, pattern `v`, scale `n` and affine `ψ = affineMap q r`,

  `∫_{cfCylinder wx'} (blockCount (cfCylinder v) n (ψ x) − n·γv)² dγ ≤ (8|v|+80)·n·γv·γ(cfCylinder wx')`.

`OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md` refuted it on paper with a deep
cylinder whose ψ-image is trapped in `[2,…,2]`.  This module lands the **signpost
theorem** for that refutation (KB rule: a refuted route gets a proved negation of the
exact refuted shape), and sharpens it: the affine map is irrelevant.  Already at
`q = 1, r = 0` (`ψ = id`) the statement fails — take `v = [1]`, `wx' = [2,…,2]` (`m`
twos) and `n = m`: on `cfCylinder wx'` the first `m` digits are all `2`, so
`blockCount (cfCylinder [1]) m ≡ 0` there, the integrand is the constant `(m·γv)²`, and
`m²γv²·γ(wx') > 88·m·γv·γ(wx')` as soon as `m·γv > 88`.  With `γv = γ(cfCylinder [1]) =
log₂(4/3) ≥ 1/4` (`gaussMeasure_digit_cylinder`), `m = 1000` does it.

What the refutation SAYS about the mathematics: the second moment of a block count
*restricted to a cylinder* but centred at the *global* mean `n·γv` is `Θ(n²)·γ(wx')`
whenever the cylinder pins the first `n` digits — the conditional mean on a deep cylinder
is nowhere near `n·γv`, and no base-mass factor rescues a quadratic-in-`n` second moment.
Any Chebyshev on a restricted measure must centre at the *conditional* mean (which the
route could not control), which is exactly why the route died and B6 went through the
measure route (`CFAeNormal.lean`).

`varianceBlockCountPsiPushed_false` is sorry-free; `#print axioms` = the trust triple.
-/

namespace NormalNumbers

open MeasureTheory

/-- **`VarianceBlockCountPsiPushed` is FALSE** (kernel-checked signpost for the refuted
node).  Witness: `q = 1, r = 0, wx' = List.replicate m 2, v = [1], n = m` with `m = 1000`.
On `cfCylinder (replicate m 2)` every point has its first `m` CF digits equal to `2`, so
`gaussMap^[k] x ∉ cfCylinder [1]` for `k < m` and `blockCount (cfCylinder [1]) m x = 0`;
the integrand is then the constant `(m·γv)²`, the integral is `γ(wx')·(m·γv)²`, and with
`γv = log₂(4/3) ≥ 1/4` this exceeds `88·m·γv·γ(wx')` because `m·γv ≥ 250 > 88`.

Note the affine map plays no role: the statement is false for the identity map, so the
obstruction is intrinsic to "restricted measure, global centring", not to the ψ-pushforward. -/
theorem varianceBlockCountPsiPushed_false : ¬ VarianceBlockCountPsiPushed := by
  intro H
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℝ) = 1000 := ⟨1000, by norm_num⟩
  have hne : List.replicate m 2 ≠ [] := by
    rw [Ne, List.replicate_eq_nil_iff]
    intro h; rw [h] at hm; norm_num at hm
  have hpos : ∀ c ∈ List.replicate m 2, 1 ≤ c := by
    intro c hc; rw [List.mem_replicate] at hc; omega
  have hv : ∀ a ∈ [1], 1 ≤ a := by simp
  have key := H one_pos 0 (List.replicate m 2) hne hpos [1] hv m
  set γv := (gaussMeasure (cfCylinder [1])).toReal with hγv
  set γS := (gaussMeasure (cfCylinder (List.replicate m 2))).toReal with hγS
  -- on the cylinder `[2,…,2]` the pattern `[1]` never occurs among the first `m` digits
  have hblock : ∀ x ∈ cfCylinder (List.replicate m 2),
      blockCount (cfCylinder [1]) m (affineMap 1 0 x) = 0 := by
    intro x hx
    have hx' : affineMap 1 0 x = x := by simp
    rw [hx', blockCount_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hnot : gaussMap^[k] x ∉ cfCylinder [1] := by
      intro hmem
      have hd := hmem.2 0 (by simp)
      have hd' := hx.2 k (by simpa using hk)
      simp only [cfDigit, Function.iterate_zero, id_eq] at hd
      simp only [cfDigit] at hd'
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate] at hd'
      simp [hk] at hd'
      simp at hd
      omega
    simp [blockIndic, Set.indicator_of_notMem hnot]
  -- the integrand is the constant `(m·γv)²` on the base cylinder
  have hLHS : ∫ x in cfCylinder (List.replicate m 2),
      (blockCount (cfCylinder [1]) m (affineMap 1 0 x) - m * γv) ^ 2 ∂gaussMeasure
      = γS * ((m : ℝ) * γv) ^ 2 := by
    rw [setIntegral_congr_fun (measurableSet_cfCylinder _)
      (g := fun _ => ((m : ℝ) * γv) ^ 2) (fun x hx => by
        show _ = ((m : ℝ) * γv) ^ 2
        rw [hblock x hx]; ring)]
    rw [setIntegral_const, smul_eq_mul, measureReal_def]
  have hγS0 : 0 < γS := gaussMeasure_cfCylinder_toReal_pos _ hne hpos
  -- `γ(cfCylinder [1]) = log₂(4/3) ≥ 1/4`
  have hγv14 : (1 : ℝ) / 4 ≤ γv := by
    rw [hγv, gaussMeasure_digit_cylinder 1 le_rfl]
    have h43 : (1 : ℝ) + 1 / (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 2)) = 4 / 3 := by norm_num
    rw [h43]
    have hlogb0 : 0 ≤ Real.logb 2 (4 / 3) := Real.logb_nonneg one_lt_two (by norm_num)
    rw [ENNReal.toReal_ofReal hlogb0]
    rw [Real.logb]
    have h1 : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
      norm_num at this ⊢; linarith
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have h3 : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [le_div_iff₀ h3]; nlinarith
  rw [hLHS] at key
  simp only [List.length_singleton, Nat.cast_one] at key
  rw [hm] at key
  nlinarith [hγS0, hγv14, mul_pos hγS0 (by linarith : (0:ℝ) < γv)]

end NormalNumbers
