import NormalNumbers.ElliottSquarefullConv

/-!
# The Rankin shift: a UNIFORMLY small squarefull tail

This file supplies `NormalNumbers.ElliottLeafTwo.exists_squarefull_tail`, the obligation found
while assembling leaf 2 (lap 60).

`ElliottSquarefullConv.sum_norm_squarefullPart_div_le_exp_two` bounds the **total**
`∑_{d ≤ Y} ‖u d‖/d ≤ e²`.  Case B needs more: the `(d₁,d₂)`-sum must be truncated at a `D` fixed
*before* the function, because `AffineCMLogElliott` hands out its threshold per affine pair and the
substituted dilations `a₁d₂, a₂d₁` grow with `d`.  A uniformly bounded total does **not** give
uniformly small tails — that is precisely the inference that killed the `v`-expansion at lap 54.

Here it is nevertheless true, by a **Rankin shift**: for `d > D`,

`1/d = d^{-3/4} · d^{-1/4} ≤ D^{-1/4} · d^{-3/4}`,

and the shifted sum `∑_d ‖u d‖ / d^{3/4}` is still absolutely bounded, because the shifted local
factor is `1 + 2 ∑_{k ≥ 2} p^{-3k/4} ≤ 1 + 5 p^{-3/2}` and `∑_p p^{-3/2}` converges — the exponent
being `2 · (3/4) = 3/2 > 1`.

**The shift must be strictly below `1/2`.**  At `δ = 1/2` the local factor would be
`1 + 2/(√p(√p−1))` and `∑_p 1/(√p(√p−1)) ≍ ∑_p 1/p` diverges.  `δ = 1/4` is a safe choice.

## Main results

* `local_factor_geom_le` — the local factor at an arbitrary geometric ratio `r`; lap 56's
  `ElliottSquarefull.local_factor_squarefull_le` is the case `r = 1/p`.
* `sum_Icc_inv_mul_sqrt_le` — `∑_{2 ≤ n ≤ Y} 1/(n√n) ≤ 2`, by telescoping `2/√(n−1) − 2/√n`.
* `sum_primesBelow_rpow_le` — `∑_{p ≤ Y} p^{-3/2} ≤ 2`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottRankin

open ArithmeticFunction NormalNumbers.ElliottEulerBound NormalNumbers.ElliottSquarefull

/-! ## The local factor at an arbitrary ratio -/

/-- **The local factor at ratio `r`.**  For `f` nonnegative multiplicative with `f p = 0` and
`f (p^k) ≤ 2 r^k`, the truncated local Euler factor is at most `1 + 2 r²/(1−r)`.

Lap 56's `ElliottSquarefull.local_factor_squarefull_le` is the case `r = 1/p`; the point of the
generalisation is the Rankin ratio `r = p^{-3/4}`. -/
theorem local_factor_geom_le {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {p : ℕ} (hp : p.Prime) (hprime : f p = 0) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbd : ∀ k : ℕ, f (p ^ k) ≤ 2 * r ^ k) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), f (p ^ k) ≤ 1 + 2 * (r ^ 2 / (1 - r)) := by
  classical
  have htailnn : (0 : ℝ) ≤ r ^ 2 / (1 - r) := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  rcases Nat.lt_or_ge K 2 with hK | hK
  · interval_cases K
    · rw [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, hf.map_one]
      linarith
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, pow_one, hf.map_one, hprime]
      linarith
  · have hsplit : ∑ k ∈ Finset.range (K + 1), f (p ^ k) =
        f 1 + f p + ∑ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) := by
      have h1 : Finset.range (K + 1) = Finset.range 2 ∪ Finset.Ico 2 (K + 1) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico] <;> omega
      rw [h1, Finset.sum_union (by
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive 0 2 (K + 1))]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp
    have htailbd : ∑ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) ≤ 2 * (r ^ 2 / (1 - r)) := by
      refine (Finset.sum_le_sum (fun k _ => hbd k)).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (geom_sum_Ico_two_le hr0 hr1 K) (by norm_num)
    rw [hsplit, hf.map_one, hprime]
    linarith

/-! ## The convergent prime sum at exponent `3/2` -/

/-- The telescoping step: `1/(n√n) ≤ 2/√(n−1) − 2/√n`.

With `s = √(n−1)`, `t = √n` this is `s t (t+s) ≤ 2 t³`, which follows from `s ≤ t` alone. -/
theorem inv_mul_sqrt_le_telescope {m : ℕ} (hm : 1 ≤ m) :
    1 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤
      2 / Real.sqrt (m : ℝ) - 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hc]
  set s : ℝ := Real.sqrt (m : ℝ) with hs
  set t : ℝ := Real.sqrt ((m : ℝ) + 1) with ht
  have hs1 : 1 ≤ s := by
    rw [hs]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hm0
  have hspos : 0 < s := by linarith
  have hsq : s ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith)
  have htsq : t ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hst : s ≤ t := by
    rw [hs, ht]
    exact Real.sqrt_le_sqrt (by linarith)
  have htpos : 0 < t := by linarith
  -- rewrite both sides over the common positive denominator `s * t^3`
  have hlhs : 1 / (((m : ℝ) + 1) * t) = 1 / t ^ 3 := by
    rw [← htsq]; ring_nf
  rw [hlhs]
  rw [div_sub_div _ _ (ne_of_gt hspos) (ne_of_gt htpos), div_le_div_iff₀ (by positivity)
    (by positivity)]
  -- `s * t * (t + s) ≤ 2 t^3` from `s ≤ t`
  have hkey : s * t ^ 2 + s ^ 2 * t ≤ 2 * t ^ 3 := by nlinarith
  nlinarith [hkey, sq_nonneg (t - s), mul_pos hspos htpos]

/-- **`∑_{2 ≤ n ≤ Y} 1/(n√n) ≤ 2 − 2/√Y`.**  Pure telescoping; no integral comparison. -/
theorem sum_Icc_inv_mul_sqrt_le_sub (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 2 Y, 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
      2 - 2 / Real.sqrt (Y : ℝ) := by
  induction Y with
  | zero => omega
  | succ Y ih =>
    rcases Nat.eq_or_lt_of_le hY with h1 | h1
    · have hY0 : Y = 0 := by omega
      subst hY0
      norm_num
    · have hY1 : 1 ≤ Y := by omega
      have hins : Finset.Icc 2 (Y + 1) = insert (Y + 1) (Finset.Icc 2 Y) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (Y + 1) ∉ Finset.Icc 2 Y := by simp
      rw [hins, Finset.sum_insert hnot]
      have hstep := inv_mul_sqrt_le_telescope hY1
      have := ih hY1
      have hcast : ((Y + 1 : ℕ) : ℝ) = (Y : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hstep ⊢
      linarith

/-- `∑_{2 ≤ n ≤ Y} 1/(n√n) ≤ 2`, uniformly in `Y`. -/
theorem sum_Icc_inv_mul_sqrt_le (Y : ℕ) :
    ∑ n ∈ Finset.Icc 2 Y, 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤ 2 := by
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp
  have h := sum_Icc_inv_mul_sqrt_le_sub Y hY
  have : (0 : ℝ) ≤ 2 / Real.sqrt (Y : ℝ) := by positivity
  linarith

/-- **`∑_{p ≤ Y} 1/(p√p) ≤ 2`** — the convergent prime sum the Rankin shift needs.  Compare
`ElliottEulerBound.sum_primesBelow_inv_mul_pred_le_one`, which is the unshifted analogue. -/
theorem sum_primesBelow_inv_mul_sqrt_le (Y : ℕ) :
    ∑ p ∈ Nat.primesBelow (Y + 1), 1 / ((p : ℝ) * Real.sqrt (p : ℝ)) ≤ 2 := by
  classical
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp [Nat.primesBelow_one]
  have hsub : Nat.primesBelow (Y + 1) ⊆ Finset.Icc 2 Y := by
    intro p hp
    obtain ⟨hpY, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.two_le, by omega⟩
  have hnn : ∀ n ∈ Finset.Icc 2 Y, n ∉ Nat.primesBelow (Y + 1) →
      0 ≤ 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    intro n _ _
    positivity
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) (sum_Icc_inv_mul_sqrt_le Y)

end NormalNumbers.ElliottRankin
