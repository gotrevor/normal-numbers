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

/-! ## The shifted weight -/

noncomputable section

open NormalNumbers.ElliottSquarefullConv

/-- `n ↦ ‖u n‖ / n^{3/4}`, the Rankin-shifted weight. -/
def shifted (u : ArithmeticFunction ℂ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else ‖u n‖ / (n : ℝ) ^ ((3 : ℝ) / 4)
  map_zero' := by simp

theorem shifted_apply (u : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0) :
    shifted u n = ‖u n‖ / (n : ℝ) ^ ((3 : ℝ) / 4) := by simp [shifted, hn]

theorem shifted_nonneg (u : ArithmeticFunction ℂ) (n : ℕ) : 0 ≤ shifted u n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [shifted]
  · rw [shifted_apply u hn]
    have : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    positivity

theorem isMultiplicative_shifted {u : ArithmeticFunction ℂ} (hu : u.IsMultiplicative) :
    (shifted u).IsMultiplicative := by
  refine ⟨?_, fun {m n} hcop => ?_⟩
  · rw [shifted_apply u one_ne_zero, hu.map_one]
    norm_num
  · rcases eq_or_ne m 0 with rfl | hm
    · simp [shifted]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [shifted]
    rw [shifted_apply u (Nat.mul_ne_zero hm hn), shifted_apply u hm, shifted_apply u hn,
      hu.map_mul_of_coprime hcop, norm_mul]
    have hsplit : (((m * n : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
        = (m : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) := by
      push_cast
      exact Real.mul_rpow (by positivity) (by positivity)
    rw [hsplit]
    field_simp

/-- `2^{-3/4} ≤ 3/5`, i.e. `5/3 ≤ 2^{3/4}`: the only numeric constant the shift needs.
It is genuinely tight-ish — `(5/3)^4 = 625/81 ≈ 7.72` against `2^3 = 8`. -/
theorem five_div_three_le_rpow {x : ℝ} (hx : 2 ≤ x) : (5 : ℝ) / 3 ≤ x ^ ((3 : ℝ) / 4) := by
  have h2 : ((2 : ℝ)) ^ ((3 : ℝ) / 4) ≤ x ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  refine le_trans ?_ h2
  have hnn : (0 : ℝ) ≤ ((2 : ℝ)) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
  have hpow : (((2 : ℝ)) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) = 8 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
    rw [show ((3 : ℝ) / 4) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hnn ?_
  rw [hpow]
  norm_num

/-- The shifted local ratio is at most `3/5`, so `1 − r ≥ 2/5`. -/
theorem rpow_neg_le {p : ℕ} (hp : 2 ≤ p) :
    1 / (p : ℝ) ^ ((3 : ℝ) / 4) ≤ 3 / 5 := by
  have hx : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h := five_div_three_le_rpow hx
  have hpos : (0 : ℝ) < (p : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- The shifted local factor is `≤ 1 + 5/(p√p)`. -/
theorem local_factor_shifted_le {U : ℕ → ℂ} (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1)
    {p : ℕ} (hpp : p.Prime) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), shifted (squarefullPart U) (p ^ k) ≤
      1 + 5 * (1 / ((p : ℝ) * Real.sqrt (p : ℝ))) := by
  have hf := isMultiplicative_shifted (isMultiplicative_squarefullPart U hone hmul)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  set r : ℝ := 1 / (p : ℝ) ^ ((3 : ℝ) / 4) with hr
  have hrpos : (0 : ℝ) < (p : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr35 : r ≤ 3 / 5 := rpow_neg_le hpp.two_le
  have hr1 : r < 1 := by linarith
  have hprime0 : shifted (squarefullPart U) p = 0 := by
    rw [shifted_apply _ hpp.ne_zero, squarefullPart_prime_eq_zero U hone hpp]
    simp
  have hbd : ∀ k : ℕ, shifted (squarefullPart U) (p ^ k) ≤ 2 * r ^ k := by
    intro k
    have hpk : (p ^ k : ℕ) ≠ 0 := pow_ne_zero k hpp.ne_zero
    rw [shifted_apply _ hpk]
    have hcast : (((p ^ k : ℕ) : ℝ)) ^ ((3 : ℝ) / 4) = ((p : ℝ) ^ ((3 : ℝ) / 4)) ^ k := by
      push_cast
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast ((p : ℝ) ^ ((3 : ℝ) / 4)) k, ← Real.rpow_mul (by positivity)]
      ring_nf
    rw [hcast, hr, div_pow, one_pow,
      show (2 : ℝ) * (1 / ((p : ℝ) ^ ((3 : ℝ) / 4)) ^ k)
        = 2 / ((p : ℝ) ^ ((3 : ℝ) / 4)) ^ k by ring]
    gcongr
    exact norm_squarefullPart_prime_pow_le_two U hU hpp k
  refine (local_factor_geom_le hf hpp hprime0 hr0 hr1 hbd K).trans ?_
  have hrsq : r ^ 2 = 1 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
    rw [hr, div_pow, one_pow]
    congr 1
    rw [← Real.rpow_natCast ((p : ℝ) ^ ((3 : ℝ) / 4)) 2, ← Real.rpow_mul (by positivity),
      Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith) (by norm_num)]
    norm_num
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  have hdiv : r ^ 2 / (1 - r) ≤ r ^ 2 / (2 / 5) := by
    gcongr <;> linarith
  have heq : r ^ 2 / ((2 : ℝ) / 5) = 5 / 2 * r ^ 2 := by ring
  rw [← hrsq]
  rw [heq] at hdiv
  linarith

/-- **The shifted total is absolutely bounded.**  `∑_{d ≤ Y} ‖u d‖/d^{3/4} ≤ e^{11}`, for every
unimodular multiplicative `U` and every `Y`.  This is the Rankin-shifted analogue of lap 57's
`e²` bound, and it is what converts a bounded total into a *uniformly small tail*. -/
theorem sum_Icc_shifted_le (U : ℕ → ℂ) (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1) (Y : ℕ) :
    ∑ d ∈ Finset.Icc 1 Y, shifted (squarefullPart U) d ≤ Real.exp 11 := by
  classical
  have hf := isMultiplicative_shifted (isMultiplicative_squarefullPart U hone hmul)
  refine (sum_Icc_le_euler_product hf (shifted_nonneg _) Y).trans ?_
  have hF0 : ∀ p ∈ Nat.primesBelow (Y + 1),
      0 ≤ ∑ k ∈ Finset.range (Nat.log 2 Y + 1), shifted (squarefullPart U) (p ^ k) :=
    fun p _ => Finset.sum_nonneg fun k _ => shifted_nonneg _ _
  have hFle : ∀ p ∈ Nat.primesBelow (Y + 1),
      ∑ k ∈ Finset.range (Nat.log 2 Y + 1), shifted (squarefullPart U) (p ^ k) ≤
        1 + (fun q : ℕ => 5 * (1 / ((q : ℝ) * Real.sqrt (q : ℝ)))) p +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have htailnn : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    have := local_factor_shifted_le hone hmul hU hpp (Nat.log 2 Y)
    simp only
    linarith
  refine (prod_le_exp_prime_sum hF0 hFle).trans ?_
  refine Real.exp_le_exp.mpr ?_
  have hsum : ∑ p ∈ Nat.primesBelow (Y + 1),
      (fun q : ℕ => 5 * (1 / ((q : ℝ) * Real.sqrt (q : ℝ)))) p ≤ 10 := by
    simp only
    rw [← Finset.mul_sum]
    linarith [sum_primesBelow_inv_mul_sqrt_le Y]
  linarith

/-! ## The Rankin step and the uniform tail -/

/-- **The Rankin step.**  `‖u d‖/d = (‖u d‖/d^{3/4}) / d^{1/4}`, so a lower bound on `d` converts
the shifted weight into the unshifted one at a uniform discount. -/
theorem norm_div_le_shifted_div {u : ArithmeticFunction ℂ} {d D : ℕ} (hd : D + 1 ≤ d) :
    ‖u d‖ / (d : ℝ) ≤ shifted u d / ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hDpos : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
  have hsplit : (d : ℝ) = (d : ℝ) ^ ((3 : ℝ) / 4) * (d : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hdpos]
    norm_num
  have h34 : (0 : ℝ) < (d : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hdpos _
  have h14 : (0 : ℝ) < (d : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hdpos _
  have hmono : ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) := by
    refine Real.rpow_le_rpow hDpos.le ?_ (by norm_num)
    exact_mod_cast hd
  rw [shifted_apply u (by omega : d ≠ 0), div_div]
  have hle : (d : ℝ) ^ ((3 : ℝ) / 4) * ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ (d : ℝ) := by
    calc (d : ℝ) ^ ((3 : ℝ) / 4) * ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (d : ℝ) ^ ((3 : ℝ) / 4) * (d : ℝ) ^ ((1 : ℝ) / 4) := by gcongr
      _ = (d : ℝ) := hsplit.symm
  gcongr

/-- **The uniformly small squarefull tail.**  For every `ε > 0` there is a truncation point `D`,
depending on `ε` alone, with `∑_{D < d ≤ Y} ‖u d‖/d ≤ ε` for **every** unimodular multiplicative
`U` and every `Y`.

This is the obligation `NormalNumbers.ElliottLeafTwo.exists_squarefull_tail`, found while
assembling leaf 2 at lap 60.  It is strictly stronger than lap 57's bound on the total, and it is
the step at which the corrected route does what the refuted `v`-expansion could not. -/
theorem exists_squarefull_tail_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ U : ℕ → ℂ, U 1 = 1 →
        (∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y) →
        (∀ n : ℕ, 0 < n → ‖U n‖ = 1) →
        ∀ Y : ℕ,
          ∑ d ∈ Finset.Icc (D + 1) Y, ‖squarefullPart U d‖ / (d : ℝ) ≤ ε := by
  classical
  set M : ℝ := Real.exp 11 / ε with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  refine ⟨max 1 ⌈M ^ (4 : ℕ)⌉₊, le_max_left _ _, ?_⟩
  intro U hone hmul hU Y
  set D : ℕ := max 1 ⌈M ^ (4 : ℕ)⌉₊ with hD
  have hDpos : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
  -- the discount factor is at least `M`
  have hMle : M ≤ ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    have hge : M ^ (4 : ℕ) ≤ ((D + 1 : ℕ) : ℝ) := by
      have h1 : (⌈M ^ (4 : ℕ)⌉₊ : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by
        have : ⌈M ^ (4 : ℕ)⌉₊ ≤ D + 1 := le_trans (le_max_right 1 _) (by omega)
        exact_mod_cast this
      exact le_trans (Nat.le_ceil _) h1
    have h2 : (M ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hge (by norm_num)
    refine le_trans (le_of_eq ?_) h2
    rw [← Real.rpow_natCast M 4, ← Real.rpow_mul hMpos.le]
    norm_num
  -- the shifted total
  have htot := sum_Icc_shifted_le U hone hmul hU Y
  have hstep : ∑ d ∈ Finset.Icc (D + 1) Y, ‖squarefullPart U d‖ / (d : ℝ) ≤
      ∑ d ∈ Finset.Icc (D + 1) Y,
        shifted (squarefullPart U) d / ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    refine Finset.sum_le_sum fun d hd => ?_
    exact norm_div_le_shifted_div (Finset.mem_Icc.mp hd).1
  have hsub : ∑ d ∈ Finset.Icc (D + 1) Y, shifted (squarefullPart U) d ≤ Real.exp 11 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun i _ _ => shifted_nonneg _ i)) htot
    intro d hd
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
  have hrp : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hDpos _
  calc ∑ d ∈ Finset.Icc (D + 1) Y, ‖squarefullPart U d‖ / (d : ℝ)
      ≤ ∑ d ∈ Finset.Icc (D + 1) Y,
          shifted (squarefullPart U) d / ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := hstep
    _ = (∑ d ∈ Finset.Icc (D + 1) Y, shifted (squarefullPart U) d)
          / ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by rw [Finset.sum_div]
    _ ≤ Real.exp 11 / ((D + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by gcongr
    _ ≤ Real.exp 11 / M := by
        gcongr
    _ = ε := by rw [hM]; field_simp

end

end NormalNumbers.ElliottRankin
