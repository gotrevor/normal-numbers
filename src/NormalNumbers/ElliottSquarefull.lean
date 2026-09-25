import NormalNumbers.ElliottEulerBound

/-!
# The squarefull tail: an ABSOLUTE bound

Leaf 2 (`NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM`), Case B, step (3) of the
`DIRECTION.md` CURRENT DIRECTIVE.

The two-point cover of `ElliottRandomize` produces a unimodular **multiplicative** `U`; the
dependency's `Erdos67b.unitCircleLogElliott` wants a unimodular **completely multiplicative** one.
The bridge is the squarefull convolution: let `Ũ` be the completely multiplicative function with
`Ũ p = U p`, and set `u = U ⋆ (μ · Ũ)`, so that `U = u ⋆ Ũ`.  Then

* `u p = U p - Ũ p = 0`, so `u` is supported on **squarefull** integers, and
* `‖u (p^k)‖ = ‖U (p^k) - U p · U (p^(k-1))‖ ≤ 2`.

Consequently `∑_{d ≤ Y} ‖u d‖ / d ≤ ∏_p (1 + 2/(p(p-1))) ≤ e²`.

**This is exactly the uniformity the refuted `v`-expansion lacked.**  There the local factor was
`1 + (1 - ‖g p‖)/(p - ‖g p‖)`, whose size depends on `g` and can be made large at primes beyond any
pre-chosen truncation `D`.  Here the local factor is `1 + 2/(p(p-1))`: the `1/p` term is *absent*
because `u p = 0`, and what remains is bounded by an **absolute** constant independent of `U`,
so the tail beyond any `D` is uniformly small over the whole family of covers.

This file proves the analytic half — the absolute bound for any nonnegative multiplicative `f`
with `f p = 0` at primes and `f n ≤ 2/n`.  The arithmetic half (that `‖u ·‖ / ·` is such an `f`)
is `ElliottSquarefullConv.lean`.

## Main results

* `geom_sum_Ico_two_le` — `∑_{2 ≤ k ≤ K} r^k ≤ r²/(1-r)`.
* `local_factor_squarefull_le` — the local factor is `≤ 1 + 2/(p(p-1))`.
* `sum_Icc_le_exp_two` — **`∑_{m ≤ Y} f m ≤ e²`, uniformly in `Y` and in `f`.**
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottSquarefull

open ArithmeticFunction NormalNumbers.ElliottEulerBound

/-- The geometric tail from exponent `2` on, bounded uniformly in the truncation `K`. -/
theorem geom_sum_Ico_two_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.Ico 2 (K + 1), r ^ k ≤ r ^ 2 / (1 - r) := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have : Finset.Ico 2 (K + 1) = ∅ := by
      rw [Finset.Ico_eq_empty]; omega
    rw [this, Finset.sum_empty]
    positivity
  have hgeom : ∑ k ∈ Finset.Ico 2 (K + 1), r ^ k =
      r ^ 2 * ∑ j ∈ Finset.range (K - 1), r ^ j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum, show K + 1 - 2 = K - 1 by omega]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [pow_add]
  have hpartial : ∑ j ∈ Finset.range (K - 1), r ^ j ≤ 1 / (1 - r) := by
    rw [geom_sum_eq (ne_of_lt hr1)]
    rw [show (r ^ (K - 1) - 1) / (r - 1) = (1 - r ^ (K - 1)) / (1 - r) by
      rw [← neg_sub (r ^ (K - 1)) 1, ← neg_sub r 1, neg_div_neg_eq]]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : 0 ≤ r ^ (K - 1) := by positivity
    nlinarith
  rw [hgeom]
  calc r ^ 2 * ∑ j ∈ Finset.range (K - 1), r ^ j ≤ r ^ 2 * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hpartial (by positivity)
    _ = r ^ 2 / (1 - r) := by ring

/-- **The squarefull local factor.**  Vanishing at the prime itself kills the `1/p` term, and the
remaining geometric tail is `2/(p(p-1))` — independent of `f` beyond the stated hypotheses. -/
theorem local_factor_squarefull_le {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hnn : ∀ n : ℕ, 0 ≤ f n) (hbd : ∀ n : ℕ, 0 < n → f n ≤ 2 / (n : ℝ))
    (hprime : ∀ p : ℕ, p.Prime → f p = 0)
    {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), f (p ^ k) ≤
      1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  classical
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / (p : ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hppos]; linarith
  have htail2 : r ^ 2 / (1 - r) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [hr, div_pow, one_pow]
    have h1 : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
    rw [h1]
    field_simp
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have htailnn : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    interval_cases K
    · rw [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, hf.map_one]
      linarith
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, pow_one, hf.map_one, hprime p hp]
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
    have htailbd : ∑ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) ≤
        2 * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      have hterm : ∀ k ∈ Finset.Ico 2 (K + 1), f (p ^ k) ≤ 2 * r ^ k := by
        intro k _
        have hkpos : 0 < p ^ k := pow_pos hp.pos k
        have h := hbd (p ^ k) hkpos
        have hcast : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by push_cast; ring
        rw [hcast] at h
        calc f (p ^ k) ≤ 2 / (p : ℝ) ^ k := h
          _ = 2 * r ^ k := by rw [hr, div_pow, one_pow]; ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum, ← htail2]
      exact mul_le_mul_of_nonneg_left (geom_sum_Ico_two_le hr0 hr1 K) (by norm_num)
    rw [hsplit, hf.map_one, hprime p hp]
    linarith

/-- **The absolute squarefull bound.**  For every nonnegative multiplicative `f` vanishing at the
primes and bounded by `2/n`, and for *every* truncation `Y`, `∑_{m ≤ Y} f m ≤ e²`.

Both the function and the scale are arbitrary: this is the uniformity that the refuted
`‖g̃‖ = 1 ⋆ v` expansion could not supply. -/
theorem sum_Icc_le_exp_two {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hnn : ∀ n : ℕ, 0 ≤ f n) (hbd : ∀ n : ℕ, 0 < n → f n ≤ 2 / (n : ℝ))
    (hprime : ∀ p : ℕ, p.Prime → f p = 0) (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, f m ≤ Real.exp 2 := by
  classical
  refine (sum_Icc_le_euler_product hf hnn Y).trans ?_
  have hF0 : ∀ p ∈ Nat.primesBelow (Y + 1),
      0 ≤ ∑ k ∈ Finset.range (Nat.log 2 Y + 1), f (p ^ k) :=
    fun p _ => Finset.sum_nonneg fun k _ => hnn _
  have hFle : ∀ p ∈ Nat.primesBelow (Y + 1),
      ∑ k ∈ Finset.range (Nat.log 2 Y + 1), f (p ^ k) ≤
        1 + (fun q : ℕ => 1 / ((q : ℝ) * ((q : ℝ) - 1))) p +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    exact local_factor_squarefull_le hf hnn hbd hprime (Nat.mem_primesBelow.mp hp).2 _
  refine (prod_le_exp_prime_sum hF0 hFle).trans ?_
  refine Real.exp_le_exp.mpr ?_
  linarith [sum_primesBelow_inv_mul_pred_le_one Y]

end NormalNumbers.ElliottSquarefull
