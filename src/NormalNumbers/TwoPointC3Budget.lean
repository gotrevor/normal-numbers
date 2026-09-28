/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointC3Pin
import NormalNumbers.PrimeLambertTail

/-!
# A concrete growing schedule: the peel budget, unconditionally

Rung 3 (`TwoPointC3Pin.lean`) made the crux equivalent to the growing-depth **unweighted** surface
*under* the peel budget, and showed no CONSTANT schedule can satisfy the budget.  This file closes
the gap: it exhibits a schedule that does, unconditionally, so the equivalence becomes a theorem
with no hypothesis — C3's analogue of `twoPointWeighted_iff_growing_id`.

The ingredient is a uniform upper bound on the tail, the mirror of rung 2's lower bound:

    tailLarge_le_log :  tailLarge P b m  ≤  log₂(m+1) + 1     (every `b ≥ 2`, every `P`)

from `ω(m) ≤ log₂ m` (`omegaR_le_log`), `log₂(m+i+1) ≤ log₂(m+1) + i` (`log_add_le`) and
`∑_{i≥0}(A+i)2^{−(i+1)} = A+1` (`tsum_majorant`).  Then the budget at the schedule `K(N) = N` is

    b^{−N}·(1/N)∑_{n<N} tailLarge P b (n+N)  ≤  b^{−N}·(log₂(2N+1) + 1)  ≤  (2N+2)/2^N  →  0 ,

the last limit because `∑ n·2^{−n}` converges.  Schedule invariance (rung 3) then says the depth
`N` surface is no harder than any other admissible one; what matters is only that the depth grows.
-/

open Filter Topology Finset

namespace NormalNumbers.CastingOut

open PrimeLambert

/-! ### The uniform upper bound on the tail -/

/-- **The mirror of rung 2.**  The large-prime tail is at most `log₂(m+1) + 1`, uniformly in `P`
and in `b ≥ 2`. -/
theorem tailLarge_le_log {b : ℕ} (hb : 2 ≤ b) (P m : ℕ) :
    tailLarge P b m ≤ (Nat.log 2 (m + 1) : ℝ) + 1 := by
  set A : ℝ := (Nat.log 2 (m + 1) : ℝ) with hA
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hmaj : Summable (fun i : ℕ => (A + (i : ℝ)) / 2 ^ (i + 1)) := by
    have := (summable_geom_shift.mul_left A).add summable_i_geom
    refine this.congr (fun i => ?_); ring
  have hterm : ∀ i : ℕ, (omegaLarge P (m + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)
      ≤ (A + (i : ℝ)) / 2 ^ (i + 1) := by
    intro i
    have hnum : (omegaLarge P (m + i + 1) : ℝ) ≤ A + (i : ℝ) := by
      have h1 : omegaLarge P (m + i + 1) ≤ (m + i + 1).primeFactors.card :=
        Finset.card_filter_le _ _
      have h2 : (m + i + 1).primeFactors.card ≤ Nat.log 2 (m + i + 1) :=
        card_primeFactors_le_log _ (by omega)
      have h3 : Nat.log 2 (m + i + 1) ≤ Nat.log 2 (m + 1) + i := log_add_le m i
      have : omegaLarge P (m + i + 1) ≤ Nat.log 2 (m + 1) + i := by omega
      rw [hA]
      exact_mod_cast this
    have hden : (2 : ℝ) ^ (i + 1) ≤ (b : ℝ) ^ (i + 1) := by gcongr
    have hnn : (0 : ℝ) ≤ A + (i : ℝ) := by
      have : (0 : ℝ) ≤ A := by rw [hA]; positivity
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      positivity
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
    have hpos2 : (0 : ℝ) < (b : ℝ) ^ (i + 1) := by positivity
    rw [div_le_div_iff₀ hpos2 hpos1]
    have hom : (0 : ℝ) ≤ (omegaLarge P (m + i + 1) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hval : ∑' i : ℕ, (A + (i : ℝ)) / 2 ^ (i + 1) = A + 1 := by
    have h := tsum_majorant A 0
    simpa using h
  calc tailLarge P b m
      = ∑' i : ℕ, (omegaLarge P (m + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := rfl
    _ ≤ ∑' i : ℕ, (A + (i : ℝ)) / 2 ^ (i + 1) :=
        Summable.tsum_le_tsum hterm (summable_tailLarge hb P m) hmaj
    _ = A + 1 := hval

/-! ### The budget at the schedule `K(N) = N` -/

/-- `(2N+2)/2^N → 0`: the terms of a convergent series. -/
lemma tendsto_linear_div_two_pow :
    Tendsto (fun N : ℕ => (2 * (N : ℝ) + 2) / 2 ^ N) atTop (𝓝 0) := by
  have hs : Summable (fun N : ℕ => (2 * (N : ℝ) + 2) / 2 ^ N) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / 2 : ℝ)) (by
      rw [Real.norm_eq_abs]; norm_num)
    have h2 : Summable (fun N : ℕ => ((1 : ℝ) / 2) ^ N) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine ((h1.mul_left 2).add (h2.mul_left 2)).congr (fun N => ?_)
    rw [pow_one, one_div_pow]
    field_simp
  exact hs.tendsto_atTop_zero

/-- **The peel budget holds at the schedule `K(N) = N`.**  Unconditional. -/
theorem peelBudget_id {b : ℕ} (hb : 2 ≤ b) (P : ℕ) (h : ℤ) :
    PeelBudget P b h (fun N => N) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hnn : ∀ m : ℕ, 0 ≤ tailLarge P b m := fun m => tsum_nonneg fun i => by positivity
  rw [PeelBudget]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ tendsto_linear_div_two_pow
  · -- nonnegativity
    have : 0 ≤ ∑ n ∈ range N, ((b : ℝ) ^ N)⁻¹ * tailLarge P b (n + N) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (hnn _)
    positivity
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    -- each term of the shifted mean is at most `log₂(2N+1) + 1 ≤ 2N + 2`
    have hbound : ∀ n ∈ range N, tailLarge P b (n + N) ≤ 2 * (N : ℝ) + 2 := by
      intro n hn
      have hnN : n < N := mem_range.1 hn
      refine (tailLarge_le_log hb P (n + N)).trans ?_
      have hlog : Nat.log 2 (n + N + 1) ≤ n + N + 1 := Nat.log_le_self _ _
      have : (Nat.log 2 (n + N + 1) : ℝ) ≤ (n : ℝ) + (N : ℝ) + 1 := by
        have h2 : ((n + N + 1 : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) + 1 := by push_cast; ring
        calc (Nat.log 2 (n + N + 1) : ℝ) ≤ ((n + N + 1 : ℕ) : ℝ) := by exact_mod_cast hlog
          _ = (n : ℝ) + (N : ℝ) + 1 := h2
      have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN.le
      linarith
    have hsum : ∑ n ∈ range N, ((b : ℝ) ^ N)⁻¹ * tailLarge P b (n + N)
        ≤ (N : ℝ) * (((b : ℝ) ^ N)⁻¹ * (2 * (N : ℝ) + 2)) := by
      calc ∑ n ∈ range N, ((b : ℝ) ^ N)⁻¹ * tailLarge P b (n + N)
          ≤ ∑ _n ∈ range N, ((b : ℝ) ^ N)⁻¹ * (2 * (N : ℝ) + 2) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have := hbound n hn
            have hc : (0 : ℝ) ≤ ((b : ℝ) ^ N)⁻¹ := by positivity
            exact mul_le_mul_of_nonneg_left this hc
        _ = (N : ℝ) * (((b : ℝ) ^ N)⁻¹ * (2 * (N : ℝ) + 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    have hpow : ((b : ℝ) ^ N)⁻¹ ≤ ((2 : ℝ) ^ N)⁻¹ := by
      have h2 : (2 : ℝ) ^ N ≤ (b : ℝ) ^ N := by gcongr
      have hp2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
      have := one_div_le_one_div_of_le hp2 h2
      simpa [one_div] using this
    calc (∑ n ∈ range N, ((b : ℝ) ^ N)⁻¹ * tailLarge P b (n + N)) / N
        ≤ ((N : ℝ) * (((b : ℝ) ^ N)⁻¹ * (2 * (N : ℝ) + 2))) / N := by
          gcongr
      _ = ((b : ℝ) ^ N)⁻¹ * (2 * (N : ℝ) + 2) := by field_simp
      _ ≤ ((2 : ℝ) ^ N)⁻¹ * (2 * (N : ℝ) + 2) := by
          have hnn2 : (0 : ℝ) ≤ 2 * (N : ℝ) + 2 := by positivity
          exact mul_le_mul_of_nonneg_right hpow hnn2
      _ = (2 * (N : ℝ) + 2) / 2 ^ N := by rw [inv_mul_eq_div]

/-- **The pin, unconditionally.**  The crux is equivalent to the growing-depth *unweighted*
surface at the schedule `K(N) = N` — no hypothesis.  C3's analogue of
`twoPointWeighted_iff_growing_id`; with `no_constant_depth_budget` it says the depth must grow and
that any growing depth states the same problem. -/
theorem addCharTail_iff_plain_id {b : ℕ} (hb : 2 ≤ b) (P Q j : ℕ) (h : ℤ) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
          * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)) / N) atTop (𝓝 0)
      ↔ Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
          * ee (((h : ℝ) * depthPeel P b N n : ℝ) : ℂ)) / N) atTop (𝓝 0) :=
  addCharTail_iff_plain_of_budget hb P Q j h (fun N => N) (peelBudget_id hb P h)

end NormalNumbers.CastingOut
