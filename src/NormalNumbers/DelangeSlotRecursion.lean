import Mathlib

/-!
# L7: a complex linear recursion with a rotating coefficient

Pure sequence analysis, no number theory.  Given `‖σ k‖ ≤ 1` and

    ‖(log N − z) · σ N − z · Ψ N‖ ≤ C,      Ψ N = ∑_{1 ≤ k < N} σ k / (k+1),

with `‖z‖ = 1` and `Re z < 1`, we conclude `σ N → 0`.

The mechanism: `Ψ (N+1) = Ψ N · (1 + a N) + e N` with `a N = z / ((N+1)(log N − z))`, so the
integrating factor is `∏ (1 + a n)`, whose **modulus** is governed by
`Re a n ≈ Re z / (n log n)`.  Since `∑ 1/(n log n) = log log N + O(1)`, that product is
`≍ (log N)^{Re z}`, and `Re z < 1` makes `‖Ψ N‖ = o(log N)`, i.e. `σ N → 0`.
The inhomogeneous part contributes another `log log N`, which is harmless.

`Re z = 1` with `‖z‖ = 1` forces `z = 1`, so `z ≠ 1` is exactly the hypothesis `Re z < 1`.
-/

open Finset Filter Topology

namespace NormalNumbers.DelangeSlot

/-- Step (a): the pointwise telescoping bound `1/(n log n) ≤ log log n − log log (n−1)`,
by the mean value theorem applied to `log ∘ log` on `[n−1, n]`. -/
lemma one_div_mul_log_le_sub {n : ℕ} (hn : 3 ≤ n) :
    1 / ((n : ℝ) * Real.log n) ≤ Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ)) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1:ℕ) ≤ n := by lia
    push_cast [this]; ring
  rw [hcast]
  set a : ℝ := (n : ℝ) - 1 with ha
  have hn3 : (3:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha2 : (2:ℝ) ≤ a := by simp [ha]; linarith
  have hab : a < (n : ℝ) := by simp [ha]
  have hder : ∀ t : ℝ, 1 < t → HasDerivAt (fun x => Real.log (Real.log x)) (1 / (t * Real.log t)) t := by
    intro t ht
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (by linarith)
    have hlt : 0 < Real.log t := Real.log_pos ht
    have h2 : HasDerivAt Real.log (Real.log t)⁻¹ (Real.log t) := Real.hasDerivAt_log hlt.ne'
    have h3 := h2.comp t h1
    have key : 1 / (t * Real.log t) = (Real.log t)⁻¹ * t⁻¹ := by
      rw [one_div, mul_inv, mul_comm]
    rw [key]
    exact h3
  have hcont : ContinuousOn (fun x => Real.log (Real.log x)) (Set.Icc a (n:ℝ)) := by
    intro t ht
    have ht1 : 1 < t := by have := ht.1; simp [ha] at this ⊢; linarith
    exact ((hder t ht1).continuousAt).continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun x => Real.log (Real.log x))
    (fun t => 1 / (t * Real.log t)) hab hcont
    (fun t ht => hder t (by have := ht.1; simp [ha] at this ⊢; linarith))
  have hc1 : 1 < c := by have := hc.1; simp [ha] at this ⊢; linarith
  have hcn : c ≤ (n:ℝ) := hc.2.le
  rw [show (n:ℝ) - a = 1 by simp [ha], div_one] at hceq
  rw [← hceq]
  have hmono : c * Real.log c ≤ (n:ℝ) * Real.log n :=
    mul_le_mul hcn (Real.log_le_log (by linarith) hcn) (Real.log_nonneg hc1.le) (by linarith)
  have hcpos : 0 < c * Real.log c := by
    have : 0 < Real.log c := Real.log_pos hc1
    positivity
  exact one_div_le_one_div_of_le hcpos hmono

/-- Step (b): `∑_{3 ≤ n ≤ N} 1/(n log n) ≤ log log N − log log 2`. -/
lemma sum_one_div_mul_log_le {N : ℕ} (hN : 3 ≤ N) :
    ∑ n ∈ Icc 3 N, 1 / ((n : ℝ) * Real.log n)
      ≤ Real.log (Real.log N) - Real.log (Real.log 2) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have := one_div_mul_log_le_sub (n := 3) le_rfl
    simpa using this
  | succ N hN ih =>
    have hstep := one_div_mul_log_le_sub (n := N + 1) (by lia)
    have hc : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by norm_num
    rw [hc] at hstep
    rw [Finset.sum_Icc_succ_top (by lia)]
    have : (((N : ℕ) + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    linarith [ih, hstep]

/-- Step (c): the modulus of one step of the integrating factor.  For every `β` with
`max (Re z) 0 < β` there is a threshold past which `‖1 + z/((n+1)(log n − z))‖ ≤ 1 + β/((n+1) log n)`. -/
lemma eventually_norm_one_add_le {z : ℂ} (hz : ‖z‖ = 1) {β : ℝ} (hβ : max z.re 0 < β) :
    ∀ᶠ n : ℕ in atTop,
      ‖1 + z / (((n : ℂ) + 1) * ((Real.log n : ℂ) - z))‖ ≤ 1 + β / (((n : ℝ) + 1) * Real.log n) := by
  sorry

/-- **L7.**  The recursion forces `σ N → 0`. -/
theorem recursion_tendsto_zero {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z.re < 1) (C : ℝ) (σ : ℕ → ℂ)
    (hσ : ∀ k, ‖σ k‖ ≤ 1)
    (hrec : ∀ N : ℕ, 2 ≤ N →
      ‖((Real.log N : ℂ) - z) * σ N - z * ∑ k ∈ Ico 1 N, σ k / ((k : ℂ) + 1)‖ ≤ C) :
    Tendsto σ atTop (𝓝 0) := by
  sorry

end NormalNumbers.DelangeSlot
