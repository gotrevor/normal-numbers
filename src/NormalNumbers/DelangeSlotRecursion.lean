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

/-- The abstract second-order absorption: `‖1 + a‖ ≤ 1 + s` whenever `2 Re a + ‖a‖² ≤ 2 s`. -/
lemma norm_one_add_le_of_re {a : ℂ} {s : ℝ} (hs : 0 ≤ s) (h : 2 * a.re + ‖a‖ ^ 2 ≤ 2 * s) :
    ‖1 + a‖ ≤ 1 + s := by
  have hsq : ‖1 + a‖ ^ 2 = 1 + ‖a‖ ^ 2 + 2 * a.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp
  have h1 : ‖1 + a‖ ^ 2 ≤ (1 + s) ^ 2 := by rw [hsq]; nlinarith
  nlinarith [norm_nonneg ((1:ℂ) + a), h1, hs]

/-- Step (c), explicit form.  With `a = u · z/(L − z)` the second-order term is absorbed:
`‖1 + a‖ ≤ 1 + β u / L` as soon as `L` is past an explicit threshold. -/
lemma norm_one_add_le {z : ℂ} (hz : ‖z‖ = 1) {β L u : ℝ} (hβ : max z.re 0 < β)
    (hL2 : 2 ≤ L) (hLthr : 1 + 4 * β ≤ 2 * (β - max z.re 0) * L)
    (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖1 + (u : ℂ) * (z / ((L : ℂ) - z))‖ ≤ 1 + β * u / L := by
  have hα1 : z.re ≤ 1 := by
    have := Complex.abs_re_le_norm z
    rw [hz] at this
    exact (abs_le.1 this).2
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by rw [hz]; ring
    rw [← Complex.normSq_eq_norm_sq] at h
    simpa [Complex.normSq_apply, sq] using h
  set α := z.re with hαdef
  have hβ0 : 0 < β := lt_of_le_of_lt (le_max_right _ _) hβ
  have hm0 : (0:ℝ) ≤ max α 0 := le_max_right _ _
  have hmα : α ≤ max α 0 := le_max_left _ _
  have hL0 : (0:ℝ) < L := by linarith
  set w : ℂ := (L : ℂ) - z with hw
  have hwre : w.re = L - α := by simp [hw, hαdef]
  have hwim : w.im = -z.im := by simp [hw]
  have hQ : Complex.normSq w = L ^ 2 - 2 * α * L + 1 := by
    simp only [Complex.normSq_apply, hwre, hwim]
    nlinarith [hnorm]
  have hQpos : 0 < Complex.normSq w := by rw [hQ]; nlinarith [sq_nonneg (L - α)]
  set Q := Complex.normSq w with hQdef
  have hdivre : (z / w).re = (α * L - 1) / Q := by
    rw [Complex.div_re, hwre, hwim, ← add_div]
    congr 1
    nlinarith [hnorm]
  have hwnorm : ‖w‖ ^ 2 = Q := (Complex.normSq_eq_norm_sq w).symm
  have hanormsq : ‖(u : ℂ) * (z / w)‖ ^ 2 = u ^ 2 / Q := by
    rw [norm_mul, norm_div, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu,
      mul_pow, div_pow, one_pow, hwnorm]
    ring
  have hare : ((u : ℂ) * (z / w)).re = u * ((α * L - 1) / Q) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hdivre]
  refine norm_one_add_le_of_re (by positivity) ?_
  rw [hare, hanormsq]
  have expand : 2 * (u * ((α * L - 1) / Q)) + u ^ 2 / Q
      = ((2 * (α * L - 1) + u) * u) / Q := by field_simp
  have rhs : 2 * (β * u / L) = (2 * β * u) / L := by ring
  rw [expand, rhs, div_le_div_iff₀ hQpos hL0]
  have hkey : (2 * (α * L - 1) + u) * L ≤ 2 * β * Q := by
    have hLthr' : (1 + 4 * β) * L ≤ 2 * (β - max α 0) * L * L :=
      mul_le_mul_of_nonneg_right hLthr hL0.le
    rw [hQ]
    have e1 : α * L ^ 2 ≤ max α 0 * L ^ 2 :=
      mul_le_mul_of_nonneg_right hmα (sq_nonneg L)
    have e2 : u * L ≤ 1 * L := mul_le_mul_of_nonneg_right hu1 hL0.le
    have e3 : (0:ℝ) ≤ (1 - α) * (β * L) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [hLthr', e1, e2, e3, hL0, hβ0]
  have := mul_le_mul_of_nonneg_left hkey hu.le
  calc (2 * (α * L - 1) + u) * u * L = u * ((2 * (α * L - 1) + u) * L) := by ring
    _ ≤ u * (2 * β * Q) := this
    _ = 2 * β * u * Q := by ring

/-- Step (c): the modulus of one step of the integrating factor.  For every `β` with
`max (Re z) 0 < β` there is a threshold past which `‖1 + z/((n+1)(log n − z))‖ ≤ 1 + β/((n+1) log n)`. -/
lemma eventually_norm_one_add_le {z : ℂ} (hz : ‖z‖ = 1) {β : ℝ} (hβ : max z.re 0 < β) :
    ∀ᶠ n : ℕ in atTop,
      ‖1 + z / (((n : ℂ) + 1) * ((Real.log n : ℂ) - z))‖ ≤ 1 + β / (((n : ℝ) + 1) * Real.log n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in atTop, (2:ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 2
  have h2 : ∀ᶠ n : ℕ in atTop, (1 + 4 * β) / (2 * (β - max z.re 0)) ≤ Real.log n :=
    hlog.eventually_ge_atTop _
  filter_upwards [h1, h2] with n hn1 hn2
  have hγ : 0 < 2 * (β - max z.re 0) := by
    have : 0 < β - max z.re 0 := by linarith
    linarith
  have hthr : 1 + 4 * β ≤ 2 * (β - max z.re 0) * Real.log n := by
    rw [div_le_iff₀ hγ] at hn2
    linarith [hn2]
  have hu : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hu1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have := norm_one_add_le hz hβ hn1 hthr hu hu1
  have heq1 : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (z / ((Real.log n : ℂ) - z))
      = z / (((n : ℂ) + 1) * ((Real.log n : ℂ) - z)) := by
    have hn0 : ((n : ℂ) + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [this]
    push_cast
    field_simp
  have heq2 : β * (1 / ((n : ℝ) + 1)) / Real.log n = β / (((n : ℝ) + 1) * Real.log n) := by
    field_simp
  rw [heq1, heq2] at this
  exact this

/-- **L7.**  The recursion forces `σ N → 0`. -/
theorem recursion_tendsto_zero {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z.re < 1) (C : ℝ) (σ : ℕ → ℂ)
    (hσ : ∀ k, ‖σ k‖ ≤ 1)
    (hrec : ∀ N : ℕ, 2 ≤ N →
      ‖((Real.log N : ℂ) - z) * σ N - z * ∑ k ∈ Ico 1 N, σ k / ((k : ℂ) + 1)‖ ≤ C) :
    Tendsto σ atTop (𝓝 0) := by
  sorry

end NormalNumbers.DelangeSlot
