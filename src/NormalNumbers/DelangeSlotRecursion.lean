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

/-- Discrete Gronwall: `r (n+1) ≤ r n · q n + d n` with `q ≥ 1`, `d ≥ 0` integrates to the
product/sum bound. -/
lemma gronwall {r d q : ℕ → ℝ} {N₀ : ℕ}
    (hstep : ∀ n, N₀ ≤ n → r (n + 1) ≤ r n * q n + d n)
    (hq : ∀ n, N₀ ≤ n → 1 ≤ q n) (hd : ∀ n, N₀ ≤ n → 0 ≤ d n) (hr0 : 0 ≤ r N₀) :
    ∀ N, N₀ ≤ N → r N ≤ (r N₀ + ∑ n ∈ Ico N₀ N, d n) * ∏ n ∈ Ico N₀ N, q n := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hP1 : (1:ℝ) ≤ ∏ n ∈ Ico N₀ N, q n :=
      Finset.one_le_prod fun n hn => hq n (mem_Ico.1 hn).1
    have hP0 : (0:ℝ) ≤ ∏ n ∈ Ico N₀ N, q n := le_trans zero_le_one hP1
    have hqN : 1 ≤ q N := hq N hN
    have hdN : 0 ≤ d N := hd N hN
    have hDsum : 0 ≤ ∑ n ∈ Ico N₀ N, d n :=
      Finset.sum_nonneg fun n hn => hd n (mem_Ico.1 hn).1
    have h1 : r (N + 1) ≤ ((r N₀ + ∑ n ∈ Ico N₀ N, d n) * ∏ n ∈ Ico N₀ N, q n) * q N + d N := by
      refine le_trans (hstep N hN) ?_
      have := mul_le_mul_of_nonneg_right ih (le_trans zero_le_one hqN)
      linarith
    rw [Finset.sum_Ico_succ_top hN, Finset.prod_Ico_succ_top hN]
    have hPq : (1:ℝ) ≤ (∏ n ∈ Ico N₀ N, q n) * q N :=
      le_trans hP1 (le_mul_of_one_le_right hP0 hqN)
    have h2 : d N ≤ d N * ((∏ n ∈ Ico N₀ N, q n) * q N) := le_mul_of_one_le_right hdN hPq
    nlinarith [h1, h2, hP0, hqN]

/-- Every term of the two tail sums is dominated by `1/(n log n)` on `n ≥ 3`. -/
lemma subset_Icc {N₀ N : ℕ} (h3 : 3 ≤ N₀) : Ico N₀ N ⊆ Icc 3 N := by
  intro n hn
  rw [mem_Ico] at hn
  exact mem_Icc.2 ⟨le_trans h3 hn.1, hn.2.le⟩

/-- The integrating factor is at most `(log N)^β`, up to the constant `(log 2)^{-β}`. -/
lemma prod_bound {β : ℝ} (hβ : 0 ≤ β) {N₀ N : ℕ} (h3 : 3 ≤ N₀) (hN : 3 ≤ N) :
    ∏ n ∈ Ico N₀ N, (1 + β / (((n : ℝ) + 1) * Real.log n))
      ≤ Real.exp (β * (Real.log (Real.log N) - Real.log (Real.log 2))) := by
  have hterm : ∀ n ∈ Ico N₀ N, (0:ℝ) ≤ 1 + β / (((n : ℝ) + 1) * Real.log n) := by
    intro n hn
    have h3n : 3 ≤ n := le_trans h3 (mem_Ico.1 hn).1
    have : (0:ℝ) < Real.log n := Real.log_pos (by exact_mod_cast by lia : (1:ℝ) < (n:ℝ))
    positivity
  have hle : ∀ n ∈ Ico N₀ N, 1 + β / (((n : ℝ) + 1) * Real.log n)
      ≤ Real.exp (β / (((n : ℝ) + 1) * Real.log n)) := fun n _ => by rw [add_comm]; exact Real.add_one_le_exp _
  refine le_trans (Finset.prod_le_prod hterm hle) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  have hdom : ∀ n ∈ Ico N₀ N, β / (((n : ℝ) + 1) * Real.log n) ≤ β * (1 / ((n : ℝ) * Real.log n)) := by
    intro n hn
    have h3n : 3 ≤ n := le_trans h3 (mem_Ico.1 hn).1
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast by lia
    have hlog : (0:ℝ) < Real.log n := Real.log_pos hn1
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlog, hn0]
  refine le_trans (Finset.sum_le_sum hdom) ?_
  rw [← Finset.mul_sum]
  have hpos : ∀ n ∈ Icc 3 N, (0:ℝ) ≤ 1 / ((n : ℝ) * Real.log n) := by
    intro n hn
    have h3n : 3 ≤ n := (mem_Icc.1 hn).1
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast by lia
    have := Real.log_pos hn1
    positivity
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (subset_Icc (N := N) h3) (fun n hn _ => hpos n hn)
  exact le_trans (mul_le_mul_of_nonneg_left hsub hβ)
    (mul_le_mul_of_nonneg_left (sum_one_div_mul_log_le hN) hβ)

/-- The inhomogeneous sum is `O(log log N)`. -/
lemma sum_d_bound {c : ℝ} (hc : 0 ≤ c) {N₀ N : ℕ} (h3 : 3 ≤ N₀) (hN : 3 ≤ N)
    (hlog : ∀ n : ℕ, N₀ ≤ n → 2 ≤ Real.log n) :
    ∑ n ∈ Ico N₀ N, c / (((n : ℝ) + 1) * (Real.log n - 1))
      ≤ 2 * c * (Real.log (Real.log N) - Real.log (Real.log 2)) := by
  have hdom : ∀ n ∈ Ico N₀ N, c / (((n : ℝ) + 1) * (Real.log n - 1))
      ≤ (2 * c) * (1 / ((n : ℝ) * Real.log n)) := by
    intro n hn
    have hn0' : N₀ ≤ n := (mem_Ico.1 hn).1
    have h3n : 3 ≤ n := le_trans h3 hn0'
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast by lia
    have hL2 : 2 ≤ Real.log n := hlog n hn0'
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    have hA : c * ((n:ℝ) * Real.log n) ≤ 2 * c * (((n:ℝ) + 1) * (Real.log n - 1)) := by
      have h1 : (n:ℝ) * Real.log n ≤ 2 * (((n:ℝ) + 1) * (Real.log n - 1)) := by
        nlinarith [hn0, hL2]
      nlinarith [hc, h1]
    linarith [hA]
  refine le_trans (Finset.sum_le_sum hdom) ?_
  rw [← Finset.mul_sum]
  have hpos : ∀ n ∈ Icc 3 N, (0:ℝ) ≤ 1 / ((n : ℝ) * Real.log n) := by
    intro n hn
    have h3n : 3 ≤ n := (mem_Icc.1 hn).1
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast by lia
    have := Real.log_pos hn1
    positivity
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (subset_Icc (N := N) h3) (fun n hn _ => hpos n hn)
  have h2c : (0:ℝ) ≤ 2 * c := by linarith
  exact le_trans (mul_le_mul_of_nonneg_left hsub h2c)
    (mul_le_mul_of_nonneg_left (sum_one_div_mul_log_le hN) h2c)

/-- `(A + B x) e^{-c x} → 0` for `c > 0`. -/
lemma tendsto_linear_mul_exp_neg {A B c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => (A + B * x) * Real.exp (-(c * x))) atTop (𝓝 0) := by
  have hlin : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have h1 : Tendsto (fun x : ℝ => Real.exp (-(c * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have h2 : Tendsto (fun x : ℝ => (c * x) * Real.exp (-(c * x))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
    simpa [Function.comp_def] using h
  have h3 := (h1.const_mul A).add (h2.const_mul (B / c))
  simp only [mul_zero, add_zero] at h3
  have heq : (fun x : ℝ => (A + B * x) * Real.exp (-(c * x)))
      = fun x : ℝ => A * Real.exp (-(c * x)) + (B / c) * ((c * x) * Real.exp (-(c * x))) := by
    funext x; field_simp
  rw [heq]; exact h3

/-- **L7.**  The recursion forces `σ N → 0`. -/
theorem recursion_tendsto_zero {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z.re < 1) (C : ℝ) (σ : ℕ → ℂ)
    (hσ : ∀ k, ‖σ k‖ ≤ 1)
    (hrec : ∀ N : ℕ, 2 ≤ N →
      ‖((Real.log N : ℂ) - z) * σ N - z * ∑ k ∈ Ico 1 N, σ k / ((k : ℂ) + 1)‖ ≤ C) :
    Tendsto σ atTop (𝓝 0) := by
  classical
  set Ψ : ℕ → ℂ := fun N => ∑ k ∈ Ico 1 N, σ k / ((k : ℂ) + 1) with hΨ
  set r : ℕ → ℝ := fun N => ‖Ψ N‖ with hr
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hrec 2 le_rfl)
  set β : ℝ := (max z.re 0 + 1) / 2 with hβdef
  have hmax1 : max z.re 0 < 1 := max_lt hz1 one_pos
  have hβ : max z.re 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ max z.re 0 := le_max_right _ _
    rw [hβdef]; linarith
  -- the threshold
  have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      (‖1 + z / (((n : ℂ) + 1) * ((Real.log n : ℂ) - z))‖
          ≤ 1 + β / (((n : ℝ) + 1) * Real.log n)) ∧ (2 ≤ Real.log n) ∧ 3 ≤ n :=
    (eventually_norm_one_add_le hz hβ).and
      ((hlogtop.eventually_ge_atTop 2).and (eventually_ge_atTop 3))
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hev
  set M : ℕ := max M₀ 3 with hMdef
  have hM3 : 3 ≤ M := le_max_right _ _
  have hMprop : ∀ n, M ≤ n → (‖1 + z / (((n : ℂ) + 1) * ((Real.log n : ℂ) - z))‖
      ≤ 1 + β / (((n : ℝ) + 1) * Real.log n)) ∧ (2 ≤ Real.log n) ∧ 3 ≤ n :=
    fun n hn => hM₀ n (le_trans (le_max_left _ _) hn)
  set q : ℕ → ℝ := fun n => 1 + β / (((n : ℝ) + 1) * Real.log n) with hq
  set d : ℕ → ℝ := fun n => C / (((n : ℝ) + 1) * (Real.log n - 1)) with hd
  -- basic positivity on the range
  have hpos : ∀ n, M ≤ n → (0:ℝ) < ((n : ℝ) + 1) ∧ 2 ≤ Real.log n := by
    intro n hn
    refine ⟨by positivity, (hMprop n hn).2.1⟩
  have hWne : ∀ n, M ≤ n → ((Real.log n : ℂ) - z) ≠ 0 ∧
      Real.log n - 1 ≤ ‖(Real.log n : ℂ) - z‖ := by
    intro n hn
    have h2 : (2:ℝ) ≤ Real.log n := (hpos n hn).2
    have hnorm : Real.log n - 1 ≤ ‖(Real.log n : ℂ) - z‖ := by
      have := norm_sub_norm_le ((Real.log n : ℂ)) z
      rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at this
      exact this
    refine ⟨?_, hnorm⟩
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  -- the one-step inequality
  have hstep : ∀ n, M ≤ n → r (n + 1) ≤ r n * q n + d n := by
    intro n hn
    obtain ⟨hWn, hWnorm⟩ := hWne n hn
    have h1n : 1 ≤ n := le_trans (by lia) (hMprop n hn).2.2
    have hn1C : ((n : ℂ) + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    set W : ℂ := (Real.log n : ℂ) - z with hW
    set E : ℂ := W * σ n - z * Ψ n with hE
    have hEC : ‖E‖ ≤ C := hrec n (le_trans (by lia) (hMprop n hn).2.2)
    have hsucc : Ψ (n + 1) = Ψ n * (1 + z / (((n : ℂ) + 1) * W)) + E / (((n : ℂ) + 1) * W) := by
      have hs : Ψ (n + 1) = Ψ n + σ n / ((n : ℂ) + 1) := by
        rw [hΨ]; simp only []
        rw [Finset.sum_Ico_succ_top h1n]
      rw [hs, hE]
      field_simp
      ring
    have hcastn : ‖((n : ℂ) + 1)‖ = ((n : ℝ) + 1) := by
      rw [show ((n:ℂ)+1) = ((((n:ℝ)+1) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2n : (2:ℝ) ≤ Real.log n := (hpos n hn).2
    have hb1 : ‖Ψ n * (1 + z / (((n : ℂ) + 1) * W))‖ ≤ r n * q n := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMprop n hn).1 (norm_nonneg _)
    have hb2 : ‖E / (((n : ℂ) + 1) * W)‖ ≤ d n := by
      rw [norm_div, norm_mul, hcastn, hd]
      simp only []
      refine div_le_div₀ hC hEC ?_ ?_
      · have h0 : (0:ℝ) < ((n:ℝ)+1) := by positivity
        have h1 : (0:ℝ) < Real.log n - 1 := by linarith
        positivity
      · have h0 : (0:ℝ) < ((n:ℝ)+1) := by positivity
        exact mul_le_mul_of_nonneg_left hWnorm h0.le
    have : r (n + 1) ≤ ‖Ψ n * (1 + z / (((n : ℂ) + 1) * W))‖ + ‖E / (((n : ℂ) + 1) * W)‖ := by
      rw [hr]; simp only []; rw [hsucc]; exact norm_add_le _ _
    linarith

  have hqge : ∀ n, M ≤ n → 1 ≤ q n := by
    intro n hn
    have h2 : (2:ℝ) ≤ Real.log n := (hpos n hn).2
    have : (0:ℝ) ≤ β / (((n : ℝ) + 1) * Real.log n) := by
      have : (0:ℝ) < ((n:ℝ)+1) * Real.log n := by
        have : (0:ℝ) < ((n:ℝ)+1) := by positivity
        nlinarith
      positivity
    rw [hq]; simp only []; linarith
  have hdge : ∀ n, M ≤ n → 0 ≤ d n := by
    intro n hn
    have h2 : (2:ℝ) ≤ Real.log n := (hpos n hn).2
    have hden : (0:ℝ) < ((n : ℝ) + 1) * (Real.log n - 1) := by
      have h0 : (0:ℝ) < ((n:ℝ)+1) := by positivity
      have h1 : (0:ℝ) < Real.log n - 1 := by linarith
      positivity
    rw [hd]; simp only []; positivity
  have hgron := gronwall hstep hqge hdge (norm_nonneg _)
  -- the limit
  set c₂ : ℝ := Real.log (Real.log 2) with hc₂
  set A : ℝ := r M with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  set G : ℝ → ℝ := fun y =>
      (2 * Real.exp (-c₂) * A + (2 * Real.exp (-c₂) * (2 * C)) * y) * Real.exp (-((1 - β) * y))
      + (2 * Real.exp (-c₂) * C + 0 * y) * Real.exp (-(1 * y)) with hG
  have hGtend : Tendsto G atTop (𝓝 0) := by
    have h1 := tendsto_linear_mul_exp_neg (A := 2 * Real.exp (-c₂) * A)
      (B := 2 * Real.exp (-c₂) * (2 * C)) (c := 1 - β) (by linarith)
    have h2 := tendsto_linear_mul_exp_neg (A := 2 * Real.exp (-c₂) * C) (B := 0) (c := 1)
      (by norm_num)
    have := h1.add h2
    simpa [hG] using this
  have hytop : Tendsto (fun N : ℕ => Real.log (Real.log N) - c₂) atTop atTop := by
    have : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
      Real.tendsto_log_atTop.comp hlogtop
    simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right atTop (-c₂) this
  refine squeeze_zero_norm' ?_ (hGtend.comp hytop)
  filter_upwards [eventually_ge_atTop M] with N hN
  obtain ⟨hWN, hWNnorm⟩ := hWne N hN
  have h2 : (2:ℝ) ≤ Real.log N := (hpos N hN).2
  have hN3 : 3 ≤ N := (hMprop N hN).2.2
  set x : ℝ := Real.log (Real.log N) with hx
  set y : ℝ := x - c₂ with hy
  -- bound on r N
  have hPb : ∏ n ∈ Ico M N, q n ≤ Real.exp (β * y) := by
    have := prod_bound (β := β) hβ0 (N₀ := M) (N := N) hM3 hN3
    simpa [hq, hx, hy, hc₂] using this
  have hDb : ∑ n ∈ Ico M N, d n ≤ 2 * C * y := by
    have := sum_d_bound (c := C) hC (N₀ := M) (N := N) hM3 hN3
      (fun n hn => (hpos n hn).2)
    simpa [hd, hx, hy, hc₂] using this
  have hD0 : 0 ≤ ∑ n ∈ Ico M N, d n :=
    Finset.sum_nonneg fun n hn => hdge n (mem_Ico.1 hn).1
  have hP0 : (0:ℝ) ≤ ∏ n ∈ Ico M N, q n :=
    le_trans zero_le_one (Finset.one_le_prod fun n hn => hqge n (mem_Ico.1 hn).1)
  have hy0 : 0 ≤ y := by
    have hcx : c₂ ≤ x := by
      rw [hx, hc₂]
      refine Real.log_le_log (Real.log_pos (by norm_num)) ?_
      refine Real.log_le_log (by norm_num) ?_
      exact_mod_cast le_trans (by norm_num) hN3
    rw [hy]; linarith
  have hrN : r N ≤ (A + 2 * C * y) * Real.exp (β * y) := by
    refine le_trans (hgron N hN) ?_
    refine mul_le_mul (by linarith) hPb hP0 ?_
    nlinarith [hA0, hC, hy0]
  -- bound on ‖σ N‖
  have hσN : ‖σ N‖ ≤ (r N + C) / (Real.log N - 1) := by
    have hWeq : σ N = (z * Ψ N + (((Real.log N : ℂ) - z) * σ N - z * Ψ N))
        / ((Real.log N : ℂ) - z) := by
      field_simp
      ring
    rw [hWeq, norm_div]
    have hnum : ‖z * Ψ N + (((Real.log N : ℂ) - z) * σ N - z * Ψ N)‖ ≤ r N + C := by
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖z * Ψ N‖ = r N := by rw [norm_mul, hz, one_mul]
      have h2 : ‖((Real.log N : ℂ) - z) * σ N - z * Ψ N‖ ≤ C := hrec N (by lia)
      linarith [h1.le, h1.ge]
    have hden : (0:ℝ) < Real.log N - 1 := by linarith
    exact div_le_div₀ (by positivity) hnum hden hWNnorm
  -- assemble
  have hexpx : Real.exp x = Real.log N := Real.exp_log (by linarith)
  have hlogN : Real.log N - 1 ≥ Real.exp c₂ * Real.exp y / 2 := by
    have : Real.exp c₂ * Real.exp y = Real.exp x := by
      rw [← Real.exp_add, hy]; ring_nf
    rw [this, hexpx]
    linarith
  have hfinal : (r N + C) / (Real.log N - 1) ≤ G y := by
    have hden : (0:ℝ) < Real.log N - 1 := by linarith
    have hnum0 : 0 ≤ r N + C := by positivity
    have hexpc : (0:ℝ) < Real.exp c₂ := Real.exp_pos _
    have hexpy : (0:ℝ) < Real.exp y := Real.exp_pos _
    have hstep1 : (r N + C) / (Real.log N - 1)
        ≤ (r N + C) / (Real.exp c₂ * Real.exp y / 2) := by
      apply div_le_div_of_nonneg_left hnum0 (by positivity) hlogN
    refine le_trans hstep1 ?_
    have hrw : (r N + C) / (Real.exp c₂ * Real.exp y / 2)
        = 2 * Real.exp (-c₂) * (r N + C) * Real.exp (-y) := by
      rw [Real.exp_neg, Real.exp_neg]
      field_simp
    rw [hrw, hG]
    simp only []
    have hkey : (r N + C) * Real.exp (-y)
        ≤ (A + 2 * C * y) * Real.exp (-((1 - β) * y)) + C * Real.exp (-(1 * y)) := by
      have e1 : (A + 2 * C * y) * Real.exp (β * y) * Real.exp (-y)
          = (A + 2 * C * y) * Real.exp (-((1 - β) * y)) := by
        rw [mul_assoc, ← Real.exp_add, show β * y + -y = -((1 - β) * y) by ring]
      calc (r N + C) * Real.exp (-y)
          ≤ ((A + 2 * C * y) * Real.exp (β * y) + C) * Real.exp (-y) := by
            have := Real.exp_pos (-y); nlinarith [hrN]
        _ = (A + 2 * C * y) * Real.exp (β * y) * Real.exp (-y) + C * Real.exp (-y) := by ring
        _ = (A + 2 * C * y) * Real.exp (-((1 - β) * y)) + C * Real.exp (-(1 * y)) := by
            rw [e1]; ring_nf
    have hpos2 : (0:ℝ) < 2 * Real.exp (-c₂) := by positivity
    nlinarith [hkey, hpos2, Real.exp_pos (-((1-β)*y)), Real.exp_pos (-(1*y))]
  exact le_trans hσN hfinal

end NormalNumbers.DelangeSlot
