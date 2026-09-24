/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Lambert2

/-!
# The obstruction budget, machine-checked

Every heuristic in this swing has priced the discarded tail by "the `p`-term has mean
`1/((b−1)p)` over its period, so cutting at `K` discards mean mass `≍ ∑_{p>K} 1/p`".  That
pricing has been the load-bearing claim of four handoffs; this file proves it.

The tool is `sum_range_le_of_periodic_nonneg`: for a nonnegative `L`-periodic `f`,

    ∑_{n<N} f(n)  ≤  (N/L + 1) · ∑_{m<L} f(m).

Applied to the closed-form term `b^{n mod p}/(b^p − 1)`, whose complete sum over its period is
**exactly** `1/(b−1)` (a geometric sum — `sum_range_tailPrimeTerm_period`), this gives

    (1/N) ∑_{n<N} b^{n mod p}/(b^p − 1)  ≤  (1/p + 1/N)/(b−1).

Summing over `K < p ≤ K'` turns the heuristic `loglog` obstruction into a proved inequality, and
so pins the exact budget that any attack on the window `log N ≪ K ≪ N` must beat.
-/

open Finset

namespace NormalNumbers

/-- Adding one full period to the range adds the complete-period sum. -/
theorem sum_range_add_period' {M : Type*} [AddCommGroup M] {L : ℕ} (g : ℕ → M)
    (hg : ∀ n, g (n + L) = g n) (N : ℕ) :
    ∑ n ∈ range (N + L), g n = (∑ n ∈ range N, g n) + ∑ m ∈ range L, g m := by
  rw [Finset.sum_range_add, sum_range_periodic_shift g hg N]

/-- **The periodic decomposition of a partial sum.** -/
theorem sum_range_eq_mod_add_nsmul {M : Type*} [AddCommGroup M] {L : ℕ} (hL : 0 < L)
    (g : ℕ → M) (hg : ∀ n, g (n + L) = g n) (N : ℕ) :
    ∑ n ∈ range N, g n = (∑ n ∈ range (N % L), g n) + (N / L) • (∑ m ∈ range L, g m) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hNL : N < L
    · rw [Nat.mod_eq_of_lt hNL, Nat.div_eq_of_lt hNL]
      simp
    · have hsub : N - L + L = N := by omega
      have hrec := ih (N - L) (by omega)
      have hmod : (N - L) % L = N % L := by
        conv_rhs => rw [← hsub]
        rw [Nat.add_mod_right]
      have hdiv : N / L = (N - L) / L + 1 := by
        conv_lhs => rw [← hsub]
        rw [Nat.add_div_right _ hL]
      calc ∑ n ∈ range N, g n = ∑ n ∈ range ((N - L) + L), g n := by rw [hsub]
        _ = (∑ n ∈ range (N - L), g n) + ∑ m ∈ range L, g m :=
            sum_range_add_period' g hg _
        _ = ((∑ n ∈ range ((N - L) % L), g n)
              + ((N - L) / L) • (∑ m ∈ range L, g m)) + ∑ m ∈ range L, g m := by rw [hrec]
        _ = (∑ n ∈ range (N % L), g n) + (N / L) • (∑ m ∈ range L, g m) := by
            rw [hmod, hdiv, succ_nsmul]
            abel

/-- **The periodic mean-value bound.**  For a nonnegative `L`-periodic `f`,
`∑_{n<N} f(n) ≤ (N/L + 1)·∑_{m<L} f(m)`. -/
theorem sum_range_le_of_periodic_nonneg {L : ℕ} (hL : 0 < L) (f : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hf : ∀ n, f (n + L) = f n) (N : ℕ) :
    ∑ n ∈ range N, f n ≤ ((N : ℝ) / L + 1) * ∑ m ∈ range L, f m := by
  have hC0 : 0 ≤ ∑ m ∈ range L, f m := Finset.sum_nonneg fun m _ => hf0 m
  rw [sum_range_eq_mod_add_nsmul hL f hf N, nsmul_eq_mul]
  have hmodle : N % L ≤ L := (Nat.mod_lt _ hL).le
  have hsubset : range (N % L) ⊆ range L := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hstub : ∑ n ∈ range (N % L), f n ≤ ∑ m ∈ range L, f m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => hf0 m)
  have hq : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / L := by
    rw [le_div_iff₀ (by exact_mod_cast hL)]
    exact_mod_cast Nat.div_mul_le_self N L
  calc (∑ n ∈ range (N % L), f n) + ((N / L : ℕ) : ℝ) * ∑ m ∈ range L, f m
      ≤ (∑ m ∈ range L, f m) + ((N : ℝ) / L) * ∑ m ∈ range L, f m := by gcongr
    _ = ((N : ℝ) / L + 1) * ∑ m ∈ range L, f m := by ring

/-! ### The exact complete-period sum of a closed-form term -/

/-- **The complete-period sum of the `p`-term is exactly `1/(b−1)`.** -/
theorem sum_range_tailPrimeTerm_period {b : ℕ} (hb : 2 ≤ b) {p : ℕ} (hp : 0 < p) :
    ∑ m ∈ range p, tailPrimeTerm b p m = 1 / ((b : ℝ) - 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (b : ℝ) - 1 ≠ 0 := by intro hc; linarith [sub_eq_zero.1 hc]
  have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
  have hden : ((b : ℝ) ^ p - 1) ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
  have hval : ∀ m ∈ range p, tailPrimeTerm b p m = (b : ℝ) ^ m / ((b : ℝ) ^ p - 1) := by
    intro m hm
    rw [tailPrimeTerm, Nat.mod_eq_of_lt (Finset.mem_range.1 hm)]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_div, geom_sum_eq (by intro hc; linarith) p]
  field_simp

/-- **The proved pricing.**  The partial mean of the `p`-term is at most `(1/p + 1/N)/(b−1)`. -/
theorem sum_range_tailPrimeTerm_le {b : ℕ} (hb : 2 ≤ b) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ∑ n ∈ range N, tailPrimeTerm b p n ≤ ((N : ℝ) / p + 1) * (1 / ((b : ℝ) - 1)) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h := sum_range_le_of_periodic_nonneg hp (fun n => tailPrimeTerm b p n)
    (fun n => by
      have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
      rw [tailPrimeTerm]; positivity)
    (fun n => tailPrimeTerm_congr (Nat.add_modEq_right)) N
  rwa [sum_range_tailPrimeTerm_period hb hp] at h

/-- **The window budget.**  Cutting the closed form between `K` and `K'` discards, on average
over `n < N`, at most `∑_{K<p≤K'} (1/p + 1/N)/(b−1)`.  This is the `loglog` obstruction, proved:
any attack on the window `log N ≪ K ≪ N` must beat exactly this quantity. -/
theorem sum_range_tailTrunc_sub_le {b : ℕ} (hb : 2 ≤ b) (P K K' N : ℕ) :
    ∑ n ∈ range N, (tailTrunc b P K' n - tailTrunc b P K n)
      ≤ ∑ p ∈ (Finset.Ioc K K').filter Nat.Prime, ((N : ℝ) / p + 1) * (1 / ((b : ℝ) - 1)) := by
  classical
  have hkey : ∀ n, tailTrunc b P K' n - tailTrunc b P K n
      ≤ ∑ p ∈ (Finset.Ioc K K').filter Nat.Prime, tailPrimeTerm b p n := by
    intro n
    have hnn : ∀ p : ℕ, 0 < p → 0 ≤ tailPrimeTerm b p n := by
      intro p hp
      have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
      rw [tailPrimeTerm]; positivity
    have hsplit : ∑ p ∈ (Finset.Ioc P K').filter Nat.Prime, tailPrimeTerm b p n
        ≤ (∑ p ∈ (Finset.Ioc P K).filter Nat.Prime, tailPrimeTerm b p n)
          + ∑ p ∈ (Finset.Ioc K K').filter Nat.Prime, tailPrimeTerm b p n := by
      rw [← Finset.sum_union]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => hnn p ?_)
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union] at hp ⊢
          rcases Nat.lt_or_ge K p with hpk | hpk
          · exact Or.inr ⟨⟨hpk, hp.1.2⟩, hp.2⟩
          · exact Or.inl ⟨⟨hp.1.1, hpk⟩, hp.2⟩
        · simp only [Finset.mem_union, Finset.mem_filter] at hp
          rcases hp with hp | hp <;> exact hp.2.pos
      · rw [Finset.disjoint_left]
        intro p hp hq
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp hq
        omega
    simp only [tailTrunc]
    linarith [hsplit]
  calc ∑ n ∈ range N, (tailTrunc b P K' n - tailTrunc b P K n)
      ≤ ∑ n ∈ range N, ∑ p ∈ (Finset.Ioc K K').filter Nat.Prime, tailPrimeTerm b p n :=
        Finset.sum_le_sum fun n _ => hkey n
    _ = ∑ p ∈ (Finset.Ioc K K').filter Nat.Prime, ∑ n ∈ range N, tailPrimeTerm b p n :=
        Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun p hp =>
        sum_range_tailPrimeTerm_le hb (Finset.mem_filter.1 hp).2.pos N

/-! ### The master inequality: the whole crux as two competing explicit terms -/

/-- `e(·)` is Lipschitz: `‖e(x) − e(y)‖ ≤ 16|x − y|`. -/
theorem norm_ee_sub_ee_le (x y : ℝ) : ‖ee (x : ℂ) - ee (y : ℂ)‖ ≤ 16 * |x - y| := by
  have hd : ee (x : ℂ) - ee (y : ℂ) = ee (y : ℂ) * (ee (((x - y : ℝ)) : ℂ) - 1) := by
    rw [mul_sub, mul_one, ← ee_add]
    congr 2
    push_cast
    ring
  have hz : ‖(2 * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ))‖ = 2 * Real.pi * |x - y| := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ))
        = ((2 * Real.pi * (x - y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rcases le_or_gt |x - y| (1/8 : ℝ) with hcase | hcase
  · have h1 : ‖(2 * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ))‖ ≤ 1 := by
      rw [hz]
      nlinarith [Real.pi_le_four, abs_nonneg (x - y)]
    have h2 := Complex.norm_exp_sub_one_le h1
    rw [hd, norm_mul, norm_ee_real]
    rw [one_mul, ee]
    calc ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ)) - 1‖
        ≤ 2 * ‖(2 * (Real.pi : ℂ) * Complex.I * ((x - y : ℝ) : ℂ))‖ := h2
      _ = 4 * Real.pi * |x - y| := by rw [hz]; ring
      _ ≤ 16 * |x - y| := by nlinarith [Real.pi_le_four, abs_nonneg (x - y)]
  · calc ‖ee (x : ℂ) - ee (y : ℂ)‖ ≤ ‖ee (x : ℂ)‖ + ‖ee (y : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_ee_real, norm_ee_real]; norm_num
      _ ≤ 16 * |x - y| := by linarith

/-- The truncation defect is nonnegative. -/
theorem tailLarge_sub_tailTrunc_nonneg {b : ℕ} (hb : 2 ≤ b) (P K n : ℕ) :
    0 ≤ tailLarge P b n - tailTrunc b P K n := by
  have h := (tailLarge_sub_truncate_mem_Icc hb P n K).1
  rwa [sum_tailPrimeSummand_range b P n K, ← tailTrunc] at h

/-- **THE MASTER INEQUALITY.**  For every truncation level `K`, the crux's twisted sum is
controlled by exactly two competing terms: the PERIOD `∏_{P<p≤K} p · Q` (which the complete-sum
cancellation pays for, and which must be `≪ N`), and the DISCARDED MASS
`∑_{n<N}(tailLarge − tailTrunc_K)(n)` (priced by `sum_range_tailTrunc_sub_le` at
`≍ N·∑_{p>K} 1/p`, and which must be `≪ N`).  `ConjC3` is the assertion that some `K = K(N)`
makes both small; laps 7–10 show the first forces `K ≲ log N` and the second `K ≳ N`. -/
theorem norm_sum_addChar_tailLarge_le {b P K Q j : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (hQP : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ P) (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) (N : ℕ) :
    ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)‖
      ≤ ((primePeriod P K * Q : ℕ) : ℝ)
        + 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailTrunc b P K n) := by
  classical
  set A : ℂ := ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
    * ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ) with hA
  have hsplit : ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
      * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
      = A + ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
          - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)) := by
    rw [hA, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hAbd := norm_sum_addChar_tailTrunc_le (b := b) (K := K) hQ hQP hj0 hjQ h N
  have hDbd : ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
      * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
        - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ))‖
      ≤ 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailTrunc b P K n) := by
    calc ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
          - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ))‖
        ≤ ∑ n ∈ range N, ‖ee (((j : ℝ) * n / Q : ℝ) : ℂ)
            * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
              - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, 16 * |(h : ℝ)| * (tailLarge P b n - tailTrunc b P K n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_ee_real, one_mul]
          refine le_trans (norm_ee_sub_ee_le _ _) ?_
          have hnn := tailLarge_sub_tailTrunc_nonneg hb P K n
          have habs : |(h : ℝ) * tailLarge P b n - (h : ℝ) * tailTrunc b P K n|
              = |(h : ℝ)| * (tailLarge P b n - tailTrunc b P K n) := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
          rw [habs]
          ring_nf
          exact le_rfl
      _ = 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailTrunc b P K n) := by
          rw [← Finset.mul_sum]
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (by linarith)

end NormalNumbers
