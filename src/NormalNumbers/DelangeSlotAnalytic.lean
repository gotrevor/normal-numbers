import NormalNumbers.DelangeSlotIdentity
import PNTPort.MediumPNT

/-!
# Rung 1 of the Delange slot: the analytic chain

The plan of record (`DESIGN-2026-09-24-delange-route.md`), in seven steps.  Writing
`S N = ∑_{n≤N} h n`, `m N = ∑_{k≤N} h k / k`, `A N = ∑_{n≤N} h n log n`, `ψ x = ∑_{d≤x} Λ d`:

| step | statement | status |
|---|---|---|
| L1 | `A N = ∑_{d≤N} Λ d ∑_{m≤N/d} h (d m)` | proved (`sum_hfun_mul_log`) |
| L2 | `‖A N − z ∑_{d≤N} Λ d · S (N/d)‖ ≤ C_P · N` | open |
| L3 | `∑_{d≤N} Λ d · S (N/d) = ∑_{k≤N} h k · ψ (N/k)` | proved |
| L4 | `‖∑_{k≤N} h k ψ(N/k) − N · m N‖ ≤ C · N` | open (consumes `MediumPNT`) |
| L5 | `‖A N − S N · log N‖ ≤ N` | proved |
| L6 | `m N = σ N + ∑_{k<N} σ k / (k+1)`, `σ k = S k / k` | open (discrete Abel) |
| L7 | the recursion `(log N − z) σ N = z Ψ N + O(1)` forces `σ N → 0` | open |

L2+L3+L4+L5 give `S N · log N = z · N · m N + O_P(N)`; L6 turns that into a closed complex
linear recursion in `σ`, and L7 solves it with the integrating factor `∏(1 + z/(n log n))`,
whose modulus is `(log N)^{Re z}`.  `Re z < 1` is exactly what makes `σ N → 0`.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

/-- `ψ x = ∑_{d ≤ x} Λ d`, as a function of a natural cutoff. -/
noncomputable def psiN (x : ℕ) : ℝ := ∑ d ∈ Ioc 0 x, Λ d

/-- `m N = ∑_{k ≤ N} h k / k`. -/
noncomputable def mSum (z : ℂ) (P N : ℕ) : ℂ := ∑ k ∈ Ioc 0 N, hfun z P k / k

/-- `σ k = S k / k`, the normalised mean; `‖σ k‖ ≤ 1`. -/
noncomputable def sigmaMean (z : ℂ) (P k : ℕ) : ℂ := Ssum z P k / k

lemma norm_sigmaMean_le {z : ℂ} (hz : ‖z‖ = 1) (P k : ℕ) : ‖sigmaMean z P k‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [sigmaMean]
  · rw [sigmaMean, norm_div, Complex.norm_natCast, div_le_one (by positivity)]
    exact norm_Ssum_le hz P k

/-- Symmetry of the hyperbolic region `d·m ≤ N`. -/
theorem sum_div_comm {R : Type*} [AddCommMonoid R] (F : ℕ → ℕ → R) (N : ℕ) :
    ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), F d m
      = ∑ m ∈ Ioc 0 N, ∑ d ∈ Ioc 0 (N / m), F d m := by
  classical
  rw [← sum_divisorAntidiagonal_swap F N, ← sum_divisorAntidiagonal_swap (fun a b => F b a) N]
  refine sum_congr rfl fun n _ ↦ ?_
  conv_rhs => rw [← Nat.map_swap_divisorsAntidiagonal]
  rw [Finset.sum_map]
  rfl

/-- **L3.**  Transposing the hyperbola onto the `ψ`-side. -/
theorem sum_Lambda_mul_Ssum (z : ℂ) (P N : ℕ) :
    ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * Ssum z P (N / d)
      = ∑ k ∈ Ioc 0 N, hfun z P k * (psiN (N / k) : ℂ) := by
  classical
  have l : ∀ d ∈ Ioc 0 N, (Λ d : ℂ) * Ssum z P (N / d)
      = ∑ m ∈ Ioc 0 (N / d), (Λ d : ℂ) * hfun z P m := by
    intro d _; rw [Ssum, Finset.mul_sum]
  have r : ∀ k ∈ Ioc 0 N, hfun z P k * (psiN (N / k) : ℂ)
      = ∑ d ∈ Ioc 0 (N / k), (Λ d : ℂ) * hfun z P k := by
    intro k _
    rw [psiN, Complex.ofReal_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ ↦ mul_comm _ _
  rw [sum_congr rfl l, sum_congr rfl r]
  exact sum_div_comm (fun d m => (Λ d : ℂ) * hfun z P m) N

/-- `∑_{n ≤ N} log (N/n) ≤ N`, by the telescoping `log(N/n) = ∑_{j=n}^{N-1} log(1+1/j)`. -/
lemma sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n = Real.log (Nat.factorial N : ℝ) := by
  rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod, Real.log_prod]
  · rw [show Ioc 0 N = Ico 1 (N+1) by ext i; simp [Nat.lt_succ_iff, Nat.succ_le_iff]]
  · intro i hi
    have : 0 < i := (mem_Ico.1 hi).1
    positivity

lemma sum_log_div_le (N : ℕ) : ∑ n ∈ Ioc 0 N, Real.log (N / n : ℝ) ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hfac : (0:ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast N.factorial_pos
  have key : (N:ℝ) ^ N / (Nat.factorial N : ℝ) ≤ Real.exp N :=
    Real.pow_div_factorial_le_exp (x := (N:ℝ)) hN0.le N
  have hlog : Real.log ((N:ℝ) ^ N / (Nat.factorial N : ℝ)) ≤ N := by
    have := Real.log_le_log (by positivity) key
    simpa [Real.log_exp] using this
  have hterm : ∀ n ∈ Ioc 0 N, Real.log (N / n : ℝ) = Real.log N - Real.log n := by
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    rw [Real.log_div hN0.ne' hn0.ne']
  have hsplit : ∑ n ∈ Ioc 0 N, Real.log (N / n : ℝ)
      = (N:ℝ) * Real.log N - Real.log (Nat.factorial N : ℝ) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_log_eq_log_factorial]
    simp [Nat.card_Ioc]
  rw [hsplit]
  calc (N:ℝ) * Real.log N - Real.log (Nat.factorial N : ℝ)
      = Real.log ((N:ℝ) ^ N / (Nat.factorial N : ℝ)) := by
        rw [Real.log_div (by positivity) hfac.ne', Real.log_pow]
    _ ≤ N := hlog

/-- **L5.**  The `log n` weight versus the flat weight. -/
theorem norm_sum_hfun_mul_log_sub {z : ℂ} (hz : ‖z‖ = 1) (P N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, hfun z P n * (Real.log n : ℂ)) - Ssum z P N * (Real.log N : ℂ)‖ ≤ N := by
  have hrw : (∑ n ∈ Ioc 0 N, hfun z P n * (Real.log n : ℂ)) - Ssum z P N * (Real.log N : ℂ)
      = ∑ n ∈ Ioc 0 N, hfun z P n * ((Real.log n : ℂ) - (Real.log N : ℂ)) := by
    rw [Ssum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  rw [hrw]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun n hn ↦ ?_)) (sum_log_div_le N)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
  have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Ioc.1 hn).2
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le hn0 hnN
  rw [norm_mul, norm_hfun_le hz, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.log_div hN0.ne' hn0.ne', Real.norm_eq_abs, abs_sub_comm]
  exact le_of_eq (abs_of_nonneg (by
    have : Real.log n ≤ Real.log N := Real.log_le_log hn0 hnN
    linarith))

/-- **L2.**  Replacing the inner sum by `z · S (N/d)`; the constant depends on `P`. -/
theorem exists_L2 (z : ℂ) (hz : ‖z‖ = 1) (P : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖(∑ n ∈ Ioc 0 N, hfun z P n * (Real.log n : ℂ))
        - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * Ssum z P (N / d)‖ ≤ C * N := by
  sorry

/-- **L4.**  `ψ (N/k) = N/k + Δ(N/k)` summed against `h`; consumes `PNTPort.MediumPNT` through
`∑_{k ≤ N} |Δ(N/k)| = O(N)`. -/
theorem exists_L4 (z : ℂ) (hz : ‖z‖ = 1) (P : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖(∑ k ∈ Ioc 0 N, hfun z P k * (psiN (N / k) : ℂ)) - (N : ℂ) * mSum z P N‖ ≤ C * N := by
  sorry

/-- **L6.**  Discrete Abel summation for `m N`. -/
lemma Ssum_succ (z : ℂ) (P N : ℕ) : Ssum z P (N + 1) = Ssum z P N + hfun z P (N + 1) := by
  simp [Ssum, Finset.sum_Ioc_succ_top (Nat.zero_le _)]

theorem mSum_eq (z : ℂ) (P N : ℕ) :
    mSum z P N = sigmaMean z P N + ∑ k ∈ Ico 1 N, sigmaMean z P k / (k + 1 : ℂ) := by
  induction N with
  | zero => simp [mSum, sigmaMean, Ssum]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [mSum, sigmaMean, Ssum, Finset.sum_Ioc_succ_top]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hN1 : ((N : ℂ) + 1) ≠ 0 := by
      have : ((N : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast fun h => this (by exact_mod_cast h)
    have hm : mSum z P (N + 1) = mSum z P N + hfun z P (N + 1) / ((N : ℂ) + 1) := by
      simp [mSum, Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hIco : ∑ k ∈ Ico 1 (N + 1), sigmaMean z P k / (k + 1 : ℂ)
        = (∑ k ∈ Ico 1 N, sigmaMean z P k / (k + 1 : ℂ)) + sigmaMean z P N / ((N : ℂ) + 1) := by
      rw [Finset.sum_Ico_succ_top hN]
    rw [hm, ih, hIco]
    simp only [sigmaMean, Ssum_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- **L7.**  The closed recursion forces decay.  This is the only step where `z ≠ 1` is used:
the integrating factor `∏_{n ≤ N} (1 + z / (n log n))` has modulus `≍ (log N)^{Re z}` and
`Re z < 1`. -/
theorem sigmaMean_tendsto_zero_of_recursion {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ)
    (C : ℝ) (hrec : ∀ N : ℕ, 2 ≤ N →
      ‖((Real.log N : ℂ) - z) * sigmaMean z P N
        - z * ∑ k ∈ Ico 1 N, sigmaMean z P k / (k + 1 : ℂ)‖ ≤ C) :
    Tendsto (fun N : ℕ => sigmaMean z P N) atTop (𝓝 0) := by
  sorry

end NormalNumbers.DelangeSlot
