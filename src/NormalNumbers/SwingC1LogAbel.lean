import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries

/-!
# Partial summation: natural density implies logarithmic density

A Toeplitz/weighted-average lemma plus the Abel identity

    Σ_{n<N} a_n/(n+1) = A(N)/N + Σ_{1 ≤ n < N} A(n)/(n(n+1)),   A(n) = Σ_{k<n} a_k,

which together give `tendsto_logAvg_of_tendsto_avg`: if the Cesàro averages of `a` converge, so do
the logarithmic averages, to the same limit.
-/

open Finset Filter Topology Asymptotics

namespace NormalNumbers.CastingOut

/-- **Toeplitz / weighted average.**  Nonnegative weights with divergent partial sums average a
convergent sequence to its limit. -/
theorem tendsto_weighted_avg {w u : ℕ → ℝ} {c : ℝ} (hw : ∀ n, 0 ≤ w n)
    (hW : Tendsto (fun N => ∑ n ∈ range N, w n) atTop atTop)
    (hu : Tendsto u atTop (𝓝 c)) :
    Tendsto (fun N => (∑ n ∈ range N, w n * u n) / (∑ n ∈ range N, w n)) atTop (𝓝 c) := by
  have hlo : (fun n => w n * (u n - c)) =o[atTop] w := by
    refine isLittleO_iff.mpr fun ε hε => ?_
    have hu' : Tendsto (fun n => u n - c) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hu
    filter_upwards [(Metric.tendsto_nhds.mp hu') ε hε] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n), Real.norm_eq_abs, abs_of_nonneg (hw n)]
    have hb : |u n - c| ≤ ε := by
      have := hn
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    rw [mul_comm ε (w n)]
    exact mul_le_mul_of_nonneg_left hb (hw n)
  have hsum := hlo.sum_range hw hW
  have hdiv := hsum.tendsto_div_nhds_zero
  have hrw : ∀ N : ℕ, (∑ n ∈ range N, w n * (u n - c)) / (∑ n ∈ range N, w n)
      = (∑ n ∈ range N, w n * u n) / (∑ n ∈ range N, w n) - c * (∑ n ∈ range N, w n)
        / (∑ n ∈ range N, w n) := by
    intro N
    rw [← sub_div]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp only [hrw] at hdiv
  have hne : ∀ᶠ N in atTop, (∑ n ∈ range N, w n) ≠ 0 := by
    filter_upwards [hW.eventually_gt_atTop 0] with N hN
    exact ne_of_gt hN
  have hone : Tendsto (fun N => c * (∑ n ∈ range N, w n) / (∑ n ∈ range N, w n)) atTop (𝓝 c) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := c))
    filter_upwards [hne] with N hN
    rw [mul_div_assoc, div_self hN, mul_one]
  have := hdiv.add hone
  simpa using this

/-- **Abel summation** in the form needed for logarithmic averaging. -/
theorem sum_div_succ_abel (a : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, a n / (n + 1)
      = (∑ n ∈ range N, a n) / N
        + ∑ n ∈ range N, (1 / ((n : ℝ) + 1)) * ((∑ k ∈ range n, a k) / n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := fun n =>
      (1 / ((n : ℝ) + 1)) * ((∑ k ∈ range n, a k) / n)), Finset.sum_range_succ (f := a)]
    push_cast
    field_simp
    ring

/-- **Natural density implies logarithmic density.** -/
theorem tendsto_logAvg_of_tendsto_avg (a : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun N => (∑ n ∈ range N, a n) / N) atTop (𝓝 c)) :
    Tendsto (fun N => (∑ n ∈ range N, a n / (n + 1)) / ∑ n ∈ range N, (1 : ℝ) / (n + 1))
      atTop (𝓝 c) := by
  set w : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hwdef
  set u : ℕ → ℝ := fun n => (∑ k ∈ range n, a k) / n with hudef
  have hw : ∀ n, 0 ≤ w n := fun n => by positivity
  have hW : Tendsto (fun N => ∑ n ∈ range N, w n) atTop atTop := by
    simpa [hwdef] using Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hmain := tendsto_weighted_avg hw hW h
  have hhead : Tendsto (fun N => ((∑ n ∈ range N, a n) / N) / ∑ n ∈ range N, w n)
      atTop (𝓝 0) := by
    have := h.div_atTop hW
    simpa using this
  have := hhead.add hmain
  rw [zero_add] at this
  refine this.congr fun N => ?_
  rw [sum_div_succ_abel a N, add_div]

end NormalNumbers.CastingOut
