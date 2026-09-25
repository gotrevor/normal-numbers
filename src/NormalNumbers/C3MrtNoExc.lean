/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtExcScales
import NormalNumbers.C3MrtNatural

/-!
# Pinning the `D ≥ 2` route to a named open problem: remove `E` from TT Theorem 3.1

Lap 62 stated Tao–Teräväinen Theorem 3.1(ii) faithfully; lap 63 proved that a density-zero set
of exceptional scales genuinely blocks the `Tendsto` that `LogToNaturalCorrelation K` demands.
This file closes the loop from the other side.

* `exceptional_set_can_pin_a_scale` — the black box is *consistent with* a fixed scale being
  exceptional at **every** `X`: the singleton `{N}` is a legitimate exceptional set at every
  `X`, since it has logarithmic measure `0`.  So the "vary `X` for fixed `N`" rescue cannot be
  run inside the statement, whatever a proof of Theorem 3.1 might secretly give.  (Lap 63's
  Fubini analysis is the quantitative version of the same fact.)
* `TwoPointNaturalCorrelationNoExc` — Theorem 3.1(ii) with `E = ∅`: the *named open problem*.
  TT, `papers/tao-teravainen-2025-quantitative-correlations.txt:2997`: removing the exceptional
  set is not within current technology.
* `twoPointNatural_of_noExc` — the strengthening really is a strengthening.
* **`logToNatural_two_of_noExc`** — the payoff being built: `NoExc → LogToNaturalCorrelation 2`.
  With this, the `D = 2` layer of `ConjC3` is *equivalent to* (implied by) removing the
  exceptional set from a published theorem, and nothing else is missing at `K = 2`.

## The decomposition of `logToNatural_two_of_noExc` (the open sub-goals, disclosed)

Write `F n = z₀^{ω(n+1)} z₁^{ω(n+2)}` and let `S J = ∑_{m<J} F(M m + r)`.

1. `dyadic_window_bound_of_noExc` — for each dyadic scale `N`, taking `X = N²` and
   `L = log X = 2 log N` (so `N = √X` is admissible and `L ≤ log X` holds with equality),
   `|∑_{N<n≤2N, n≡r (M)} F n| ≤ Cst L^{-c} · N / M`.
2. `dyadic_decomposition` — `[0, M·J) ∩ (r mod M)` is the disjoint union of the dyadic windows
   `(2^i, 2^{i+1}]` for `i < ⌈log₂(MJ)⌉`, plus the head `{0}`.
3. `dyadic_sum_geometric` — `∑_{i<I} 2^i (log 2^i)^{-c} ≪ 2^I (I log 2)^{-c}`: the geometric
   weight concentrates the sum on the top window, so the `L^{-c}` saving survives the sum with
   only a constant loss.  This is the only genuinely quantitative step.
4. Divide by `J` and let `J → ∞`.

Steps 1, 2, 4 are bookkeeping; step 3 is a real (but elementary) estimate.  All four are
`sorry`-disclosed below, in `src/`, as named goals — that is the point of the decomposition.
-/

open Filter Finset Topology MeasureTheory

namespace NormalNumbers

namespace CastingOut

/-- **The black box cannot be pushed.**  A single prescribed scale `N` may legitimately lie in
the exceptional set at *every* `X`: `{N}` is measurable, sits inside `[√X, X]` whenever
`√X ≤ N ≤ X`, and has logarithmic measure `0`.  Hence no argument that only uses the
*statement* of Theorem 3.1 — varying `X`, intersecting over `X`, Fubini — can produce a bound
at a prescribed scale. -/
theorem exceptional_set_can_pin_a_scale (N : ℝ) (hN : 0 < N) :
    ∃ E : Set ℝ, MeasurableSet E ∧ N ∈ E ∧ (∫ t in E, t⁻¹) = 0 ∧
      ∀ X : ℝ, Real.sqrt X ≤ N → N ≤ X → E ⊆ Set.Icc (Real.sqrt X) X := by
  refine ⟨{N}, measurableSet_singleton N, rfl, ?_, fun X h1 h2 => ?_⟩
  · rw [MeasureTheory.Measure.restrict_singleton]
    simp
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨h1, h2⟩

/-- **The named open problem.**  Tao–Teräväinen Theorem 3.1(ii) with the exceptional set of
scales removed.  TT state in print that this is out of reach of current technology. -/
def TwoPointNaturalCorrelationNoExc : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
        TTNonPretentious g₁ X L →
          ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X →
            ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
              (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
              ‖((W : ℝ) / (N : ℝ) : ℝ) •
                  ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                    g₁ (n + h₁) * g₂ (n + h₂)‖
                ≤ Cst * L ^ (-c)

/-- The exceptional-set-free version is genuinely stronger: take `E = ∅`. -/
theorem twoPointNatural_of_noExc (h : TwoPointNaturalCorrelationNoExc) :
    TwoPointNaturalCorrelation := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := h
  refine ⟨c, Cst, hc, hCst, fun g₁ g₂ hm₁ hm₂ hb₁ hb₂ X L hX hL1 hLX hnp => ?_⟩
  refine ⟨∅, MeasurableSet.empty, Set.empty_subset _, ?_,
    fun N hN1 hN2 _ => hmain g₁ g₂ hm₁ hm₂ hb₁ hb₂ X L hX hL1 hLX hnp N hN1 hN2⟩
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have : (∫ t in (∅ : Set ℝ), t⁻¹) = 0 := by simp
  rw [this]
  positivity

/-! ## The payoff, decomposed

The four named sub-goals of `logToNatural_two_of_noExc`.  Each is disclosed as a `sorry` in
`src/`, deliberately: this is the crux of the `D = 2` layer broken into pieces, not hidden. -/

/-- **Sub-goal 1 (bookkeeping), PROVED.**  A single dyadic window, at `X = N²`, `L = 2 log N`.
`N = √X` is the left endpoint of the admissible range, and `L = log X`. -/
theorem dyadic_window_bound_of_noExc (h : TwoPointNaturalCorrelationNoExc)
    {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    (hnp : ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      TTNonPretentious (zOmegaNat z₀) X L) :
    ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ M r : ℕ, 0 < M → (M : ℝ) ≤ (2 * Real.log N) ^ c →
        ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
            z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2)‖
          ≤ Cst * (2 * Real.log N) ^ (-c) * (N : ℝ) / (M : ℝ) := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := h
  -- `L = 2 log N → ∞`, so `L^c ≥ 2` eventually: that is all `N₀` is for.
  have hLtend : Tendsto (fun N : ℕ => (2 * Real.log N) ^ c) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => 2 * Real.log N) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    exact (tendsto_rpow_atTop hc).comp h1
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hLtend.eventually_ge_atTop 2)
  refine ⟨c, Cst, hc, hCst, max N₁ 2, fun N hN M r hM hML => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNl : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have h2L : (2 : ℝ) ≤ (2 * Real.log N) ^ c := hN₁ N hNl
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set X : ℝ := (N : ℝ) ^ 2 with hX
  have hlogX : Real.log X = 2 * Real.log N := by rw [hX, Real.log_pow]; push_cast; ring
  have hX2 : 2 ≤ X := by rw [hX]; nlinarith
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL1 : (1 : ℝ) ≤ 2 * Real.log N := by linarith
  have hsqrt : Real.sqrt X = (N : ℝ) := by
    rw [hX, Real.sqrt_sq hNpos.le]
  have hNX : (N : ℝ) ≤ X := by rw [hX]; nlinarith
  have hspec := hmain (zOmegaNat z₀) (zOmegaNat z₁)
    (isCoprimeMultiplicativeNat_zOmegaNat z₀) (isCoprimeMultiplicativeNat_zOmegaNat z₁)
    (norm_zOmegaNat_le_one hz₀) (norm_zOmegaNat_le_one hz₁) X (2 * Real.log N)
    hX2 hL1 (le_of_eq hlogX.symm) (hnp X (2 * Real.log N) hX2 hL1 (le_of_eq hlogX.symm))
    N (by rw [hsqrt]) hNX M r 1 2 hM hML
    (by simpa using le_trans (by norm_num) h2L) (by simpa using h2L) (by norm_num)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hspec
  set S : ℂ := ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      zOmegaNat z₀ (n + 1) * zOmegaNat z₁ (n + 2) with hS
  have hSrw : (∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2)) = S := by
    rw [hS]; exact Finset.sum_congr rfl fun n _ => by simp [zOmegaNat]
  rw [hSrw]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [div_mul_eq_mul_div, div_le_iff₀ hNpos] at hspec
  rw [le_div_iff₀ hMpos]
  nlinarith [hspec, norm_nonneg S, hNpos.le, hMpos.le]

open scoped Classical in
/-- **Sub-goal 2 (bookkeeping), PROVED.**  The progression sum `∑_{m<J} F(M m + r)` is the
class sum below `M·J + r` minus a fixed head of at most `r/M + 1` terms.  The head is
independent of `J`, so it dies under the `1/J` normalisation. -/
theorem class_sum_split {M : ℕ} (hM : 0 < M) (r J : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ (range (M * J + r)).filter (fun n => n % M = r % M), F n
      = (∑ n ∈ (range r).filter (fun n => n % M = r % M), F n)
        + ∑ m ∈ range J, F (M * m + r) := by
  classical
  set p : ℕ → Prop := fun n => n % M = r % M with hp
  have hsplit : (range (M * J + r)).filter (fun n => p n)
      = ((range r).filter (fun n => p n))
        ∪ (((range (M * J + r)).filter (fun n => p n)).filter (fun n => r ≤ n)) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_ge n r with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h1, h2⟩
  have hdisj : Disjoint ((range r).filter (fun n => p n))
      (((range (M * J + r)).filter (fun n => p n)).filter (fun n => r ≤ n)) := by
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    have h1 := (Finset.mem_range.1 (Finset.mem_filter.1 hn).1)
    have h2 := (Finset.mem_filter.1 hn').2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  have hrec : ∀ n : ℕ, r ≤ n → n % M = r % M → M * ((n - r) / M) + r = n := by
    intro n h1 h2
    have hdvd : M ∣ (n - r) := (Nat.modEq_iff_dvd' h1).1 h2.symm
    have heq : M * ((n - r) / M) = n - r := Nat.mul_div_cancel' hdvd
    rw [heq]
    exact Nat.sub_add_cancel h1
  refine Finset.sum_nbij' (fun n => (n - r) / M) (fun m => M * m + r) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    rw [Finset.mem_range]
    have hk := hrec n h3 h2
    have hMJ : M * ((n - r) / M) < M * J := by omega
    exact lt_of_mul_lt_mul_left hMJ (Nat.zero_le M)
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨Nat.add_lt_add_right ((Nat.mul_lt_mul_left hM).2 hm) r, ?_⟩, by omega⟩
    rw [hp]
    simp [Nat.mul_add_mod]
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_filter] at hn
    obtain ⟨⟨_, h2⟩, h3⟩ := hn
    exact hrec n h3 h2
  · intro m _
    rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hM]
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_filter] at hn
    obtain ⟨⟨_, h2⟩, h3⟩ := hn
    rw [hrec n h3 h2]

/-- **The geometric Toeplitz kernel.**  If `a i → 0` and `a ≥ 0`, then the geometrically
weighted averages `(∑_{i<I} 2^i a i)/2^I` tend to `0`: the weights concentrate on the top
window, so only the tail of `a` matters. -/
theorem tendsto_geom_weighted_avg {a : ℕ → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun I : ℕ => (∑ i ∈ range I, (2 : ℝ) ^ i * a i) / (2 : ℝ) ^ I) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (by positivity)
  have hmlt : ∀ i, m ≤ i → a i < ε / 2 := by
    intro i hi
    have := hm i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha0 i)] at this
    exact this
  set C : ℝ := ∑ i ∈ range m, (2 : ℝ) ^ i * a i with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (ha0 i)
  obtain ⟨I₁, hI₁⟩ := pow_unbounded_of_one_lt (2 * C / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨max m I₁, fun I hI => ?_⟩
  have hIm : m ≤ I := le_trans (le_max_left _ _) hI
  have hII : I₁ ≤ I := le_trans (le_max_right _ _) hI
  have hpow : (0 : ℝ) < (2 : ℝ) ^ I := by positivity
  have hsplit : ∑ i ∈ range I, (2 : ℝ) ^ i * a i
      = C + ∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * a i := by
    rw [hC, ← Finset.sum_range_add_sum_Ico _ hIm]
  have htail : ∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * a i ≤ (ε / 2) * (2 : ℝ) ^ I := by
    have h1 : ∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * a i
        ≤ ∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * (ε / 2) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have := hmlt i (Finset.mem_Ico.1 hi).1
      exact mul_le_mul_of_nonneg_left this.le (by positivity)
    have h2 : ∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * (ε / 2)
        ≤ (∑ i ∈ range I, (2 : ℝ) ^ i) * (ε / 2) := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
      exact Finset.Ico_subset_Ico (Nat.zero_le m) le_rfl |>.trans
        (by rw [Finset.range_eq_Ico])
    have h3 : (∑ i ∈ range I, (2 : ℝ) ^ i) ≤ (2 : ℝ) ^ I := by
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      have : (0 : ℝ) < (2 : ℝ) ^ I := hpow
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < (2:ℝ) - 1)]
      linarith
    calc ∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * a i ≤ (∑ i ∈ range I, (2 : ℝ) ^ i) * (ε / 2) :=
          le_trans h1 h2
      _ ≤ (2 : ℝ) ^ I * (ε / 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (ε / 2) * (2 : ℝ) ^ I := by ring
  have hCsmall : C / (2 : ℝ) ^ I < ε / 2 := by
    have hmono : (2 : ℝ) ^ I₁ ≤ (2 : ℝ) ^ I := pow_le_pow_right₀ (by norm_num) hII
    have h1 : 2 * C / ε < (2 : ℝ) ^ I := lt_of_lt_of_le hI₁ hmono
    rw [div_lt_iff₀ hpow]
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hnn : 0 ≤ ∑ i ∈ range I, (2 : ℝ) ^ i * a i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (ha0 i)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hnn hpow.le)]
  rw [hsplit, add_div]
  have : (∑ i ∈ Finset.Ico m I, (2 : ℝ) ^ i * a i) / (2 : ℝ) ^ I ≤ ε / 2 := by
    rw [div_le_iff₀ hpow]; linarith [htail]
  linarith

/-- **Sub-goal 3 — the only quantitative step, PROVED.**  The geometric weight concentrates the
dyadic stack on its top window, so an `L^{-c}` saving applied window-by-window survives the sum:
the normalised total still tends to `0`. -/
theorem dyadic_sum_geometric {c : ℝ} (hc : 0 < c) :
    Tendsto (fun I : ℕ =>
      (∑ i ∈ range I, (2 : ℝ) ^ i * (2 * Real.log ((2 : ℝ) ^ i)) ^ (-c)) / (2 : ℝ) ^ I)
      atTop (𝓝 0) := by
  refine tendsto_geom_weighted_avg (fun i => Real.rpow_nonneg (mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_pow₀ (by norm_num)))) _) ?_
  have hbase : Tendsto (fun i : ℕ => 2 * Real.log ((2 : ℝ) ^ i)) atTop atTop := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have : ∀ i : ℕ, 2 * Real.log ((2 : ℝ) ^ i) = (2 * Real.log 2) * (i : ℝ) := by
      intro i; rw [Real.log_pow]; ring
    simp only [this]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
  exact (tendsto_rpow_neg_atTop hc).comp hbase

/-! ### The TOP-DOWN dyadic stack

A bottom-up dyadic decomposition `(2^{i-1}, 2^i]` of `[1, Y]` does **not** work here: the top
window is only partially inside `[1, Y]`, and `TwoPointNaturalCorrelation*` bounds a *full*
window `(N, 2N]`, never a sub-interval — so the partial top window would have to be bounded
trivially, at cost `≍ Y`, destroying the whole estimate.

The fix is to halve from the top: `N_k = Y / 2^k`, giving the levels `(N_{k+1}, N_k]`.  Each
level *is* a full window up to at most one point, because
`N_k ∈ {2·N_{k+1}, 2·N_{k+1} + 1}`.  The stray point costs `1` per level, i.e. `≪ log Y` in
total, which is `o(Y)`.  These two lemmas are that decomposition. -/

/-- **The top-down halving stack.**  `(0, N]` is the union of the levels
`(N/2^{k+1}, N/2^k]`, `k < K`, together with the remaining head `(0, N/2^K]`. -/
theorem sum_Ioc_halving_stack {A : Type*} [AddCommMonoid A] (F : ℕ → A) (N : ℕ) :
    ∀ K : ℕ, ∑ n ∈ Finset.Ioc 0 N, F n
      = (∑ n ∈ Finset.Ioc 0 (N / 2 ^ K), F n)
        + ∑ k ∈ range K, ∑ n ∈ Finset.Ioc (N / 2 ^ (k + 1)) (N / 2 ^ k), F n := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    have hle : N / 2 ^ (K + 1) ≤ N / 2 ^ K :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    rw [Finset.sum_range_succ, ih,
      ← Finset.sum_Ioc_consecutive F (Nat.zero_le (N / 2 ^ (K + 1))) hle]
    abel

/-- **Each level is a full window, up to one point.**  `N_k = N/2^k` satisfies
`N_k ≤ 2·N_{k+1} + 1`, so the level `(N_{k+1}, N_k]` is contained in the full window
`(N_{k+1}, 2·N_{k+1}]` together with at most the single point `2·N_{k+1}+1`. -/
theorem level_le_double_succ (N k : ℕ) : N / 2 ^ k ≤ 2 * (N / 2 ^ (k + 1)) + 1 := by
  have h : N / 2 ^ (k + 1) = N / 2 ^ k / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h]
  omega

/-- The level `(N/2^{k+1}, N/2^k]` always contains the full window `(N/2^{k+1}, 2·N/2^{k+1}]`. -/
theorem double_le_level (N k : ℕ) : 2 * (N / 2 ^ (k + 1)) ≤ N / 2 ^ k := by
  have h : N / 2 ^ (k + 1) = N / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h]; omega

/-- **The per-level bound.**  A level `(a, b]` with `2a ≤ b ≤ 2a+1` is the full window
`(a, 2a]` plus at most one point, so a window bound `B` becomes `B + 1`. -/
theorem norm_sum_level_le {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1) {a b : ℕ}
    (hb1 : 2 * a ≤ b) (hb2 : b ≤ 2 * a + 1)
    {B : ℝ} (hB : ‖∑ n ∈ Finset.Ioc a (2 * a), F n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc a b, F n‖ ≤ B + 1 := by
  rcases Nat.eq_or_lt_of_le hb1 with h | h
  · rw [← h]
    linarith [hB, norm_nonneg (∑ n ∈ Finset.Ioc a (2 * a), F n)]
  · have hbe : b = 2 * a + 1 := by omega
    subst hbe
    rw [Finset.sum_Ioc_succ_top (by omega)]
    exact le_trans (norm_add_le _ _) (add_le_add hB (hF _))

/-! ### The top-down Toeplitz estimate

The analytic heart of the assembly, isolated from all the arithmetic.  After the halving stack,
level `k` contributes `Φ(N_{k+1}) · N_{k+1}` where `N_{k+1} = Y/2^{k+1}` and `Φ` is the
normalised per-scale bound (`Φ a ≍ Cst (2 log a)^{-c}/M` for large `a`, and `Φ a ≤ 1` trivially
for small `a`).  Since `N_{k+1} ≤ Y·2^{-(k+1)}`, the normalised total is at most
`∑_k Φ(N_{k+1}) 2^{-(k+1)}` — a geometric average of `Φ` along scales that all tend to `∞`.
It therefore tends to `0`, **for any number of levels**, which is why the estimate below is
stated for an arbitrary level count `K : ℕ → ℕ`. -/

/-- `∑_{k ∈ [a,b)} 2^{-(k+1)} = 2^{-a} − 2^{-b}`. -/
theorem geom_half_Ico (a : ℕ) : ∀ b : ℕ, a ≤ b →
    ∑ k ∈ Finset.Ico a b, ((1 : ℝ) / 2) ^ (k + 1) = (1 / 2 : ℝ) ^ a - (1 / 2 : ℝ) ^ b := by
  intro b
  induction b with
  | zero => intro h; interval_cases a; simp
  | succ b ih =>
    intro h
    rcases Nat.eq_or_lt_of_le h with h1 | h1
    · rw [← h1]; simp
    · have hab : a ≤ b := by omega
      rw [Finset.sum_Ico_succ_top hab, ih hab]
      ring

/-- `∑_{k ∈ [a,b)} 2^{-(k+1)} ≤ 2^{-a}`. -/
theorem geom_half_Ico_le (a b : ℕ) :
    ∑ k ∈ Finset.Ico a b, ((1 : ℝ) / 2) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ a := by
  rcases le_or_gt a b with h | h
  · rw [geom_half_Ico a b h]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ b := by positivity
    linarith
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- **The top-down Toeplitz estimate.**  If `Φ ≥ 0` is bounded and `Φ a → 0`, then the
`Y`-normalised halving stack `∑_{k<K} Φ(Y/2^{k+1})·(Y/2^{k+1})` tends to `0`, for any level
count `K`. -/
theorem top_down_weighted_tendsto {Φ : ℕ → ℝ} (h0 : ∀ a, 0 ≤ Φ a) {G : ℝ}
    (hG : ∀ a, Φ a ≤ G) (hlim : Tendsto Φ atTop (𝓝 0)) (K : ℕ → ℕ) :
    Tendsto (fun Y : ℕ =>
      (∑ k ∈ range (K Y), Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ)) / (Y : ℝ))
      atTop (𝓝 0) := by
  have hG0 : 0 ≤ G := le_trans (h0 0) (hG 0)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  -- choose the cut `k₀` so the geometric tail is `< ε/2`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, G * (1 / 2 : ℝ) ^ k₀ < ε / 2 := by
    have hpos : (0 : ℝ) < G + 1 := by linarith
    obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < ε / (2 * (G + 1)))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨k₀, ?_⟩
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k₀ := by positivity
    have h3 : (G + 1) * (1 / 2 : ℝ) ^ k₀ < (G + 1) * (ε / (2 * (G + 1))) :=
      mul_lt_mul_of_pos_left hk₀ hpos
    have h2 : (G + 1) * (ε / (2 * (G + 1))) = ε / 2 := by field_simp
    nlinarith [h3, h2, hp]
  -- choose `A` beyond which `Φ < ε/2`
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (by positivity)
  have hAlt : ∀ a, A ≤ a → Φ a < ε / 2 := by
    intro a ha
    have := hA a ha
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (h0 a)] at this
  refine ⟨max 1 (A * 2 ^ k₀), fun Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hYA : A * 2 ^ k₀ ≤ Y := le_trans (le_max_right _ _) hY
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY1
  -- termwise: `Φ(N_{k+1})·N_{k+1}/Y ≤ Φ(N_{k+1})·2^{-(k+1)}`
  have hterm : ∀ k : ℕ, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) / (Y : ℝ)
      ≤ Φ (Y / 2 ^ (k + 1)) * ((1 : ℝ) / 2) ^ (k + 1) := by
    intro k
    have hdiv : ((Y / 2 ^ (k + 1) : ℕ) : ℝ) ≤ (Y : ℝ) / ((2 : ℝ) ^ (k + 1)) := by
      have := Nat.div_mul_le_self Y (2 ^ (k + 1))
      rw [le_div_iff₀ (by positivity)]
      calc ((Y / 2 ^ (k + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))
          = (((Y / 2 ^ (k + 1)) * 2 ^ (k + 1) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (Y : ℝ) := by exact_mod_cast this
    have hgoal : ((Y / 2 ^ (k + 1) : ℕ) : ℝ) / (Y : ℝ) ≤ ((1 : ℝ) / 2) ^ (k + 1) := by
      rw [div_le_iff₀ hYR, div_pow, one_pow, div_mul_eq_mul_div, one_mul]
      exact hdiv
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hgoal (h0 _)
  have hsplit : ∀ k : ℕ, k < k₀ → Φ (Y / 2 ^ (k + 1)) < ε / 2 := by
    intro k hk
    refine hAlt _ ?_
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have h1 : (2 : ℕ) ^ (k + 1) ≤ 2 ^ k₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc A * 2 ^ (k + 1) ≤ A * 2 ^ k₀ := Nat.mul_le_mul_left _ h1
      _ ≤ Y := hYA
  have hnn : 0 ≤ (∑ k ∈ range (K Y), Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ))
      / (Y : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (h0 _) (by positivity)) hYR.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, Finset.sum_div]
  -- split the stack at `k₀`
  rcases le_or_gt (K Y) k₀ with hK | hK
  · have hb : ∑ k ∈ range (K Y),
        Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) / (Y : ℝ)
        ≤ ∑ k ∈ range (K Y), (ε / 2) * ((1 : ℝ) / 2) ^ (k + 1) := by
      refine Finset.sum_le_sum fun k hk => ?_
      refine le_trans (hterm k) (mul_le_mul_of_nonneg_right
        (hsplit k (lt_of_lt_of_le (Finset.mem_range.1 hk) hK)).le (by positivity))
    refine lt_of_le_of_lt hb ?_
    rw [← Finset.mul_sum]
    have : ∑ k ∈ range (K Y), ((1 : ℝ) / 2) ^ (k + 1) ≤ 1 := by
      rw [Finset.range_eq_Ico]
      simpa using geom_half_Ico_le 0 (K Y)
    nlinarith [this, hε]
  · rw [← Finset.sum_range_add_sum_Ico _ hK.le]
    have hb1 : ∑ k ∈ range k₀, Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) / (Y : ℝ)
        ≤ (ε / 2) * ∑ k ∈ range k₀, ((1 : ℝ) / 2) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      exact le_trans (hterm k) (mul_le_mul_of_nonneg_right
        (hsplit k (Finset.mem_range.1 hk)).le (by positivity))
    have hb2 : ∑ k ∈ Finset.Ico k₀ (K Y),
        Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) / (Y : ℝ)
        ≤ G * (1 / 2 : ℝ) ^ k₀ := by
      have hstep : ∑ k ∈ Finset.Ico k₀ (K Y),
          Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) / (Y : ℝ)
          ≤ ∑ k ∈ Finset.Ico k₀ (K Y), G * ((1 : ℝ) / 2) ^ (k + 1) :=
        Finset.sum_le_sum fun k _ =>
          le_trans (hterm k) (mul_le_mul_of_nonneg_right (hG _) (by positivity))
      refine le_trans hstep ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (geom_half_Ico_le k₀ (K Y)) hG0
    have hgeo : ∑ k ∈ range k₀, ((1 : ℝ) / 2) ^ (k + 1) ≤ 1 := by
      rw [Finset.range_eq_Ico]
      simpa using geom_half_Ico_le 0 k₀
    nlinarith [hb1, hb2, hk₀, hε, hgeo]

/-- **The class sum, normalised, tends to zero.**  The whole assembly: halving stack + per-level
window bound + the top-down Toeplitz estimate. -/
theorem class_sum_tendsto_of_noExc (h : TwoPointNaturalCorrelationNoExc)
    {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    (hnp : ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      TTNonPretentious (zOmegaNat z₀) X L)
    {M : ℕ} (hM : 0 < M) (r : ℕ) :
    Tendsto (fun Y : ℕ =>
      ‖∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M),
          z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2)‖ / (Y : ℝ)) atTop (𝓝 0) := by
  classical
  obtain ⟨c, Cst, hc, hCst, N₀, hwin⟩ := dyadic_window_bound_of_noExc h hz₀ hz₁ hnp
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set F : ℕ → ℂ := fun n =>
    if n % M = r % M then z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2) else 0 with hFdef
  have hFnorm : ∀ n, ‖F n‖ ≤ 1 := by
    intro n
    simp only [hFdef]
    by_cases hn : n % M = r % M
    · simp only [if_pos hn, norm_mul, norm_pow, hz₀, hz₁, one_pow, mul_one, le_refl]
    · simp [hn]
  have hfilter : ∀ a b : ℕ,
      ∑ n ∈ (Finset.Ioc a b).filter (fun n => n % M = r % M),
        z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2) = ∑ n ∈ Finset.Ioc a b, F n := by
    intro a b; simp only [hFdef]; rw [Finset.sum_filter]
  set N₀' : ℕ := max N₀ 2 with hN₀'def
  set Φ : ℕ → ℝ := fun a =>
    if N₀' ≤ a ∧ (M : ℝ) ≤ (2 * Real.log a) ^ c then Cst * (2 * Real.log a) ^ (-c) / (M : ℝ)
    else 1 with hΦdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hΦ0 : ∀ a, 0 ≤ Φ a := by
    intro a
    simp only [hΦdef]
    split
    · positivity
    · norm_num
  set G : ℝ := 1 + Cst * (2 * Real.log 2) ^ (-c) / (M : ℝ) with hGdef
  have hGterm : (0 : ℝ) ≤ Cst * (2 * Real.log 2) ^ (-c) / (M : ℝ) := by positivity
  have hΦG : ∀ a, Φ a ≤ G := by
    intro a
    simp only [hΦdef]
    split
    · rename_i hcond
      have ha2 : 2 ≤ a := le_trans (le_max_right _ _) hcond.1
      have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
      have hla : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) haR
      have hx : (0 : ℝ) < 2 * Real.log 2 := by linarith
      have hy : (0 : ℝ) < 2 * Real.log a := by linarith
      have hmono : (2 * Real.log 2) ^ c ≤ (2 * Real.log a) ^ c :=
        Real.rpow_le_rpow hx.le (by linarith) hc.le
      have hxc : (0 : ℝ) < (2 * Real.log 2) ^ c := Real.rpow_pos_of_pos hx c
      have hinv : (2 * Real.log a) ^ (-c) ≤ (2 * Real.log 2) ^ (-c) := by
        rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le, inv_le_inv₀
          (Real.rpow_pos_of_pos hy c) hxc]
        exact hmono
      have hstep : Cst * (2 * Real.log a) ^ (-c) ≤ Cst * (2 * Real.log 2) ^ (-c) :=
        mul_le_mul_of_nonneg_left hinv hCst.le
      have hdiv : Cst * (2 * Real.log a) ^ (-c) / (M : ℝ)
          ≤ Cst * (2 * Real.log 2) ^ (-c) / (M : ℝ) :=
        div_le_div_of_nonneg_right hstep hMR.le
      rw [hGdef]; linarith
    · rw [hGdef]; linarith
  have hΦlim : Tendsto Φ atTop (𝓝 0) := by
    have hbase : Tendsto (fun a : ℕ => 2 * Real.log a) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    have hgo : Tendsto (fun a : ℕ => Cst * (2 * Real.log a) ^ (-c) / (M : ℝ)) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop hc).comp hbase).const_mul Cst
      have h2 := this.div_const (M : ℝ)
      simpa using h2
    refine hgo.congr' ?_
    have hc1 : ∀ᶠ a : ℕ in atTop, N₀' ≤ a := Filter.eventually_atTop.2 ⟨N₀', fun a ha => ha⟩
    have hc2 : ∀ᶠ a : ℕ in atTop, (M : ℝ) ≤ (2 * Real.log a) ^ c :=
      ((tendsto_rpow_atTop hc).comp hbase).eventually_ge_atTop (M : ℝ)
    filter_upwards [hc1, hc2] with a ha1 ha2
    simp only [hΦdef]
    rw [if_pos (And.intro ha1 ha2)]
  -- the per-window bound
  have hB : ∀ a : ℕ, ‖∑ n ∈ Finset.Ioc a (2 * a), F n‖ ≤ Φ a * (a : ℝ) := by
    intro a
    by_cases hcond : N₀' ≤ a ∧ (M : ℝ) ≤ (2 * Real.log a) ^ c
    · have hspec := hwin a (le_trans (le_max_left _ _) hcond.1) M r hM hcond.2
      rw [hfilter] at hspec
      simp only [hΦdef, if_pos hcond]
      refine le_trans hspec (le_of_eq ?_)
      field_simp
    · simp only [hΦdef, if_neg hcond, one_mul]
      refine le_trans (norm_sum_le _ _) ?_
      have h1 : ∑ n ∈ Finset.Ioc a (2 * a), ‖F n‖ ≤ ∑ _n ∈ Finset.Ioc a (2 * a), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => hFnorm n
      refine le_trans h1 ?_
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      have : (2 * a - a : ℕ) = a := by omega
      rw [this]
  -- the halving stack
  have hstack : ∀ Y : ℕ, ‖∑ n ∈ Finset.Ioc 0 Y, F n‖
      ≤ (∑ k ∈ range (Nat.log 2 Y + 1), Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ))
        + ((Nat.log 2 Y + 1 : ℕ) : ℝ) := by
    intro Y
    have hhead : Y / 2 ^ (Nat.log 2 Y + 1) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) Y)
    rw [sum_Ioc_halving_stack F Y (Nat.log 2 Y + 1), hhead]
    simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
    refine le_trans (norm_sum_le _ _) ?_
    have hlev : ∀ k ∈ range (Nat.log 2 Y + 1),
        ‖∑ n ∈ Finset.Ioc (Y / 2 ^ (k + 1)) (Y / 2 ^ k), F n‖
          ≤ Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ) + 1 := fun k _ =>
      norm_sum_level_le hFnorm (double_le_level Y k) (level_le_double_succ Y k) (hB _)
    refine le_trans (Finset.sum_le_sum hlev) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- assembling the limit
  have hmain := top_down_weighted_tendsto hΦ0 hΦG hΦlim (fun Y => Nat.log 2 Y + 1)
  have hlogY : Tendsto (fun Y : ℕ => ((Nat.log 2 Y + 1 : ℕ) : ℝ) / (Y : ℝ)) atTop (𝓝 0) := by
    have hlogdiv : Tendsto (fun Y : ℕ => (Real.log Y / Real.log 2 + 1) / (Y : ℝ))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have h2 : Tendsto (fun Y : ℕ => Real.log Y / (Y : ℝ)) atTop (𝓝 0) :=
        h1.comp tendsto_natCast_atTop_atTop
      have h3 : Tendsto (fun Y : ℕ => (1 : ℝ) / (Y : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h4 := (h2.div_const (Real.log 2)).add h3
      simp only [zero_div, zero_add] at h4
      refine h4.congr fun Y => ?_
      field_simp
    refine squeeze_zero' (Filter.Eventually.of_forall fun Y => by positivity)
      (Filter.eventually_atTop.2 ⟨1, fun Y hY => ?_⟩) hlogdiv
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
    refine div_le_div_of_nonneg_right ?_ hYpos.le
    have hpow : (2 : ℕ) ^ Nat.log 2 Y ≤ Y := Nat.pow_log_le_self 2 (by omega)
    have hpowR : ((2 : ℝ)) ^ (Nat.log 2 Y) ≤ (Y : ℝ) := by exact_mod_cast hpow
    have hle : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log Y := by
      have := Real.log_le_log (by positivity) hpowR
      rwa [Real.log_pow] at this
    push_cast
    rw [div_add' _ _ _ (ne_of_gt hlog2), le_div_iff₀ hlog2]
    nlinarith [hle, hlog2]
  have hsq : Tendsto (fun Y : ℕ =>
      (∑ k ∈ range (Nat.log 2 Y + 1), Φ (Y / 2 ^ (k + 1)) * ((Y / 2 ^ (k + 1) : ℕ) : ℝ))
        / (Y : ℝ) + ((Nat.log 2 Y + 1 : ℕ) : ℝ) / (Y : ℝ)) atTop (𝓝 0) := by
    simpa using hmain.add hlogY
  refine squeeze_zero' (Filter.Eventually.of_forall fun Y => by positivity)
    (Filter.eventually_atTop.2 ⟨1, fun Y hY => ?_⟩) hsq
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  rw [hfilter, ← add_div]
  exact div_le_div_of_nonneg_right (hstack Y) hYpos.le

open scoped Classical in
/-- **THE PAYOFF.**  Removing the exceptional set from Tao–Teräväinen Theorem 3.1(ii)
discharges the `K = 2` natural-density transfer — the last open obligation of the `D = 2`
layer of `ConjC3`.

The hypothesis `z 0 ≠ 1` is not stated: what is actually needed is the non-pretentiousness of
`z 0 ^ ω` in TT's sense, supplied as `hnp`.  (`LogToNaturalCorrelation K` as written carries no
such hypothesis and is false without one — take `z ≡ 1` — so it is only ever usable through its
log-averaged premise; the consumer `depthAvg_tendsto_of_transfer` has `z 0 ≠ 1` in hand.) -/
theorem logToNatural_two_of_noExc (h : TwoPointNaturalCorrelationNoExc)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (hnp : ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      TTNonPretentious (zOmegaNat (z 0)) X L)
    {M : ℕ} (hM : 0 < M) (r : ℕ) :
    Tendsto (fun J : ℕ =>
        (∑ m ∈ range J, ∏ i : Fin 2, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)) / (J : ℂ))
      atTop (𝓝 0) := by
  classical
  set g : ℕ → ℂ := fun n => z 0 ^ omegaNat (n + 1) * z 1 ^ omegaNat (n + 2) with hgdef
  have hgnorm : ∀ n, ‖g n‖ = 1 := by
    intro n; simp only [hgdef, norm_mul, norm_pow, hz, one_pow, mul_one]
  have hprod : ∀ m : ℕ, (∏ i : Fin 2, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)) = g (M * m + r) := by
    intro m
    rw [Fin.prod_univ_two, hgdef]
    norm_num
  have hCS := class_sum_tendsto_of_noExc h (hz 0) (hz 1) hnp hM r
  -- the head, and the two boundary points
  have hbound : ∀ J : ℕ, 1 ≤ J →
      ‖∑ m ∈ range J, g (M * m + r)‖
        ≤ ((r : ℝ) + 2)
          + ‖∑ n ∈ (Finset.Ioc 0 (M * J + r)).filter (fun n => n % M = r % M),
              z 0 ^ omegaNat (n + 1) * z 1 ^ omegaNat (n + 2)‖ := by
    intro J hJ
    set Y : ℕ := M * J + r with hY
    have hsplit := class_sum_split hM r J g
    have hhead : ‖∑ n ∈ (range r).filter (fun n => n % M = r % M), g n‖ ≤ (r : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      have h1 : ∑ n ∈ (range r).filter (fun n => n % M = r % M), ‖g n‖
          ≤ ∑ _n ∈ (range r).filter (fun n => n % M = r % M), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => le_of_eq (hgnorm n)
      refine le_trans h1 ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have := Finset.card_filter_le (range r) (fun n => n % M = r % M)
      rw [Finset.card_range] at this
      exact_mod_cast this
    -- `range Y` vs `Ioc 0 Y` differ by the two endpoints `0` and `Y`
    have hrange : ∑ n ∈ (range Y).filter (fun n => n % M = r % M), g n
        = (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
          + ((if (0 : ℕ) % M = r % M then g 0 else 0)
             - (if Y % M = r % M then g Y else 0)) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      have hMJ : 0 < M * J := Nat.mul_pos hM hJ
      have hY0 : 0 < Y := by omega
      have h1 : ∑ n ∈ range Y, (if n % M = r % M then g n else 0)
          = (if (0 : ℕ) % M = r % M then g 0 else 0)
            + ∑ n ∈ Finset.Ico 1 Y, (if n % M = r % M then g n else 0) := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hY0]
      have h2 : ∑ n ∈ Finset.Ioc 0 Y, (if n % M = r % M then g n else 0)
          = (∑ n ∈ Finset.Ico 1 Y, (if n % M = r % M then g n else 0))
            + (if Y % M = r % M then g Y else 0) := by
        rw [show Finset.Ioc 0 Y = Finset.Ico 1 Y ∪ {Y} by
          ext n; simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_Ico,
            Finset.mem_singleton]; omega]
        rw [Finset.sum_union (by
          refine Finset.disjoint_left.2 fun n hn hn' => ?_
          rw [Finset.mem_Ico] at hn
          rw [Finset.mem_singleton] at hn'
          omega)]
        simp
      rw [h1, h2]
      ring
    have heq : ∑ m ∈ range J, g (M * m + r)
        = (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
          + ((if (0 : ℕ) % M = r % M then g 0 else 0)
             - (if Y % M = r % M then g Y else 0))
          - ∑ n ∈ (range r).filter (fun n => n % M = r % M), g n := by
      rw [← hrange, hY, hsplit]
      ring
    rw [heq]
    have hb1 : ‖(if (0 : ℕ) % M = r % M then g 0 else 0)‖ ≤ 1 := by
      split
      · exact le_of_eq (hgnorm 0)
      · simp
    have hb2 : ‖(if Y % M = r % M then g Y else 0)‖ ≤ 1 := by
      split
      · exact le_of_eq (hgnorm Y)
      · simp
    have := norm_sub_le
      ((∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
        + ((if (0 : ℕ) % M = r % M then g 0 else 0) - (if Y % M = r % M then g Y else 0)))
      (∑ n ∈ (range r).filter (fun n => n % M = r % M), g n)
    have h3 := norm_add_le
      (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
      ((if (0 : ℕ) % M = r % M then g 0 else 0) - (if Y % M = r % M then g Y else 0))
    have h4 := norm_sub_le
      ((if (0 : ℕ) % M = r % M then g 0 else 0)) ((if Y % M = r % M then g Y else 0))
    have hgeq : (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
        = ∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M),
            z 0 ^ omegaNat (n + 1) * z 1 ^ omegaNat (n + 2) := rfl
    rw [hgeq] at h3 ⊢
    linarith [hhead, hb1, hb2, this, h3, h4]
  -- the majorant
  have hcomp : Tendsto (fun J : ℕ =>
      ‖∑ n ∈ (Finset.Ioc 0 (M * J + r)).filter (fun n => n % M = r % M),
          z 0 ^ omegaNat (n + 1) * z 1 ^ omegaNat (n + 2)‖ / ((M * J + r : ℕ) : ℝ))
      atTop (𝓝 0) := by
    refine hCS.comp (tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b + r, fun J hJ => ?_⟩)
    calc b ≤ J := by omega
      _ ≤ M * J := Nat.le_mul_of_pos_left J hM
      _ ≤ M * J + r := by omega
  have hmaj : Tendsto (fun J : ℕ => ((r : ℝ) + 2) / (J : ℝ)
      + (‖∑ n ∈ (Finset.Ioc 0 (M * J + r)).filter (fun n => n % M = r % M),
            z 0 ^ omegaNat (n + 1) * z 1 ^ omegaNat (n + 2)‖ / ((M * J + r : ℕ) : ℝ))
        * ((M : ℝ) + r)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun J : ℕ => ((r : ℝ) + 2) / (J : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_one_div_atTop_nhds_zero_nat.const_mul ((r : ℝ) + 2)
    have h2 := hcomp.mul_const ((M : ℝ) + r)
    simpa using h1.add h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun J => norm_nonneg _)
    (Filter.eventually_atTop.2 ⟨1, fun J hJ => ?_⟩) hmaj
  have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hYpos : (0 : ℝ) < ((M * J + r : ℕ) : ℝ) := by
    have : 0 < M * J + r := by positivity
    exact_mod_cast this
  rw [norm_div, Complex.norm_natCast]
  have hnum : ‖∑ m ∈ range J, ∏ i : Fin 2, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)‖
      = ‖∑ m ∈ range J, g (M * m + r)‖ :=
    congrArg norm (Finset.sum_congr rfl fun m _ => hprod m)
  rw [hnum]
  set S : ℝ := ‖∑ n ∈ (Finset.Ioc 0 (M * J + r)).filter (fun n => n % M = r % M),
      z 0 ^ omegaNat (n + 1) * z 1 ^ omegaNat (n + 2)‖ with hS
  have hS0 : 0 ≤ S := norm_nonneg _
  have hratio : ((M * J + r : ℕ) : ℝ) / (J : ℝ) ≤ (M : ℝ) + r := by
    rw [div_le_iff₀ hJR]
    push_cast
    nlinarith [hJR, (by exact_mod_cast hJ : (1:ℝ) ≤ (J:ℝ)), Nat.cast_nonneg (α := ℝ) r]
  have hkey : S / (J : ℝ) ≤ (S / ((M * J + r : ℕ) : ℝ)) * ((M : ℝ) + r) := by
    have h1 : (1 : ℝ) / (J : ℝ) ≤ ((M : ℝ) + r) / ((M * J + r : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hJR hYpos]
      rw [div_le_iff₀ hJR] at hratio
      linarith
    calc S / (J : ℝ) = S * (1 / (J : ℝ)) := by ring
      _ ≤ S * (((M : ℝ) + r) / ((M * J + r : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h1 hS0
      _ = (S / ((M * J + r : ℕ) : ℝ)) * ((M : ℝ) + r) := by ring
  have hthis := hbound J hJ
  rw [← hS] at hthis
  have hfin : ‖∑ m ∈ range J, g (M * m + r)‖ / (J : ℝ)
      ≤ ((r : ℝ) + 2) / (J : ℝ) + S / (J : ℝ) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hthis hJR.le
  linarith [hfin, hkey]

#print axioms exceptional_set_can_pin_a_scale
#print axioms twoPointNatural_of_noExc
#print axioms tendsto_geom_weighted_avg
#print axioms dyadic_sum_geometric
#print axioms dyadic_window_bound_of_noExc
#print axioms class_sum_split
#print axioms sum_Ioc_halving_stack
#print axioms double_le_level
#print axioms norm_sum_level_le
#print axioms geom_half_Ico_le
#print axioms top_down_weighted_tendsto
#print axioms class_sum_tendsto_of_noExc
#print axioms logToNatural_two_of_noExc

end CastingOut

end NormalNumbers
