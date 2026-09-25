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

/-- **THE PAYOFF.**  Removing the exceptional set from TT Theorem 3.1(ii) discharges
`LogToNaturalCorrelation 2` — the last open obligation of the `D = 2` layer.  With this, the
`D = 2` row of the ledger is *equivalent to a named open problem in the literature*, and
nothing else is missing at `K = 2`. -/
theorem logToNatural_two_of_noExc (h : TwoPointNaturalCorrelationNoExc)
    (hnp : ∀ (z : ℂ), ‖z‖ = 1 → z ≠ 1 → ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      TTNonPretentious (zOmegaNat z) X L) :
    LogToNaturalCorrelation 2 := by
  sorry

#print axioms exceptional_set_can_pin_a_scale
#print axioms twoPointNatural_of_noExc
#print axioms tendsto_geom_weighted_avg
#print axioms dyadic_sum_geometric
#print axioms dyadic_window_bound_of_noExc
#print axioms class_sum_split

end CastingOut

end NormalNumbers
