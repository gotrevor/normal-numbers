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

/-- **Sub-goal 1 (bookkeeping).**  A single dyadic window, at `X = N²`, `L = 2 log N`.
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
  sorry

/-- **Sub-goal 2 (bookkeeping).**  The class below `M·J` is the disjoint union of dyadic
windows plus a bounded head. -/
theorem dyadic_decomposition {M r : ℕ} (hM : 0 < M) (J : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ range J, F (M * m + r)
      = ∑ n ∈ (range (M * J + r)).filter (fun n => n % M = r % M ∧ r ≤ n), F n := by
  sorry

/-- **Sub-goal 3 — the only quantitative step.**  The geometric weight concentrates the dyadic
stack on its top window, so summing an `L^{-c}` saving over `I` dyadic scales costs only a
constant. -/
theorem dyadic_sum_geometric {c : ℝ} (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ I : ℕ, 2 ≤ I →
      ∑ i ∈ range I, (2 : ℝ) ^ i * (2 * Real.log ((2 : ℝ) ^ i)) ^ (-c)
        ≤ D * (2 : ℝ) ^ I * (2 * Real.log ((2 : ℝ) ^ I)) ^ (-c) := by
  sorry

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

end CastingOut

end NormalNumbers
