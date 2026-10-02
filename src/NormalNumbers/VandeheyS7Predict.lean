/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Cell

/-!
# S7-P1: predictability plus smallness is not enough, and here is the witness

The crux `OrbitCellBound` unwinds to

  `limsup (1/N) #{n < N : Gⁿx ∈ s_n⁻¹(E)} ≤ C γ(E)`,

where the target set `A n = s_n⁻¹(E)` is **predictable** — determined by the input digits
`x₁…x_n` — and has controlled size, while the input `x` is CF-normal, i.e. its orbit has the
correct *marginal* frequencies.  The tempting step is to conclude directly from those three facts.

This module shows, in the kernel, that those three facts are **not enough**: a sequence with
perfect marginals can land in its own predicted interval far more often than the interval's
length, for a predictor that reads only *one* earlier term.

## The witness

`u n = n/k` on the horizon `k`.  It is *exactly* uniform on the `k` cells of width `1/k`
(`cellUniform_grid`: each cell gets exactly one term — perfect marginals, no error at all).  The
predictor is `lastPredict`, "the previous term".  Then `u n` lies in `(u_{n−1}, u_{n−1} + δ)` for
**every** `n ≥ 1` as soon as `1/k < δ` (`hitCount_grid`), so the hit frequency is `(k−1)/k`, close
to `1`, while the interval has length `δ` and the cells have width `1/k`.  Taking `δ = 1/2` and
`k = 10` gives frequency `9/10` against a predicted `6/10`: `not_predictableHitPrinciple`.

## What it does and does not say

It does **not** say the crux is false: the transducer's states are not an arbitrary predictor, and
`u n = n/k` is not a Gauss orbit.  What it says is that any proof of `OrbitCellBound` must use the
*specific arithmetic* of `s_n = O_n⁻¹ Φ P_n` — the `Γ\SL₂(ℝ)` structure of the directive's fact
(γ) — and can never be assembled out of "predictable + small + correct marginals" alone.  Together
with `no_window_function` (the state is not a function of a bounded window) this closes both soft
routes: the state cannot be forgotten, and it cannot be ignored.

## Guard rule

Content locator: `predictableHitPrinciple_of_one_le_delta` — for `δ ≥ 1` the principle is free, so
all its content is at small `δ`; and `hitCount_le_horizon` is the trivial bound the principle must
beat.  Degenerate cases: `cellUniform_one` — at `m = 1` cell-uniformity says only "every term lies
in `[0,1)`", so the hypothesis carries no information there; and at `k = 1` the grid's hit count is
`0`, so the witness genuinely needs `k` large (`1/k < δ`).
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-! ## Predictors and hit counts -/

/-- The value a predictor `F` announces at time `n`, reading only the earlier terms. -/
noncomputable def predict (F : List ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  F ((List.range n).map u)

/-- The number of times, before the horizon `N`, that `u` lands in its own predicted interval of
width `δ`. -/
noncomputable def hitCount (F : List ℝ → ℝ) (u : ℕ → ℝ) (δ : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter
    (fun n => predict F u n < u n ∧ u n < predict F u n + δ)).card

/-- Exact uniformity on the `m` cells of width `1/m`, over the horizon `N`: the strongest possible
marginal hypothesis, and strictly stronger than anything CF-normality supplies. -/
def CellUniform (m N : ℕ) (u : ℕ → ℝ) : Prop :=
  ∀ j < m, ((Finset.range N).filter
    (fun n => (j : ℝ) / m ≤ u n ∧ u n < ((j : ℝ) + 1) / m)).card * m = N

/-- The trivial bound the principle has to beat. -/
theorem hitCount_le_horizon (F : List ℝ → ℝ) (u : ℕ → ℝ) (δ : ℝ) (N : ℕ) :
    hitCount F u δ N ≤ N := by
  rw [hitCount]
  calc ((Finset.range N).filter _).card ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

/-! ## The principle -/

/-- **The predictable-hit principle** (REFUTED below).  A sequence with perfect marginals on cells
of width `1/m` lands in its own predicted interval of width `δ` at most a `δ + 1/m` fraction of
the time.  This is the abstract form of the step `OrbitCellBound` would need. -/
def PredictableHitPrinciple : Prop :=
  ∀ (δ : ℝ) (m N : ℕ) (u : ℕ → ℝ) (F : List ℝ → ℝ),
    0 < δ → 0 < m → 0 < N → (1 : ℝ) / m < δ →
    (∀ n < N, u n ∈ Set.Ico (0 : ℝ) 1) → CellUniform m N u →
      (hitCount F u δ N : ℝ) ≤ (δ + 1 / m) * N

/-- **Content locator.**  For `δ ≥ 1` the principle is free: the count never exceeds `N`. -/
theorem predictableHitPrinciple_of_one_le_delta {δ : ℝ} (hδ : 1 ≤ δ) {m N : ℕ} (hm : 0 < m)
    (u : ℕ → ℝ) (F : List ℝ → ℝ) : (hitCount F u δ N : ℝ) ≤ (δ + 1 / m) * N := by
  have h1 : (hitCount F u δ N : ℝ) ≤ N := by exact_mod_cast hitCount_le_horizon F u δ N
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have : (1 : ℝ) * N ≤ (δ + 1 / m) * N := by
    have : (1 : ℝ) ≤ δ + 1 / m := by
      have : (0 : ℝ) < 1 / m := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg N)
  linarith

/-- **Degenerate case.**  At `m = 1` cell-uniformity says only "every term lies in `[0,1)`". -/
theorem cellUniform_one {N : ℕ} {u : ℕ → ℝ} (h : ∀ n < N, u n ∈ Set.Ico (0 : ℝ) 1) :
    CellUniform 1 N u := by
  intro j hj
  interval_cases j
  simp only [Nat.cast_zero, Nat.cast_one, zero_add, div_one, mul_one]
  have hall : ∀ n ∈ Finset.range N, (0 : ℝ) ≤ u n ∧ u n < 1 := by
    intro n hn
    exact h n (Finset.mem_range.1 hn)
  rw [Finset.filter_true_of_mem hall, Finset.card_range]

/-! ## The witness: the uniform grid, predicted by its own previous term -/

/-- The grid `u n = n/k`. -/
noncomputable def grid (k : ℕ) (n : ℕ) : ℝ := (n : ℝ) / k

/-- "The previous term", as a predictor: `foldl` keeping the last entry, `0` on the empty list. -/
def lastPredict : List ℝ → ℝ := fun l => l.foldl (fun _ a => a) 0

theorem predict_lastPredict_zero (u : ℕ → ℝ) : predict lastPredict u 0 = 0 := rfl

theorem predict_lastPredict_succ (u : ℕ → ℝ) (n : ℕ) :
    predict lastPredict u (n + 1) = u n := by
  rw [predict, lastPredict, List.range_succ, List.map_append]
  simp

/-- The grid lands one term in each cell: perfect marginals. -/
theorem cellUniform_grid {k : ℕ} (hk : 0 < k) : CellUniform k k (grid k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  intro j hj
  have hfil : (Finset.range k).filter
      (fun n => (j : ℝ) / k ≤ grid k n ∧ grid k n < ((j : ℝ) + 1) / k) = {j} := by
    apply Finset.ext
    intro n
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h1, h2⟩
      rw [grid] at h1 h2
      have hj1 : (j : ℝ) ≤ (n : ℝ) := (div_le_div_iff_of_pos_right hkR).1 h1
      have hj2 : (n : ℝ) < (j : ℝ) + 1 := (div_lt_div_iff_of_pos_right hkR).1 h2
      have hle : j ≤ n := by exact_mod_cast hj1
      have hlt : n < j + 1 := by
        have hc : (n : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast hc
      omega
    · rintro rfl
      refine ⟨hj, le_of_eq (by rw [grid]), ?_⟩
      rw [grid]
      exact (div_lt_div_iff_of_pos_right hkR).2 (by linarith)
  rw [hfil, Finset.card_singleton, one_mul]

/-- On the grid, every step lands in the interval predicted by the previous term, as soon as the
step `1/k` is shorter than `δ`. -/
theorem hitCount_grid {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : (1 : ℝ) / k < δ) :
    hitCount lastPredict (grid k) δ k = k - 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfil : (Finset.range k).filter
      (fun n => predict lastPredict (grid k) n < grid k n ∧
        grid k n < predict lastPredict (grid k) n + δ) = Finset.Ico 1 k := by
    apply Finset.ext
    intro n
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    cases n with
    | zero =>
        rw [predict_lastPredict_zero]
        have h0 : grid k 0 = 0 := by rw [grid]; simp
        rw [h0]
        constructor
        · rintro ⟨-, h1, -⟩; exact absurd h1 (lt_irrefl 0)
        · rintro ⟨h1, -⟩; omega
    | succ m =>
        rw [predict_lastPredict_succ]
        constructor
        · rintro ⟨hlt, -, -⟩; exact ⟨Nat.succ_le_succ (Nat.zero_le m), hlt⟩
        · rintro ⟨-, hlt⟩
          refine ⟨hlt, ?_, ?_⟩
          · rw [grid, grid]
            exact (div_lt_div_iff_of_pos_right hkR).2 (by push_cast; linarith)
          · rw [grid, grid]
            have hstep : (((m + 1 : ℕ)) : ℝ) / k = (m : ℝ) / k + 1 / k := by push_cast; ring
            rw [hstep]
            linarith
  rw [hitCount, hfil, Nat.card_Ico]

/-! ## The refutation -/

/-- **REFUTED.**  Perfect marginals, an interval far wider than a cell, and a predictor that reads
only the previous term: the hit frequency is `9/10` where the principle allows `6/10`. -/
theorem not_predictableHitPrinciple : ¬ PredictableHitPrinciple := by
  intro h
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hmem : ∀ n < 10, grid 10 n ∈ Set.Ico (0 : ℝ) 1 := by
    intro n hn
    constructor
    · rw [grid]; positivity
    · rw [grid, div_lt_one (by norm_num)]
      exact_mod_cast (by exact_mod_cast hn : (n : ℝ) < (10 : ℕ))
  have hbound := h (1 / 2) 10 10 (grid 10) lastPredict hδ (by norm_num) (by norm_num)
    (by norm_num) hmem (cellUniform_grid (by norm_num))
  rw [hitCount_grid (by norm_num) (by norm_num : (1 : ℝ) / (10 : ℕ) < 1 / 2)] at hbound
  norm_num at hbound

section Audit

#print axioms hitCount_le_horizon
#print axioms predictableHitPrinciple_of_one_le_delta
#print axioms cellUniform_one
#print axioms predict_lastPredict_succ
#print axioms cellUniform_grid
#print axioms hitCount_grid
#print axioms not_predictableHitPrinciple

end Audit

end NormalNumbers.VandeheyS7
