/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Predict

/-!
# S7-G2: the gap does not save the predictable-hit principle

Lap 56 reduced Vandehey §7 Problem 1 to `WindowedPullback`, whose decisive component is that the
transducer target is determined by a **window** of `k` input digits.  Lap 57 showed the target's
*shape* is window-determined and its *location* is not, and asked (lap 58's probe) whether a
location-free hit principle could still hold: the predictor announces an interval from the past,
the observation happens `k` steps later, and only the interval's *length* is constrained.

This module answers that in the kernel, for every gap `k`, and the answer is as negative as it can
be.

## The theorems

* `exists_predictor_all_hit` — for **every** sequence `u`, every width `δ > 0` and every gap `k`
  there is a predictor `F` reading the prefix `u₀ … u_{n−1}` whose announced interval of width `δ`
  contains `u_{n+k}` for **every** `n`.  Hit frequency `1`, uniformly.  The witness is
  `F l := u (l.length + k) − δ/2`: a prefix of length `n` announces its own length, and the length
  already determines the observation time.
* `not_gappedHitPrinciple` — consequently the gapped principle fails against a sequence with
  *perfect* marginals (the `10`-point grid, `δ = 1/2`): frequency `1` where the principle allows
  `6/10`.

## What this settles

"Predictable + narrow + the orbit is CF-normal" carries **zero** information about hit frequency,
no matter how large the gap.  Only *finiteness of the predictor's range* — a genuine window
predictor, finitely many announced intervals — can help, and that case is already a theorem
(`windowHit_Ioo_le`, constant `(1+8log2)/log2`).  So the location-determinacy in
`WindowedPullback` is not an artefact of how it was stated: it is the entire content, and the
route must go through the arithmetic of `Φ` (`VandeheyS7Lattice`), as the directive's fact (γ)
demands.

## Guard rule

Content locator: `exists_predictor_all_hit` needs `0 < δ` only — it is the cheapness of the
predictor class, not any property of `u`, that kills the principle; and `not_gappedHitPrinciple`
needs a `u` with perfect marginals, so the failure is *not* a marginals failure.  Degenerate case:
`k = 0` recovers the ungapped statement, which `not_predictableHitPrinciple` already refutes by a
harder witness (a predictor reading only the previous term).
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-- The gapped hit count: the predictor speaks at time `n` from `u₀ … u_{n−1}`, and the
observation is `u_{n+k}`. -/
noncomputable def gapHitCount (F : List ℝ → ℝ) (u : ℕ → ℝ) (δ : ℝ) (k N : ℕ) : ℕ :=
  ((Finset.range N).filter
    (fun n => predict F u n < u (n + k) ∧ u (n + k) < predict F u n + δ)).card

/-- **Predictability is vacuous.**  Whatever the sequence, whatever the gap, a prefix-reading
predictor can announce an interval of width `δ` containing the observation every single time. -/
theorem exists_predictor_all_hit (u : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ F : List ℝ → ℝ, ∀ n : ℕ, predict F u n < u (n + k) ∧ u (n + k) < predict F u n + δ := by
  refine ⟨fun l => u (l.length + k) - δ / 2, fun n => ?_⟩
  have hlen : ((List.range n).map u).length = n := by simp
  simp only [predict, hlen]
  constructor <;> linarith

/-- The same, as a hit count: every `n < N` is a hit. -/
theorem gapHitCount_eq_of_predictor (u : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k N : ℕ) :
    ∃ F : List ℝ → ℝ, gapHitCount F u δ k N = N := by
  obtain ⟨F, hF⟩ := exists_predictor_all_hit u hδ k
  refine ⟨F, ?_⟩
  rw [gapHitCount, Finset.filter_true_of_mem (fun n _ => hF n), Finset.card_range]

/-- **The gapped predictable-hit principle**: the statement `WindowedPullback` would need if the
target's location were allowed to be arbitrary. -/
def GappedHitPrinciple (k : ℕ) : Prop :=
  ∀ (δ : ℝ) (m N : ℕ) (u : ℕ → ℝ) (F : List ℝ → ℝ),
    0 < δ → 0 < m → 0 < N → (1 : ℝ) / m < δ →
    (∀ n, u n ∈ Set.Ico (0 : ℝ) 1) → CellUniform m N u →
      (gapHitCount F u δ k N : ℝ) ≤ (δ + 1 / m) * N

/-- A cell-uniform sequence defined for **all** `n`: the `10`-point grid, read cyclically. -/
noncomputable def cycGrid (m : ℕ) (n : ℕ) : ℝ := ((n % m : ℕ) : ℝ) / m

theorem cycGrid_mem_Ico {m : ℕ} (hm : 0 < m) (n : ℕ) : cycGrid m n ∈ Set.Ico (0 : ℝ) 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · rw [cycGrid]; positivity
  · rw [cycGrid, div_lt_one hm0]
    exact_mod_cast Nat.mod_lt n hm

theorem cycGrid_eq_grid {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : n < m) :
    cycGrid m n = (n : ℝ) / m := by
  rw [cycGrid, Nat.mod_eq_of_lt hn]

/-- The cyclic grid has perfect marginals over the horizon `N = m`. -/
theorem cellUniform_cycGrid {m : ℕ} (hm : 0 < m) : CellUniform m m (cycGrid m) := by
  classical
  intro j hj
  have hfil : (Finset.range m).filter
      (fun n => (j : ℝ) / m ≤ cycGrid m n ∧ cycGrid m n < ((j : ℝ) + 1) / m) = {j} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    constructor
    · rintro ⟨hn, h1, h2⟩
      rw [cycGrid_eq_grid hm hn] at h1 h2
      rw [div_le_div_iff_of_pos_right hm0] at h1
      rw [div_lt_div_iff_of_pos_right hm0] at h2
      have hjn : (j : ℝ) ≤ (n : ℝ) := h1
      have hnj : (n : ℝ) < (j : ℝ) + 1 := h2
      have h3 : j ≤ n := by exact_mod_cast hjn
      have h4 : n < j + 1 := by exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((j + 1 : ℕ) : ℝ))
      omega
    · rintro rfl
      refine ⟨hj, ?_, ?_⟩
      · rw [cycGrid_eq_grid hm hj]
      · rw [cycGrid_eq_grid hm hj]
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
        rw [div_lt_div_iff_of_pos_right hm0]
        linarith
  rw [hfil]
  simp

/-- **REFUTED, at every gap.**  Perfect marginals, a target far wider than a cell, and the
observation `k` steps after the prediction: the hit frequency is `1` where the principle allows
`6/10`. -/
theorem not_gappedHitPrinciple (k : ℕ) : ¬ GappedHitPrinciple k := by
  intro h
  obtain ⟨F, hF⟩ := gapHitCount_eq_of_predictor (cycGrid 10) (show (0:ℝ) < 1/2 by norm_num) k 10
  have hbound := h (1 / 2) 10 10 (cycGrid 10) F (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (cycGrid_mem_Ico (by norm_num)) (cellUniform_cycGrid (by norm_num))
  rw [hF] at hbound
  norm_num at hbound

section Audit

#print axioms exists_predictor_all_hit
#print axioms cellUniform_cycGrid
#print axioms not_gappedHitPrinciple

end Audit

end NormalNumbers.VandeheyS7
