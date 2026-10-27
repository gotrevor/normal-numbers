/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Wall
import Architect

/-!
# A low orbit mean obstructs normality

Normality forces half of the orbit visits into `[1/2,1)`, and each such visit
contributes at least `1/2` to the orbit sum.  Thus a sufficiently small upper
bound on the partial sums contradicts Wall's equidistribution criterion.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter

/-- A uniform mean bound below `1/4` rules out normality: equidistribution
would force orbit frequency `1/2` on `[1/2,1)`, while the sum bound forces
that frequency to be at most `1/4` asymptotically. -/
@[blueprint (title := "A small radix orbit mean obstructs normality")]
theorem not_isNormal_of_orbit_sum_bound (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hbound : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, NormalNumbers.orbit b x n) ≤ ((N : ℝ) + 2) / 8) :
    ¬ NormalNumbers.IsNormal b x := by
  intro hnormal
  let I : Set ℝ := Set.Ico (1 / 2 : ℝ) 1
  let freq : ℕ → ℝ := fun N =>
    (NormalNumbers.visitCount (NormalNumbers.orbit b x) (1 / 2) 1 N : ℝ) / N
  have heq : NormalNumbers.Equidistributed (NormalNumbers.orbit b x) :=
    (NormalNumbers.isNormal_iff_equidistributed_orbit b hb x).mp hnormal
  have hfreq : Tendsto freq atTop (nhds (1 / 2 : ℝ)) := by
    have h := heq (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    simpa [freq] using h
  have hcountSum (N : ℕ) :
      (NormalNumbers.visitCount (NormalNumbers.orbit b x) (1 / 2) 1 N : ℝ) / 2 ≤
        ∑ n ∈ Finset.range N, NormalNumbers.orbit b x n := by
    let V := (Finset.range N).filter (fun n => NormalNumbers.orbit b x n ∈ I)
    have hlow : ∑ n ∈ V, (1 / 2 : ℝ) ≤
        ∑ n ∈ V, NormalNumbers.orbit b x n :=
      Finset.sum_le_sum fun n hn => (Finset.mem_filter.mp hn).2.1
    have hsub : ∑ n ∈ V, NormalNumbers.orbit b x n ≤
        ∑ n ∈ Finset.range N, NormalNumbers.orbit b x n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => Int.fract_nonneg _)
    have hcard : NormalNumbers.visitCount (NormalNumbers.orbit b x) (1 / 2) 1 N = V.card := rfl
    rw [hcard]
    have hconst : ∑ n ∈ V, (1 / 2 : ℝ) = (V.card : ℝ) / 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [← hconst]
    exact le_trans hlow hsub
  have hfreqBound : ∀ N : ℕ, 6 ≤ N → freq N ≤ 1 / 3 := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hcount :
        (NormalNumbers.visitCount (NormalNumbers.orbit b x) (1 / 2) 1 N : ℝ)
          ≤ ((N : ℝ) + 2) / 4 := by
      have h := hcountSum N
      have hbN := hbound N
      nlinarith
    have hNreal : (6 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [freq]
    rw [div_le_iff₀ hNpos]
    nlinarith [hcount]
  have hevent : ∀ᶠ N : ℕ in atTop, (1 / 3 : ℝ) < freq N :=
    hfreq.eventually (Ioi_mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
  let N := max N₀ 6
  have hN₀' : N₀ ≤ N := le_max_left _ _
  have hN6 : 6 ≤ N := le_max_right _ _
  have hsmall := hfreqBound N hN6
  have hlarge := hN₀ N hN₀'
  linarith

end NormalNumbers.ArithmeticDisjunctivity
