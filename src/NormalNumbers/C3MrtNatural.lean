/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtSmallPrimes

/-!
# The natural-density `D`-point rung, and the one named barrier left

Laps 53–54 reduced `depthAvg b P Q j h D N` — twist and all — to FULL-`ω` correlations along the
arithmetic progressions `M·X + (r+i+1)`, `M = Q · primorial P` (`norm_depthAvg_le_omega_progressions`).
Laps 35–52 built the `K`-fold assembly, which bounds such correlations **log-averaged**.

This file names the two obligations that stand between those two facts and the *natural*-density
`D`-point rung, and proves the rung from them.

* `ProgressionLogRung K` — the `K`-fold assembly's conclusion, along a progression.
  `rung_multi_correlation` is exactly this with `M = 1`, `r = 0`; the general `(M, r)` case is the
  same proof with the joint modulus `lcm(d)` replaced by `lcm(M, d)` throughout the truncation
  chain.  **Bookkeeping, no new analytic input** — but several files' worth, so it is named rather
  than inlined.
* `LogToNaturalCorrelation K` — **the barrier.**  Log-averaged `o(log N)` control of a `K`-point
  correlation, upgraded to natural-density `o(1)`.  This is NOT bookkeeping: log control gives
  `S(N) = o(log N)`, and the natural mean over a window `(X, AX]` needs `S(AX) − S(X) = o(1)`,
  which `o(log N)` does not supply.  It is the *log-Chowla ⇏ Chowla* barrier, open even at `K = 2`
  for the Liouville function.  The whole `D ≥ 2` route of `ConjC3` rests on it.

`depthAvg_tendsto_of_transfer` is the payoff: at every FIXED depth `D`, the twisted `D`-point
depth average tends to `0`.  That is the exact generalisation of `depthAvg_one_tendsto` (`D = 1`,
Selberg–Delange) to all `D`, and the first natural-density multi-point statement of the campaign.
The remaining gap to `DepthElliott` is then *uniformity in `D`* along the schedule `D = D_N`,
which `QuantDepthElliottGen` / `budget_absorb` already quantify (lap 40).
-/

open Filter Finset Topology

namespace NormalNumbers

namespace CastingOut

/-- **Obligation A (bookkeeping).**  The `K`-fold assembly's log-averaged correlation bound,
along the arithmetic progression `M·X + r`.  `rung_multi_correlation` is the case `M = 1`,
`r = 0`. -/
def ProgressionLogRung (K : ℕ) : Prop :=
  ∀ z : ℕ → ℂ, (∀ i, ‖z i‖ = 1) → z 0 ≠ 1 → ∀ M r : ℕ, 0 < M → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ m ∈ range N, (((m : ℝ) + 1)⁻¹ : ℝ) •
          ∏ i : Fin K, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N

/-- **Obligation B — THE BARRIER.**  Log-averaged `o(log N)` control of a `K`-point correlation
upgraded to natural-density `o(1)`.  This is the *log-Chowla ⇏ Chowla* gap: open already for
`K = 2` and the Liouville function, and the only genuinely open step left in the `D ≥ 2` route
of `ConjC3`. -/
def LogToNaturalCorrelation (K : ℕ) : Prop :=
  ∀ z : ℕ → ℂ, (∀ i, ‖z i‖ = 1) → ∀ M r : ℕ, 0 < M →
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ m ∈ range N, (((m : ℝ) + 1)⁻¹ : ℝ) •
          ∏ i : Fin K, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N) →
    Tendsto (fun J : ℕ =>
        (∑ m ∈ range J, ∏ i : Fin K, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)) / (J : ℂ))
      atTop (𝓝 0)

/-- The cutoff index of the progression `M·X + r` below `N`. -/
private def progIdx (M r N : ℕ) : ℕ := (N - 1 - r) / M + 1

private lemma progIdx_tendsto {M r : ℕ} (hM : 0 < M) :
    Tendsto (fun N => progIdx M r N) atTop atTop := by
  refine tendsto_atTop.2 fun K => eventually_atTop.2 ⟨M * K + r + 1, fun N hN => ?_⟩
  have h1 : M * K ≤ N - 1 - r := by omega
  have h2 : (M * K) / M ≤ (N - 1 - r) / M := Nat.div_le_div_right h1
  rw [Nat.mul_div_cancel_left K hM] at h2
  rw [progIdx]
  exact Nat.le_succ_of_le h2

private lemma progIdx_le {M r N : ℕ} (hM : 0 < M) (hN : 0 < N) : progIdx M r N ≤ N := by
  have h : (N - 1 - r) / M ≤ N - 1 - r := Nat.div_le_self _ _
  rw [progIdx]
  exact Nat.succ_le_of_lt (lt_of_le_of_lt h (by omega))

private lemma progIdx_pos (M r N : ℕ) : 0 < progIdx M r N := by rw [progIdx]; exact Nat.succ_pos _

/-- **The natural-density `D`-point depth rung, at every fixed depth.**  Granting the two named
obligations, the twisted depth-`D` average tends to `0` for every fixed `D`.  This is
`depthAvg_one_tendsto` (Selberg–Delange, `D = 1`) at all `D`. -/
theorem depthAvg_tendsto_of_transfer {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {D : ℕ} (hζ : depthRoot b hh 0 ≠ 1)
    (hrung : ProgressionLogRung D) (htrans : LogToNaturalCorrelation D) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh D N) atTop (𝓝 0) := by
  classical
  set z : ℕ → ℂ := fun i => depthRoot b hh i with hzdef
  have hz : ∀ i, ‖z i‖ = 1 := fun i =>
    show ‖depthRoot b hh i‖ = 1 from by rw [depthRoot]; exact norm_ee_real _
  set M : ℕ := Q * primorial P with hMdef
  have hM0 : 0 < M := Nat.mul_pos hQ (primorial_pos P)
  -- the class sums
  set S : ℕ → ℕ → ℂ := fun r J =>
    ∑ m ∈ range J, ∏ i : Fin D, z i ^ omegaNat (M * m + r + (i : ℕ) + 1) with hSdef
  -- obligation B applied to obligation A
  have htr : ∀ r : ℕ, Tendsto (fun J : ℕ => S r J / (J : ℂ)) atTop (𝓝 0) := fun r =>
    htrans z hz M r hM0 (hrung z hz hζ M r hM0)
  -- the real-valued rate
  set g : ℕ → ℕ → ℝ := fun r J => ‖S r J‖ / (J : ℝ) with hgdef
  have hg : ∀ r : ℕ, Tendsto (fun J : ℕ => g r J) atTop (𝓝 0) := by
    intro r
    have := (htr r).norm
    simp only [norm_zero, norm_div, Complex.norm_natCast] at this
    exact this
  -- composed with the cutoff index
  have hcomp : ∀ r : ℕ, Tendsto (fun N : ℕ => g r (progIdx M r N)) atTop (𝓝 0) := fun r =>
    (hg r).comp (progIdx_tendsto (r := r) hM0)
  have hsum : Tendsto (fun N : ℕ => ∑ r ∈ range M, g r (progIdx M r N)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (range M) (fun r _ => hcomp r)
    simpa using this
  -- the pointwise bound, eventually
  have hbd : ∀ᶠ N : ℕ in atTop,
      ‖depthAvg b P Q j hh D N‖ ≤ ∑ r ∈ range M, g r (progIdx M r N) := by
    refine eventually_atTop.2 ⟨M + 1, fun N hN => ?_⟩
    have hN0 : 0 < N := by omega
    have hNR : (0 : ℝ) < (N : ℝ) := by positivity
    refine le_trans (norm_depthAvg_le_omega_progressions hQ b P j hh D N) ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrN : r < N := by
      have := Finset.mem_range.1 hr
      omega
    have hfil : (range N).filter (fun m => M * m + r < N) = range (progIdx M r N) := by
      rw [progIdx]
      exact filter_linear_lt_eq_range hM0 hrN
    have hJ0 : 0 < progIdx M r N := progIdx_pos M r N
    have hJN : progIdx M r N ≤ N := progIdx_le hM0 hN0
    have hJR : (0 : ℝ) < ((progIdx M r N : ℕ) : ℝ) := by positivity
    have hJNR : ((progIdx M r N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hJN
    have heq : ∑ m ∈ (range N).filter (fun m => M * m + r < N),
        ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (M * m + r + i + 1) = S r (progIdx M r N) := by
      rw [hfil, hSdef]
      exact Finset.sum_congr rfl fun m _ => by
        rw [Fin.prod_univ_eq_prod_range (fun i => z i ^ omegaNat (M * m + r + i + 1)) D]
    rw [heq, hgdef]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hJR hJNR
  exact squeeze_zero_norm' hbd hsum

#print axioms ProgressionLogRung
#print axioms LogToNaturalCorrelation
#print axioms depthAvg_tendsto_of_transfer

end CastingOut

end NormalNumbers
