/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtShape
import NormalNumbers.PairDecoupleMertens

/-!
# The deep tail on AVERAGE: the required depth drops from `log log N` to `log log log N`

`C3MrtShape` priced the depth-`D` truncation **pointwise**, at `(log₂ n + D + 1)/((b−2)b^D)`,
and so needed a depth schedule with `b^{D_N} ≳ log N`, i.e. `D_N ≍ log_b log N` correlation
points.  But only the *mean* of the discarded phase is ever spent, and the mean of `ω` is
`log log`, not `log`:

    tailLarge P b n − tailDepth P b D n ≤ omegaTail b (n+D) / b^D      (pointwise, exact shape)
    (1/N) ∑_{n<N} omegaTail b (n+D)     ≤ 4 log(log₂ N) + 11           (repo Mertens)

so the mean discarded phase is `≪ log log N / b^D`.  Hence a schedule with
`b^{D_N} ≳ log log N` suffices, i.e.

> **`D_N ≍ log_b log log N` correlation points are enough.**

`weylLambertTwist_of_schedule` is the resulting reduction, parametric in the schedule; it
subsumes `weylLambertTwist_of_depthElliott`.

The Mertens input is `PairDecouple.sum_omegaTail_AP_le'` (already proved in this repo).
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

lemma omegaLarge_le_omegaNat (P m : ℕ) : omegaLarge P m ≤ omegaNat m :=
  Finset.card_filter_le _ _

/-- **The deep tail, in `omegaTail` form.**  Discarding digit depths `≥ D` costs at most
`b^{−D}` times the full carry tail at `n + D`. -/
theorem tailLarge_sub_tailDepth_le_omegaTail {b : ℕ} (hb : 2 ≤ b) (P D n : ℕ) :
    tailLarge P b n - tailDepth P b D n ≤ omegaTail b (n + D) / (b : ℝ) ^ D := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hLsum : Summable (fun i : ℕ =>
      (omegaLarge P (n + (i + D) + 1) : ℝ) / (b : ℝ) ^ ((i + D) + 1)) := by
    have := (summable_nat_add_iff D).2 (summable_tailLarge hb P n)
    exact this.congr fun i => by ring_nf
  have hRsum : Summable (fun k : ℕ =>
      (omegaNat (n + D + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) / (b : ℝ) ^ D) :=
    (summable_omegaTail b hb (n + D)).div_const _
  have hRtsum : omegaTail b (n + D) / (b : ℝ) ^ D
      = ∑' k : ℕ, (omegaNat (n + D + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) / (b : ℝ) ^ D := by
    rw [omegaTail, ← tsum_div_const]
  rw [tailLarge_sub_tailDepth_eq hb P D n, hRtsum]
  refine hLsum.tsum_le_tsum (fun i => ?_) hRsum
  have harg : n + (i + D) + 1 = n + D + 1 + i := by omega
  have hden : (b : ℝ) ^ ((i + D) + 1) = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ D := by
    rw [← pow_add]; ring_nf
  rw [harg, hden, div_div]
  gcongr
  exact_mod_cast omegaLarge_le_omegaNat P _

/-- `LL N = 4 log(log₂ N) + 11`: the repo's Mertens bound on the mean of `omegaTail`. -/
noncomputable def LLbound (N : ℕ) : ℝ := 4 * Real.log (Nat.log 2 N) + 11

/-- **The deep tail on average.**  Mertens, via `PairDecouple.sum_omegaTail_AP_le'`. -/
theorem sum_range_deep_le {b : ℕ} (hb : 2 ≤ b) (P D N : ℕ) (hN : D + 3 ≤ N) :
    ∑ n ∈ range N, (tailLarge P b n - tailDepth P b D n)
      ≤ (N : ℝ) * LLbound N / (b : ℝ) ^ D := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := by positivity
  have hmert := PairDecouple.sum_omegaTail_AP_le' b 1 D N hb one_ne_zero (by omega)
  have hone : omegaNat 1 = 0 := by simp [omegaNat]
  have hstep : ∑ n ∈ range N, (tailLarge P b n - tailDepth P b D n)
      ≤ (∑ n ∈ range N, omegaTail b (n + D)) / (b : ℝ) ^ D := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun n _ => tailLarge_sub_tailDepth_le_omegaTail hb P D n
  refine hstep.trans ?_
  have hre : ∑ n ∈ range N, omegaTail b (n + D) = ∑ i ∈ range N, omegaTail b (1 * i + D) :=
    Finset.sum_congr rfl fun i _ => by rw [one_mul]
  rw [hre]
  refine (div_le_div_iff_of_pos_right hbD).2 ?_
  rw [LLbound]
  calc ∑ i ∈ range N, omegaTail b (1 * i + D)
      ≤ (N : ℝ) * (4 * Real.log (Nat.log 2 N) + 11 + (omegaNat 1 : ℝ)) := hmert
    _ = (N : ℝ) * (4 * Real.log (Nat.log 2 N) + 11) := by rw [hone]; push_cast; ring

/-! ### The reduction, parametric in the depth schedule -/

/-- **The sharpened reduction.**  Any depth schedule `Dsch` along which
(i) the twisted `Dsch N`-point correlations tend to `0`, and
(ii) the *mean* discarded phase `LL(N)/b^{Dsch N}` tends to `0`,
closes the C3 crux.  Since `LL(N) ≍ log log N`, (ii) needs only `b^{Dsch N} ≳ log log N`, i.e.
`Dsch N ≍ log_b log log N` correlation points — one `log` better than
`weylLambertTwist_of_depthElliott`, which spent the pointwise bound `log N / b^D`. -/
theorem weylLambertTwist_of_schedule {b : ℕ} (hb : 3 ≤ b) (Dsch : ℕ → ℕ)
    (hgrow : ∀ᶠ N : ℕ in atTop, Dsch N + 3 ≤ N)
    (hmean : Tendsto (fun N : ℕ => LLbound N / (b : ℝ) ^ Dsch N) atTop (𝓝 0))
    (H : ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
      Tendsto (fun N : ℕ => depthAvg b P Q j h (Dsch N) N) atTop (𝓝 0)) :
    WeylLambertTwist b := by
  intro P Q j h hQ hj0 hjQ
  have hb2 : 2 ≤ b := by omega
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set A : ℕ → ℂ := fun N => (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
    * ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))) / N with hA
  have hnorm : ∀ᶠ N : ℕ in atTop, ‖A N - depthAvg b P Q j h (Dsch N) N‖
      ≤ 16 * |(h : ℝ)| * (LLbound N / (b : ℝ) ^ Dsch N) := by
    filter_upwards [hgrow, eventually_gt_atTop 0] with N hN hN0
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    have hsub : A N - depthAvg b P Q j h (Dsch N) N
        = (∑ n ∈ range N, (ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * (ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))
              - ee ((((h : ℝ) * tailDepth P b (Dsch N) n : ℝ) : ℂ))))) / N := by
      rw [hA, depthAvg, div_sub_div_same]
      congr 1
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by rw [mul_sub]
    rw [hsub, norm_div, Complex.norm_natCast, div_le_iff₀ hNR]
    calc ‖∑ n ∈ range N, (ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * (ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))
              - ee ((((h : ℝ) * tailDepth P b (Dsch N) n : ℝ) : ℂ))))‖
        ≤ ∑ n ∈ range N, 16 * |(h : ℝ)|
            * (tailLarge P b n - tailDepth P b (Dsch N) n) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_mul, norm_ee_real, one_mul]
          refine (norm_ee_sub_ee_le _ _).trans ?_
          have hnn := tailLarge_sub_tailDepth_nonneg hb2 P (Dsch N) n
          have habs : |(h : ℝ) * tailLarge P b n
              - (h : ℝ) * tailDepth P b (Dsch N) n|
              = |(h : ℝ)| * (tailLarge P b n - tailDepth P b (Dsch N) n) := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
          rw [habs]; ring_nf; exact le_rfl
      _ = 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailDepth P b (Dsch N) n) := by
          rw [Finset.mul_sum]
      _ ≤ 16 * |(h : ℝ)| * ((N : ℝ) * LLbound N / (b : ℝ) ^ Dsch N) := by
          refine mul_le_mul_of_nonneg_left (sum_range_deep_le hb2 P (Dsch N) N hN) (by positivity)
      _ = 16 * |(h : ℝ)| * (LLbound N / (b : ℝ) ^ Dsch N) * N := by ring
  have hdiff : Tendsto (fun N : ℕ => A N - depthAvg b P Q j h (Dsch N) N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' hnorm ?_
    simpa using hmean.const_mul (16 * |(h : ℝ)|)
  have hAt : Tendsto A atTop (𝓝 0) := by
    have := hdiff.add (H P Q j h hQ hj0 hjQ)
    simpa using this
  refine hAt.congr fun N => ?_
  simp only [hA]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [ee_tailLarge_eq_ee_orbit hb2 P n h]

end CastingOut

end NormalNumbers
