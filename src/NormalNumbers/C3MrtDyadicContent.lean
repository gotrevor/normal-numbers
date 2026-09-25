/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtDyadicInput

/-!
# Where `DepthDyadicBound` actually has content

Lap 96 reduced `ConjC3` to the explicit inequality `DepthDyadicBound`.  Before attacking that
inequality it is worth knowing exactly which of its instances are assumptions and which are
theorems — otherwise one may "prove" the crux on its trivial range, or, worse, the ledger may be
overstating what is assumed.

Write the **saving factor** of an instance as

    dyadicFactor CstK cK κ K N = CstK K · (2 log N)^{-κ·cK K} .

*   `dyadic_ineq_of_trivial` — if `M ≤ dyadicFactor …` the asserted inequality is a THEOREM,
    proved from `‖∑‖ ≤ #(Ioc N (2N)) = N` alone.  In particular every instance with
    `dyadicFactor ≥ 1` is free, since `M ≥ 1`.  So the content of `DepthDyadicBound` lives
    entirely in the range `M > dyadicFactor`, and a fortiori needs `dyadicFactor < M ≤
    (2 log N)^{κ·cK K}`.
*   `dyadicFactor_ge_one_of_small_scale` — for EVERY `K` the trivial range is non-empty among the
    admissible `N`: taking `N` just past the threshold leaves `dyadicFactor ≥ 1`, because the
    threshold only forces `log(K+1) ≤ κ cK K · log(2 log N)` while triviality needs the weaker
    `log CstK K ≤ κ cK K · log(2 log N)` to FAIL.  So `DepthDyadicBound` is not a uniformly
    content-bearing statement; its strength is concentrated at large `N` for each `K`.
*   `dyadicFactor_tendsto_zero_at_diagonal` — and the chain uses exactly that regime: along the
    diagonal `K = KN N ≤ depthSlow b N` with the geometric profile and `θ < 1`, the saving factor
    tends to `0`.  So the input is being assumed precisely where it asserts genuine cancellation,
    and the reduction is not smuggling its conclusion out of a trivial range.

Together these two say the ledger reading is honest: `DepthDyadicBound` is neither vacuous nor
trivially true where it is consumed.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- The saving factor asserted by one instance of `DepthDyadicBound`. -/
noncomputable def dyadicFactor (cK CstK : ℕ → ℝ) (κ : ℝ) (K N : ℕ) : ℝ :=
  CstK K * (2 * Real.log N) ^ (-(κ * cK K))

open scoped Classical in
/-- **The trivial range of the crux.**  When the modulus is below the saving factor the asserted
inequality follows from the trivial estimate `‖∑‖ ≤ #(Ioc N (2N)) = N`; no cancellation is being
claimed.  (No unimodularity is even needed beyond `‖·‖ ≤ 1` per factor.) -/
theorem dyadic_ineq_of_trivial {cK CstK : ℕ → ℝ} {κ : ℝ} {b : ℕ} {h' : ℤ} {K N M r : ℕ}
    (hM : 0 < M) (htriv : (M : ℝ) ≤ dyadicFactor cK CstK κ K N) :
    ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1)‖
      ≤ dyadicFactor cK CstK κ K N * (N : ℝ) / (M : ℝ) := by
  classical
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hz : ∀ i, ‖depthRoot b h' i‖ = 1 := fun i => by rw [depthRoot]; exact norm_ee_real _
  -- every summand is unimodular, so the norm is at most the cardinality
  have hcard : ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1)‖ ≤ (N : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
        ‖∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ ∑ _n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M), (1 : ℝ) := by
      refine Finset.sum_le_sum fun n _ => ?_
      simp only [norm_prod, norm_pow]
      have hone : ∀ i : Fin K, ‖depthRoot b h' i‖ ^ omegaNat (n + (i : ℕ) + 1) = 1 :=
        fun i => by rw [hz i, one_pow]
      rw [Finset.prod_congr rfl (fun i _ => hone i), Finset.prod_const_one]
    refine le_trans h1 ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc := Finset.card_filter_le (Finset.Ioc N (2 * N)) (fun n => n % M = r % M)
    rw [Nat.card_Ioc, show 2 * N - N = N by omega] at hc
    exact_mod_cast hc
  refine le_trans hcard ?_
  rw [le_div_iff₀ hMR]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [htriv, hN0]

/-- **For every `K` the trivial range is non-empty among the admissible `N`.**  If
`CstK K ≥ (2 log N)^{κ·cK K}` — which the threshold hypothesis does NOT rule out, since it only
demands `K + 1 ≤ (2 log N)^{κ·cK K}` — then `dyadicFactor ≥ 1`, hence the instance is free by
`dyadic_ineq_of_trivial`.  So the strength of `DepthDyadicBound` at a given `K` is concentrated
at large `N`, not spread over the whole admissible range. -/
theorem dyadicFactor_ge_one_of_small_scale {cK CstK : ℕ → ℝ} {κ : ℝ} {K N : ℕ}
    (hN : 2 ≤ N) (hC : (2 * Real.log N) ^ (κ * cK K) ≤ CstK K) :
    1 ≤ dyadicFactor cK CstK κ K N := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hbase : (0 : ℝ) < 2 * Real.log N := by linarith
  have hpos : (0 : ℝ) < (2 * Real.log N) ^ (κ * cK K) := Real.rpow_pos_of_pos hbase _
  rw [dyadicFactor, Real.rpow_neg hbase.le, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact hC

/-- **The chain consumes the crux exactly where it asserts real cancellation.**  Along the
diagonal `K = KN N ≤ depthSlow b N`, with the geometric profile and `θ < 1`, the saving factor
tends to `0` — so no instance used by the reduction lies in the trivial range of
`dyadic_ineq_of_trivial` beyond finitely many `N`. -/
theorem dyadicFactor_tendsto_zero_at_diagonal {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) {κ : ℝ} (hκ : 0 < κ) (m : ℕ)
    (KN : ℕ → ℕ) (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N) :
    Tendsto (fun N : ℕ => dyadicFactor (cKgeom c₀ θ b) (CstKdeg m) κ (KN N)
        (N / 2 ^ (Nat.log 2 (Nat.log 2 N)))) atTop (𝓝 0) := by
  have hbase : ∀ᶠ N : ℕ in atTop,
      0 < 2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) := by
    filter_upwards [tendsto_cut_atTop.eventually_ge_atTop 2] with N hN
    have h2 : (2 : ℝ) ≤ ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    linarith
  have h := rate_tendsto_of_exponent (cK := cKgeom c₀ θ b) (CstK := CstKdeg m)
    (fun K => CstKdeg_pos m K) (κ := κ) (M₀ := 1) KN
    (fun N => N / 2 ^ (Nat.log 2 (Nat.log 2 N))) hbase
    (exponent_tendsto_atBot_of_geom_slow hb hc₀ hθ0 hθ hκ m KN hKle)
  simpa [dyadicFactor] using h

#print axioms NormalNumbers.CastingOut.dyadic_ineq_of_trivial
#print axioms NormalNumbers.CastingOut.dyadicFactor_ge_one_of_small_scale
#print axioms NormalNumbers.CastingOut.dyadicFactor_tendsto_zero_at_diagonal

end CastingOut

end NormalNumbers
