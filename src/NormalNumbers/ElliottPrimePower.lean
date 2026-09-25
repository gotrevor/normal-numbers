import NormalNumbers.ElliottDamped

/-!
# The prime-power correction (lap 109)

The slice `logWeightedSlice` runs over *primes*; the von Mangoldt series `−ζ'/ζ(s)` runs over all
prime powers.  The difference is the `j ≥ 2` part, and it is `O(1)` uniformly for `Re s ≥ 1` with no
cancellation at all:

  `∑_{p, j≥2} log p · p^{-σj} ≤ ∑_p log p · p^{-2}·2·... ≤ 16·∑_n n^{-3/2}`.

This file proves the estimate in the shape the bridge needs: a bound on any **finite set of pairs**
`(m, j)` with `m, j ≥ 2`, so that the eventual map `n = p^j ↦ (p, j)` can be an arbitrary injection
and no grouping by `p` is required.  The trick that removes the grouping is to majorize the term by a
*product* `a_m · b_j` and then use `F ⊆ (image fst) ×ˢ (image snd)`.
-/

open Finset

namespace NormalNumbers.ElliottPrimePower

open NormalNumbers.ElliottDamped

noncomputable section

/-- The absolute cost of the prime powers. -/
noncomputable def ppCost : ℝ := 16 * pSeriesThreeHalves

theorem ppCost_nonneg : 0 ≤ ppCost := by
  have := pSeriesThreeHalves_nonneg
  rw [ppCost]; linarith

/-- `∑_{m ∈ S, m ≥ 2} log m · m^{-2} ≤ 2·∑_n n^{-3/2}`. -/
theorem sum_log_mul_rpow_neg_two_le {S : Finset ℕ} (hS : ∀ m ∈ S, 2 ≤ m) :
    ∑ m ∈ S, Real.log (m : ℝ) * (m : ℝ) ^ (-2 : ℝ) ≤ 2 * pSeriesThreeHalves := by
  have hterm : ∀ m ∈ S, Real.log (m : ℝ) * (m : ℝ) ^ (-2 : ℝ)
      ≤ 2 * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    intro m hm
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hS m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hlog := log_le_two_mul_rpow_half hm1
    have hcomb : (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (-2 : ℝ) = ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_add hm0, ← Real.rpow_neg hm0.le]
      congr 1
      ring
    calc Real.log (m : ℝ) * (m : ℝ) ^ (-2 : ℝ)
        ≤ (2 * (m : ℝ) ^ (1 / 2 : ℝ)) * (m : ℝ) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = 2 * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [← hcomb]; ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ m ∈ S, ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤ pSeriesThreeHalves := by
    rw [pSeriesThreeHalves]
    refine Summable.sum_le_tsum S (fun n _ => by positivity) ?_
    simpa [pSeriesThreeHalves] using summable_pSeriesThreeHalves
  linarith

/-- `∑_{j ∈ T} (1/2)^j ≤ 2`. -/
theorem sum_half_pow_le (T : Finset ℕ) :
    ∑ j ∈ T, (1 / 2 : ℝ) ^ j ≤ 2 := by
  have hsummable : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := Summable.sum_le_tsum T (fun j _ => by positivity) hsummable
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  norm_num at h
  linarith

/-- **THE PRIME-POWER CORRECTION.**  Any finite set of pairs `(m, j)` with `m, j ≥ 2` contributes at
most `ppCost`, uniformly in `σ ≥ 1`.  No grouping by `m`: the term is majorized by a product
`a_m·b_j` and `F ⊆ (image fst) ×ˢ (image snd)`. -/
theorem sum_pairs_le {F : Finset (ℕ × ℕ)} (hF : ∀ q ∈ F, 2 ≤ q.1 ∧ 2 ≤ q.2) {σ : ℝ} (hσ : 1 ≤ σ) :
    ∑ q ∈ F, Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-(σ * q.2)) ≤ ppCost := by
  classical
  set A : Finset ℕ := F.image Prod.fst with hA
  set B : Finset ℕ := F.image Prod.snd with hB
  -- majorize each term by a product
  have hterm : ∀ q ∈ F,
      Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-(σ * q.2))
        ≤ (Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-2 : ℝ)) * (4 * (1 / 2 : ℝ) ^ q.2) := by
    intro q hq
    obtain ⟨hm, hj⟩ := hF q hq
    have hm2 : (2 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ (q.1 : ℝ) := by linarith
    have hm0 : (0 : ℝ) < (q.1 : ℝ) := by linarith
    have hjR : (2 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast hj
    have hlog : 0 ≤ Real.log (q.1 : ℝ) := Real.log_nonneg hm1
    -- `m^{-σj} ≤ m^{-j} = m^{-2}·m^{-(j-2)} ≤ m^{-2}·2^{-(j-2)}`
    have h1 : (q.1 : ℝ) ^ (-(σ * q.2)) ≤ (q.1 : ℝ) ^ (-(q.2 : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
      nlinarith
    have h2 : (q.1 : ℝ) ^ (-(q.2 : ℝ))
        = (q.1 : ℝ) ^ (-2 : ℝ) * (q.1 : ℝ) ^ (-((q.2 : ℝ) - 2)) := by
      rw [← Real.rpow_add hm0]
      congr 1
      ring
    have h3 : (q.1 : ℝ) ^ (-((q.2 : ℝ) - 2)) ≤ (2 : ℝ) ^ (-((q.2 : ℝ) - 2)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hm2 (by linarith)
    have h4 : (2 : ℝ) ^ (-((q.2 : ℝ) - 2)) = 4 * (1 / 2 : ℝ) ^ q.2 := by
      have e1 : (2 : ℝ) ^ (-((q.2 : ℝ) - 2)) = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (-(q.2 : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      have e2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      have e3 : (2 : ℝ) ^ (-(q.2 : ℝ)) = (1 / 2 : ℝ) ^ q.2 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [e1, e2, e3]
    have hpow_nonneg : (0 : ℝ) ≤ (q.1 : ℝ) ^ (-2 : ℝ) := by positivity
    calc Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-(σ * q.2))
        ≤ Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-(q.2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h1 hlog
      _ = Real.log (q.1 : ℝ) * ((q.1 : ℝ) ^ (-2 : ℝ) * (q.1 : ℝ) ^ (-((q.2 : ℝ) - 2))) := by
          rw [h2]
      _ ≤ Real.log (q.1 : ℝ) * ((q.1 : ℝ) ^ (-2 : ℝ) * (2 : ℝ) ^ (-((q.2 : ℝ) - 2))) := by
          have := mul_le_mul_of_nonneg_left h3 hpow_nonneg
          exact mul_le_mul_of_nonneg_left this hlog
      _ = (Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-2 : ℝ)) * (4 * (1 / 2 : ℝ) ^ q.2) := by
          rw [h4]; ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- enlarge to the product set
  have hsubset : F ⊆ A ×ˢ B := by
    intro q hq
    rw [Finset.mem_product, hA, hB]
    exact ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
  have hnonneg : ∀ q ∈ A ×ˢ B, q ∉ F →
      0 ≤ (Real.log (q.1 : ℝ) * (q.1 : ℝ) ^ (-2 : ℝ)) * (4 * (1 / 2 : ℝ) ^ q.2) := by
    intro q hq _
    rcases Nat.eq_zero_or_pos q.1 with h0 | h0
    · simp [h0]
    · have : (1 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast h0
      have hlog : 0 ≤ Real.log (q.1 : ℝ) := Real.log_nonneg this
      positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg) ?_
  rw [Finset.sum_product]
  have hfactor : ∑ m ∈ A, ∑ j ∈ B,
      (Real.log (m : ℝ) * (m : ℝ) ^ (-2 : ℝ)) * (4 * (1 / 2 : ℝ) ^ j)
      = (∑ m ∈ A, Real.log (m : ℝ) * (m : ℝ) ^ (-2 : ℝ))
        * (4 * ∑ j ∈ B, (1 / 2 : ℝ) ^ j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hfactor]
  have hA2 : ∀ m ∈ A, 2 ≤ m := by
    intro m hm
    rw [hA, Finset.mem_image] at hm
    obtain ⟨q, hq, rfl⟩ := hm
    exact (hF q hq).1
  have h1 := sum_log_mul_rpow_neg_two_le hA2
  have h2 := sum_half_pow_le B
  have hAnn : 0 ≤ ∑ m ∈ A, Real.log (m : ℝ) * (m : ℝ) ^ (-2 : ℝ) := by
    refine Finset.sum_nonneg (fun m hm => ?_)
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hA2 m hm
    have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
    positivity
  have hBnn : 0 ≤ ∑ j ∈ B, (1 / 2 : ℝ) ^ j :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hps := pSeriesThreeHalves_nonneg
  rw [ppCost]
  nlinarith [h1, h2, hAnn, hBnn]

end

end NormalNumbers.ElliottPrimePower
