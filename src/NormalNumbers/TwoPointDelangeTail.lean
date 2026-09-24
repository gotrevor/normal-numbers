import NormalNumbers.TwoPointDelange
import NormalNumbers.TwoPointTuranKubilius

/-!
# `DelangeKernelTail` for `‖z − 1‖ < 1`, unconditionally

The `ℓ¹` residue of the Delange decomposition (`TwoPointDelange.lean`) is

    (1/N) Σ_{n ≤ N} ‖h_z(n)‖  =  (1/N) Σ_{n ≤ N} μ²(n) u^{ω(n)},   u := ‖z − 1‖ .

For `u < 1` this is `o(1)` by a two-line elementary argument with no analytic input beyond
Mertens' divergence of `Σ 1/p`:

* **truncation**: `u^{ω(n)} ≤ u^{K+1} + [ω(n) ≤ K]` for every `K` (if `ω(n) ≤ K` the indicator
  already pays `1 ≥ u^{ω(n)}`; otherwise `ω(n) ≥ K+1` and `u^{ω(n)} ≤ u^{K+1}`);
* **rarity of small `ω`**: `#{n ≤ N : ω(n) ≤ K} ≤ 8N/L(w)` whenever `2K ≤ L(w)`, by Chebyshev on
  the in-kernel `turanKubilius` variance bound `Σ_{n ≤ N} (ω_w(n) − L(w))² ≤ 2 N L(w)`, using
  `ω_w(n) ≤ ω(n)` (`kataiOmega_le_omegaNat`).

Given `ε`, pick `K` with `u^{K+1} < ε/2` and then `w` with `L(w) > max(2K, 16/ε)`: Mertens
supplies it.  This discharges `DelangeKernelTail` for all `z` on the unit circle with
`‖z − 1‖ < 1`, i.e. `‖t‖_{ℝ/ℤ} < 1/6` — half of the elementary discharge of the `DelangeMean`
axiom (`delangeMean_of_kernel`); the other half is `DelangeKernelMean`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The truncated prime-divisor count never exceeds the full one. -/
lemma kataiOmega_le_omegaNat (w n : ℕ) (hn : n ≠ 0) : kataiOmega w n ≤ omegaNat n := by
  classical
  refine Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact Nat.mem_primeFactors.mpr ⟨prime_of_mem_primesLe hp.1, hp.2, hn⟩

/-- **Chebyshev on Turán–Kubilius.**  If `2K ≤ L(w)` and `2π(w) ≤ N` then integers with at most
`K` prime factors are rare: their count is at most `8N/L(w)`. -/
lemma card_small_omega_le (w N K : ℕ) (hN : 2 * (primesLe w).card ≤ N)
    (hK : 2 * (K : ℝ) ≤ kataiPrimeRecip w) :
    (((Finset.Ioc 0 N).filter (fun n => omegaNat n ≤ K)).card : ℝ)
      * (kataiPrimeRecip w / 2) ^ 2 ≤ 2 * (N : ℝ) * kataiPrimeRecip w := by
  classical
  set L : ℝ := kataiPrimeRecip w with hLdef
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun p _ => by positivity
  set S := (Finset.Ioc 0 N).filter (fun n => omegaNat n ≤ K) with hSdef
  have hpt : ∀ n ∈ S, (L / 2) ^ 2 ≤ ((kataiOmega w n : ℝ) - L) ^ 2 := by
    intro n hn
    simp only [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hn
    have hn0 : n ≠ 0 := by omega
    have h1 : (kataiOmega w n : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast le_trans (kataiOmega_le_omegaNat w n hn0) hn.2
    have h2 : (kataiOmega w n : ℝ) ≤ L / 2 := by linarith
    have h3 : (0 : ℝ) ≤ (kataiOmega w n : ℝ) := Nat.cast_nonneg _
    nlinarith [h2, h3]
  calc (S.card : ℝ) * (L / 2) ^ 2 = ∑ _n ∈ S, (L / 2) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ S, ((kataiOmega w n : ℝ) - L) ^ 2 := Finset.sum_le_sum hpt
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, ((kataiOmega w n : ℝ) - L) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => by positivity)
    _ ≤ 2 * (N : ℝ) * L := turanKubilius w N hN

/-- The pointwise truncation `u^{ω(n)} ≤ u^{K+1} + [ω(n) ≤ K]` for `0 ≤ u ≤ 1`. -/
lemma pow_omega_le_trunc {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (K n : ℕ) :
    u ^ omegaNat n ≤ u ^ (K + 1) + (if omegaNat n ≤ K then (1 : ℝ) else 0) := by
  by_cases h : omegaNat n ≤ K
  · simp only [h, if_true]
    have : u ^ omegaNat n ≤ 1 := pow_le_one₀ hu0 hu1
    have : (0 : ℝ) ≤ u ^ (K + 1) := by positivity
    linarith [pow_le_one₀ hu0 hu1 (n := omegaNat n)]
  · simp only [h, if_false, add_zero]
    exact pow_le_pow_of_le_one hu0 hu1 (by omega)

/-- **The `ℓ¹` bound.**  For `u = ‖z − 1‖ ≤ 1`, every `K`, and every `w` with `2K ≤ L(w)` and
`2π(w) ≤ N`, the kernel mass is at most `N u^{K+1} + 8N/L(w)`. -/
lemma sum_norm_delangeKernel_le (z : ℂ) (hu1 : ‖z - 1‖ ≤ 1) (w N K : ℕ)
    (hN : 2 * (primesLe w).card ≤ N) (hL : 0 < kataiPrimeRecip w)
    (hK : 2 * (K : ℝ) ≤ kataiPrimeRecip w) :
    ∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖
      ≤ (N : ℝ) * ‖z - 1‖ ^ (K + 1) + 8 * (N : ℝ) / kataiPrimeRecip w := by
  classical
  set u : ℝ := ‖z - 1‖ with hudef
  have hu0 : 0 ≤ u := norm_nonneg _
  set L : ℝ := kataiPrimeRecip w with hLdef
  set S := (Finset.Ioc 0 N).filter (fun n => omegaNat n ≤ K) with hSdef
  have hstep : ∀ n ∈ Finset.Ioc 0 N,
      ‖delangeKernel z n‖ ≤ u ^ (K + 1) + (if omegaNat n ≤ K then (1 : ℝ) else 0) := by
    intro n _
    refine le_trans ?_ (pow_omega_le_trunc hu0 hu1 K n)
    rw [norm_delangeKernel]
    split
    · exact le_rfl
    · positivity
  have hsum : ∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖
      ≤ (N : ℝ) * u ^ (K + 1) + (S.card : ℝ) := by
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_filter]
    simp [hSdef, Nat.card_Ioc, mul_comm]
  have hcard : (S.card : ℝ) ≤ 8 * (N : ℝ) / L := by
    have h := card_small_omega_le w N K hN hK
    rw [← hLdef, ← hSdef] at h
    rw [le_div_iff₀ hL]
    nlinarith [h, hL]
  linarith [hsum, hcard]

/-- **`DelangeKernelTail` holds whenever `‖z − 1‖ < 1`** — no analytic input beyond Mertens. -/
theorem delangeKernelTail_of_norm_lt_one (z : ℂ) (hz : ‖z - 1‖ < 1) :
    DelangeKernelTail z := by
  classical
  set u : ℝ := ‖z - 1‖ with hudef
  have hu0 : 0 ≤ u := norm_nonneg _
  rw [DelangeKernelTail, Metric.tendsto_atTop]
  intro ε hε
  -- pick `K` with `u^{K+1} < ε/2`
  obtain ⟨K₀, hK₀⟩ : ∃ n : ℕ, u ^ n < ε / 2 := exists_pow_lt_of_lt_one (by linarith) hz
  refine ?_
  set K : ℕ := K₀ with hKdef
  -- pick `w` with `L(w) > max (2K) (16/ε)`
  obtain ⟨w, hw⟩ : ∃ w : ℕ, max (2 * (K : ℝ)) (16 / ε) < kataiPrimeRecip w :=
    (tendsto_kataiPrimeRecip.eventually_gt_atTop (max (2 * (K : ℝ)) (16 / ε))).exists
  have hK : 2 * (K : ℝ) ≤ kataiPrimeRecip w := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hw)
  have hLbig : 16 / ε < kataiPrimeRecip w := lt_of_le_of_lt (le_max_right _ _) hw
  have hL : 0 < kataiPrimeRecip w := lt_of_le_of_lt (by positivity) hLbig
  refine ⟨max 1 (2 * (primesLe w).card), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 * (primesLe w).card ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hnn : 0 ≤ (∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖) / (N : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun n _ => norm_nonneg _) hNR.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ hNR]
  have hbd := sum_norm_delangeKernel_le z (le_of_lt hz) w N K hN2 hL hK
  rw [← hudef] at hbd
  have hpow : u ^ (K + 1) ≤ u ^ K := pow_le_pow_of_le_one hu0 (le_of_lt hz) (by omega)
  have h1 : (N : ℝ) * u ^ (K + 1) < (N : ℝ) * (ε / 2) := by
    nlinarith [hNR, hpow, hK₀]
  have h2 : 8 * (N : ℝ) / kataiPrimeRecip w < (N : ℝ) * (ε / 2) := by
    rw [div_lt_iff₀ hL]
    have hmul : 16 / ε * ε < kataiPrimeRecip w * ε := by nlinarith [hLbig, hε]
    rw [div_mul_cancel₀ _ (ne_of_gt hε)] at hmul
    have this := hmul
    nlinarith [this, hNR]
  linarith [hbd, h1, h2]

/-- **Half the elementary discharge.**  In the range `‖phase t − 1‖ < 1` the `DelangeMean` axiom
now rests on the single residue `DelangeKernelMean` — the tail is a theorem. -/
theorem delangeMean_of_kernelMean (t : ℝ) (ht : ‖phase t - 1‖ < 1)
    (hM : DelangeKernelMean (phase t)) : DelangeMean t :=
  delangeMean_of_kernel t hM (delangeKernelTail_of_norm_lt_one _ ht)

end NormalNumbers.CastingOut
