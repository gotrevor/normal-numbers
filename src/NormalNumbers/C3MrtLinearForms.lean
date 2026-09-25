/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtPowerfulSum

/-!
# From `ζ^ω` along a shift to `ζ^Ω` along linear forms

`C3MrtOmegaBridge` gives `z^{ω} = z^{Ω} ⋆ g` with `g = sqfW z` supported on the powerful
numbers, and `C3MrtPowerfulSum` shows `∑_d ‖g(d)‖/d < ∞`.  This file performs the actual
**substitution**: it rewrites a shifted `ζ^ω` average as a sum, over powerful moduli `d`, of
`ζ^Ω` averages along the **linear form** `k ↦ d k`.

The single-shift statement (`sum_pow_omega_shift_eq`) is

    ∑_{n < N} F(n) · z^{ω(n+1)}
      =  ∑_{d ≤ N}  g(d) · ∑_{1 ≤ k ≤ N/d}  F(dk − 1) · z^{Ω(k)} ,

with `g(d) = (z − z²)^{ω(d)}` on powerful `d` and `0` elsewhere.  The inner sum is a correlation
of the **completely multiplicative** `z^{Ω}` against the weight `F` restricted to the arithmetic
progression `n ≡ −1 (mod d)` — exactly the shape `Erdos67b.NonasymptoticLogElliott` is stated
for.  Taking `F(n) = e(jn/Q) ∏_{i≥1} ζ_i^{ω(n+1+i)}` and iterating over the `D` shifts turns the
`D`-point correlation into a `D`-fold tuple sum of `ζ^Ω` correlations along `D` linear forms;
`C3MrtPowerfulSum.summable_norm_sqfW_div` makes that tuple sum absolutely convergent, hence
truncatable at `d ≤ Y` uniformly in `N`.

The `g`-side is the transpose of the bridge (`pow_omegaNat_eq_sum_divisors'`): it is `g` that
carries the divisor, and `z^{Ω}` that carries the quotient — which is what puts the *linear
form* on the completely multiplicative factor.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **Transposed bridge.**  `z^{ω(m)} = ∑_{d ∣ m} g(d) · z^{Ω(m/d)}` with `g = sqfW z`.
The transpose of `pow_omegaNat_eq_sum_divisors`; this is the orientation in which the
*completely multiplicative* factor receives the quotient `m/d`. -/
theorem pow_omegaNat_eq_sum_divisors' (z : ℂ) {m : ℕ} (hm : m ≠ 0) :
    z ^ omegaNat m = ∑ d ∈ m.divisors, sqfW z d * z ^ ArithmeticFunction.cardFactors (m / d) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f m) (mul_comm (zOm z) (sqfW z) ▸
    zOm_mul_sqfW z)
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y => sqfW z x * zOm z y)] at h
  rw [zom_apply hm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm := Nat.mem_divisors.1 hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hm (Nat.eq_zero_of_zero_dvd hdm.1)
  have hq0 : m / d ≠ 0 := Nat.div_ne_zero_iff.2 ⟨hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm.1⟩
  rw [zOm_apply hq0]

/-- The divisors of `m` with `0 < m ≤ N` all lie in `range (N+1)`. -/
private lemma divisors_subset_range {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    m.divisors ⊆ range (N + 1) := by
  intro d hd
  have := Nat.le_of_dvd hm (Nat.mem_divisors.1 hd).1
  exact Finset.mem_range.2 (by omega)

/-- **Reindexing along the linear form.**  For `d ≥ 1`, the `n < N` with `d ∣ n+1` are exactly
`n = dk − 1` for `1 ≤ k ≤ N/d`. -/
theorem sum_over_progression_eq {d N : ℕ} (hd : 0 < d) (G : ℕ → ℂ) :
    ∑ n ∈ (range N).filter (fun n => d ∣ n + 1), G n
      = ∑ k ∈ Icc 1 (N / d), G (d * k - 1) := by
  refine Finset.sum_nbij' (i := fun n => (n + 1) / d) (j := fun k => d * k - 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hdvd⟩ := hn
    have hk : 1 ≤ (n + 1) / d := Nat.one_le_div_iff hd |>.2 (Nat.le_of_dvd (by omega) hdvd)
    have hk2 : (n + 1) / d ≤ N / d := Nat.div_le_div_right (by omega)
    exact Finset.mem_Icc.2 ⟨hk, hk2⟩
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hkN : d * k ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd).1 hk.2
    have hpos : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne' (by omega))
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : d * k - 1 + 1 = d * k := by omega
    rw [this]
    exact Dvd.intro k rfl
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨k, hk⟩ := hn.2
    rw [hk, Nat.mul_div_cancel_left _ hd]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hpos : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne' (by omega))
    have : d * k - 1 + 1 = d * k := by omega
    rw [this, Nat.mul_div_cancel_left _ hd]
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨k, hk⟩ := hn.2
    have : d * ((n + 1) / d) = n + 1 := by rw [hk, Nat.mul_div_cancel_left _ hd]
    rw [this, Nat.add_sub_cancel]

/-- **The substitution lemma.**  A shifted `z^{ω}` average is a sum, over powerful moduli `d`,
of `z^{Ω}` averages along the linear forms `k ↦ dk`. -/
theorem sum_pow_omega_shift_eq (z : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, F n * z ^ omegaNat (n + 1)
      = ∑ d ∈ range (N + 1),
          sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k := by
  have step1 : ∀ n ∈ range N, F n * z ^ omegaNat (n + 1)
      = ∑ d ∈ range (N + 1),
          (if d ∣ n + 1 then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + 1) / d) else 0)
            * F n := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hm : (n + 1) ≠ 0 := by omega
    have hsub : (n + 1).divisors ⊆ range (N + 1) :=
      divisors_subset_range (by omega) (by omega)
    have hfilter : (range (N + 1)).filter (fun d => d ∣ n + 1) = (n + 1).divisors := by
      ext d
      constructor
      · intro hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.2 ⟨hd.2, hm⟩
      · intro hd
        have hdvd := (Nat.mem_divisors.1 hd).1
        have : d ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hdvd⟩
    rw [← Finset.sum_mul, ← Finset.sum_filter, hfilter,
      pow_omegaNat_eq_sum_divisors' z hm, mul_comm]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp [sqfW]
  · rw [← Finset.sum_filter_add_sum_filter_not (range N) (fun n => d ∣ n + 1)]
    have hzero : ∑ n ∈ (range N).filter (fun n => ¬ d ∣ n + 1),
        (if d ∣ n + 1 then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + 1) / d) else 0)
          * F n = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      rw [if_neg hn.2, zero_mul]
    rw [hzero, add_zero]
    have hcongr : ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
        (if d ∣ n + 1 then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + 1) / d) else 0)
          * F n
        = ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
            sqfW z d * (F n * z ^ ArithmeticFunction.cardFactors ((n + 1) / d)) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_filter] at hn
      rw [if_pos hn.2]; ring
    rw [hcongr, ← Finset.mul_sum]
    congr 1
    rw [sum_over_progression_eq hdpos (fun n => F n * z ^ ArithmeticFunction.cardFactors ((n + 1) / d))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hpos : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hdpos.ne' (by omega))
    have hk1 : d * k - 1 + 1 = d * k := by omega
    rw [hk1, Nat.mul_div_cancel_left _ hdpos]

/-! ### Truncating the modulus at `d ≤ Y`, uniformly in `N` -/

/-- The tail of the bridge weight beyond `Y`. -/
noncomputable def bridgeTail (z : ℂ) (Y : ℕ) : ℝ :=
  ∑' d : {d : ℕ // d ∉ range (Y + 1)}, ‖sqfW z d.val‖ / (d.val : ℝ)

lemma bridgeTail_nonneg (z : ℂ) (Y : ℕ) : 0 ≤ bridgeTail z Y :=
  tsum_nonneg fun _ => by positivity

/-- The tail vanishes as `Y → ∞` (this is where `summable_norm_sqfW_div` is spent). -/
theorem bridgeTail_tendsto (z : ℂ) :
    Filter.Tendsto (bridgeTail z) Filter.atTop (nhds 0) := by
  have hcomp := tendsto_tsum_compl_atTop_zero (fun d : ℕ => ‖sqfW z d‖ / (d : ℝ))
  exact hcomp.comp (Filter.tendsto_finset_range.comp (Filter.tendsto_add_atTop_nat 1))

/-- **Uniform truncation.**  Cutting the modulus at `d ≤ Y` costs at most `N · (tail beyond Y)`,
with a tail independent of `N`.  Together with `bridgeTail_tendsto` this makes the
`ζ^ω → ζ^Ω`-along-linear-forms substitution usable inside a density statement: pick `Y` from
`ε`, then let `N → ∞`. -/
theorem bridge_truncation_bound (z : ℂ) (hz : ‖z‖ = 1) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1)
    (Y N : ℕ) :
    ‖(∑ n ∈ range N, F n * z ^ omegaNat (n + 1))
        - ∑ d ∈ range (Y + 1),
            sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
      ≤ (N : ℝ) * bridgeTail z Y := by
  set T : ℕ → ℂ := fun d =>
    sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k with hT
  set M := max N Y with hM
  rw [sum_pow_omega_shift_eq z F N]
  -- extend the first sum to `range (M+1)`: the new terms vanish
  have hext : ∑ d ∈ range (N + 1), T d = ∑ d ∈ range (M + 1), T d := by
    refine Finset.sum_subset (by
      intro d hd
      rw [Finset.mem_range] at hd ⊢
      omega) ?_
    intro d hd hd'
    rw [Finset.mem_range] at hd hd'
    have hdN : N < d := by omega
    have : N / d = 0 := Nat.div_eq_of_lt hdN
    simp [hT, this]
  have hsubY : range (Y + 1) ⊆ range (M + 1) := by
    intro d hd; rw [Finset.mem_range] at hd ⊢; omega
  have hdiff : (∑ d ∈ range (N + 1), T d) - ∑ d ∈ range (Y + 1), T d
      = ∑ d ∈ range (M + 1) \ range (Y + 1), T d := by
    rw [hext, ← Finset.sum_sdiff hsubY]
    ring
  rw [hdiff]
  -- termwise bound
  have hterm : ∀ d ∈ range (M + 1) \ range (Y + 1),
      ‖T d‖ ≤ (N : ℝ) * (‖sqfW z d‖ / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_range] at hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (Finset.mem_range.2 (by omega)) hd.2
      · exact h
    have hinner : ‖∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
        ≤ ((N / d : ℕ) : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hle : ∀ k ∈ Icc 1 (N / d),
          ‖F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖ ≤ 1 := by
        intro k _
        rw [norm_mul, norm_pow, hz, one_pow, mul_one]
        exact hF _
      calc ∑ k ∈ Icc 1 (N / d), ‖F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
          ≤ ∑ _k ∈ Icc 1 (N / d), (1 : ℝ) := Finset.sum_le_sum hle
        _ = ((N / d : ℕ) : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc]
            simp
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    calc ‖T d‖ = ‖sqfW z d‖ *
          ‖∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖ := by
          rw [hT, norm_mul]
      _ ≤ ‖sqfW z d‖ * ((N : ℝ) / (d : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (hinner.trans hdiv) (norm_nonneg _)
      _ = (N : ℝ) * (‖sqfW z d‖ / (d : ℝ)) := by ring
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  -- compare the finite sum with the tail tsum
  have hsummable : Summable fun d : {d : ℕ // d ∉ range (Y + 1)} => ‖sqfW z d.val‖ / (d.val : ℝ) :=
    (summable_norm_sqfW_div z hz).subtype _
  classical
  have hfilter : (range (M + 1) \ range (Y + 1)).filter (fun d => d ∉ range (Y + 1))
      = range (M + 1) \ range (Y + 1) :=
    Finset.filter_true_of_mem (fun d hd => (Finset.mem_sdiff.1 hd).2)
  have hsub := Finset.sum_subtype_eq_sum_filter (s := range (M + 1) \ range (Y + 1))
      (p := fun d : ℕ => d ∉ range (Y + 1)) (f := fun d : ℕ => ‖sqfW z d‖ / (d : ℝ))
  rw [hfilter] at hsub
  rw [← hsub]
  exact hsummable.sum_le_tsum _ (fun _ _ => by positivity)

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.sum_pow_omega_shift_eq
#print axioms NormalNumbers.CastingOut.bridge_truncation_bound
#print axioms NormalNumbers.CastingOut.bridgeTail_tendsto
