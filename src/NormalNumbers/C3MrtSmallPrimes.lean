/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTwist
import Mathlib.NumberTheory.Primorial

/-!
# The small primes cost only a period, too

`norm_depthAvg_le_progressions` (lap 53) removed the additive twist `e(jn/Q)` but left
`ω_{>P}`, the count of prime factors `> P`.  The `K`-fold assembly
(`rung_multi_correlation`) bounds correlations of `z^{ω}` — the FULL `ω`.  This file removes the
difference.

**Insight.**  `ω = ω_{≤P} + ω_{>P}`, so with `ζ` on the unit circle

    ζ^{ω_{>P}(m)} = ζ^{ω(m)} · conj(ζ)^{ω_{≤P}(m)} ,

and `ω_{≤P}` is `primorial P`-periodic in `m` (for `m ≠ 0`): `p ∣ m` for a prime `p ≤ P` is
decided by `m mod primorial P`.  So the whole small-prime discrepancy is a **unimodular
`primorial P`-periodic weight**, exactly like the twist.  Both are stripped at once by splitting
`range N` into residue classes modulo `M = Q · primorial P` — an `N`-independent modulus, since
`P` and `Q` are quantified before `N`.

**Consequence** (`norm_depthAvg_le_omega_progressions`).

    ‖depthAvg b P Q j h D N‖ ≤ (∑_{r<M} ‖∑_{m : Mm+r<N} ∏_{i<D} ζ_i^{ω(Mm+r+i+1)}‖)/N ,
    M = Q · primorial P .

The right-hand sums are correlations of `z^{ω}` at `D` consecutive shifts along the progressions
`M·X + (r+i+1)` — *precisely* the objects `rung_multi_correlation` bounds.  So the second of the
three gaps of lap 53 is closed: **neither the twist nor the small primes need any analytic
input.**  What remains between `rung_multi_correlation` and `weylLambertTwist_of_kfold_bound` is
the single genuinely open step, log-average → natural average.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-! ## `ω_{≤P}` is `primorial P`-periodic -/

/-- `ω_{≤P}(m)` is `primorial P`-periodic for `m ≠ 0`.  (The hypothesis is necessary: `ω_{≤P}(0)
= 0` because `primeFactors 0 = ∅`.  Every use site has `m = n + i + 1 ≥ 1`.) -/
theorem omegaSmall_add_primorial (P m : ℕ) (hm : m ≠ 0) :
    omegaSmall P (m + primorial P) = omegaSmall P m := by
  have hP : 0 < primorial P := primorial_pos P
  unfold omegaSmall
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hdvd, -⟩, hpP⟩
    have hpdvd : p ∣ primorial P := hp.dvd_primorial_iff.2 hpP
    refine ⟨⟨hp, ?_, hm⟩, hpP⟩
    have := Nat.dvd_sub hdvd hpdvd
    simpa using this
  · rintro ⟨⟨hp, hdvd, -⟩, hpP⟩
    have hpdvd : p ∣ primorial P := hp.dvd_primorial_iff.2 hpP
    exact ⟨⟨hp, hdvd.add hpdvd, by omega⟩, hpP⟩

/-! ## Unimodular periodic weights split a sum into residue classes -/

/-- A `R`-periodic function is `k·R`-periodic. -/
theorem periodic_mul {R : ℕ} {w : ℕ → ℂ} (hper : ∀ n, w (n + R) = w n) (k : ℕ) :
    ∀ n, w (n + k * R) = w n := by
  intro n
  induction k with
  | zero => simp
  | succ k ih =>
      have : n + (k + 1) * R = (n + k * R) + R := by ring
      rw [this, hper, ih]

/-- A periodic function is constant on residue classes. -/
theorem periodic_eq_mod {M : ℕ} (hM : 0 < M) {w : ℕ → ℂ} (hper : ∀ n, w (n + M) = w n) (n : ℕ) :
    w n = w (n % M) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases lt_or_ge n M with h | h
      · rw [Nat.mod_eq_of_lt h]
      · have hn : n - M + M = n := by omega
        have key : w n = w (n - M) := by
          have h2 := hper (n - M)
          rw [hn] at h2
          exact h2
        rw [key, ih (n - M) (by omega), Nat.mod_eq_sub_mod h]

/-- **A unimodular periodic weight splits off.**  The `M`-periodic factor `w` is constant on each
residue class mod `M`, so the triangle inequality strips it at a cost of the FIXED factor `M`. -/
theorem norm_sum_periodic_le {M : ℕ} (hM : 0 < M) (w : ℕ → ℂ)
    (hper : ∀ n, w (n + M) = w n) (hw : ∀ n, ‖w n‖ ≤ 1) (N : ℕ) (F : ℕ → ℂ) :
    ‖∑ n ∈ range N, w n * F n‖
      ≤ ∑ r ∈ range M, ‖∑ n ∈ (range N).filter (fun n => n % M = r), F n‖ := by
  classical
  have hmaps : ∀ n ∈ range N, n % M ∈ range M := fun n _ =>
    Finset.mem_range.2 (Nat.mod_lt _ hM)
  have hsplit : ∑ n ∈ range N, w n * F n
      = ∑ r ∈ range M, w r * ∑ n ∈ (range N).filter (fun n => n % M = r), F n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => w n * F n)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [periodic_eq_mod hM hper n, (Finset.mem_filter.1 hn).2]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw r)

/-! ## Stripping the small primes -/

/-- `ζ · conj ζ = 1` for the depth roots. -/
theorem depthRoot_mul_conj (b : ℕ) (hh : ℤ) (i : ℕ) :
    depthRoot b hh i * (starRingEnd ℂ) (depthRoot b hh i) = 1 := by
  have hnorm : ‖depthRoot b hh i‖ = 1 := by rw [depthRoot]; exact norm_ee_real _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-- **The small-prime factorisation.**  `z^{ω_{>P}} = z^{ω} · conj(z)^{ω_{≤P}}` for `z` on the
unit circle. -/
theorem pow_omegaLarge_eq {z : ℂ} (hz : z * (starRingEnd ℂ) z = 1) (P m : ℕ) :
    z ^ omegaLarge P m = z ^ omegaNat m * ((starRingEnd ℂ) z) ^ omegaSmall P m := by
  have hsum : omegaNat m = omegaSmall P m + omegaLarge P m := by
    unfold omegaNat omegaSmall omegaLarge
    exact (Finset.card_filter_add_card_filter_not (s := m.primeFactors)
      (p := fun p => p ≤ P)).symm
  rw [hsum, pow_add, mul_comm (z ^ omegaSmall P m) (z ^ omegaLarge P m), mul_assoc,
    ← mul_pow, hz, one_pow, mul_one]

/-- The combined weight: the additive twist times the small-prime correction. -/
noncomputable def smallWeight (b P Q j : ℕ) (hh : ℤ) (D : ℕ) (n : ℕ) : ℂ :=
  ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) *
    ∏ i ∈ range D, ((starRingEnd ℂ) (depthRoot b hh i)) ^ omegaSmall P (n + i + 1)

theorem norm_smallWeight_le_one (b P Q j : ℕ) (hh : ℤ) (D n : ℕ) :
    ‖smallWeight b P Q j hh D n‖ ≤ 1 := by
  rw [smallWeight, norm_mul, norm_ee_real, one_mul, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow, RCLike.norm_conj, depthRoot, norm_ee_real, one_pow]

theorem smallWeight_periodic (b P Q j : ℕ) (hh : ℤ) (D : ℕ) (n : ℕ) :
    smallWeight b P Q j hh D (n + Q * primorial P) = smallWeight b P Q j hh D n := by
  have htw : ee ((((j : ℝ) * ((n + Q * primorial P : ℕ) : ℝ) / Q : ℝ) : ℂ))
      = ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · simp
    · have hmod : (n + Q * primorial P) % Q = n % Q := by
        simp [Nat.add_mul_mod_self_left]
      rw [ee_twist_mod hQ j hmod, ← ee_twist_mod hQ j (rfl : n % Q = n % Q)]
  have hsm : ∀ i : ℕ, omegaSmall P (n + Q * primorial P + i + 1)
      = omegaSmall P (n + i + 1) := by
    intro i
    have hstep : ∀ k : ℕ, omegaSmall P (n + i + 1 + k * primorial P)
        = omegaSmall P (n + i + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have hre : n + i + 1 + (k + 1) * primorial P
              = (n + i + 1 + k * primorial P) + primorial P := by ring
          rw [hre, omegaSmall_add_primorial P _ (by omega), ih]
    have hre : n + Q * primorial P + i + 1 = n + i + 1 + Q * primorial P := by ring
    rw [hre, hstep Q]
  rw [smallWeight, smallWeight, htw]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [hsm i]

/-- **The twisted, rough depth average reduced to FULL-`ω` progression correlations.**
Both the additive twist and the small primes are unimodular `M`-periodic weights with
`M = Q · primorial P` — an `N`-independent modulus — so one class decomposition strips both.
The resulting sums are exactly what `rung_multi_correlation` bounds (modulo the log→natural
weighting, the one genuinely open step). -/
theorem norm_depthAvg_le_omega_progressions {Q : ℕ} (hQ : 0 < Q) (b P j : ℕ) (hh : ℤ) (D N : ℕ) :
    ‖depthAvg b P Q j hh D N‖
      ≤ (∑ r ∈ range (Q * primorial P),
            ‖∑ m ∈ (range N).filter (fun m => Q * primorial P * m + r < N),
              ∏ i ∈ range D, depthRoot b hh i ^
                omegaNat (Q * primorial P * m + r + i + 1)‖) / N := by
  classical
  set M : ℕ := Q * primorial P with hM
  have hM0 : 0 < M := by rw [hM]; exact Nat.mul_pos hQ (primorial_pos P)
  have hterm : ∀ n : ℕ, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
      * ee ((((hh : ℝ) * tailDepth P b D n : ℝ) : ℂ))
      = smallWeight b P Q j hh D n * ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (n + i + 1) := by
    intro n
    rw [ee_tailDepth_eq_prod b P D n hh, smallWeight]
    rw [show (∏ i ∈ range D, depthRoot b hh i ^ omegaLarge P (n + i + 1))
        = ∏ i ∈ range D, (depthRoot b hh i ^ omegaNat (n + i + 1)
            * ((starRingEnd ℂ) (depthRoot b hh i)) ^ omegaSmall P (n + i + 1)) from
      Finset.prod_congr rfl fun i _ =>
        pow_omegaLarge_eq (depthRoot_mul_conj b hh i) P (n + i + 1)]
    rw [Finset.prod_mul_distrib]
    ring
  have hnum : ‖∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
        * ee ((((hh : ℝ) * tailDepth P b D n : ℝ) : ℂ))‖
      ≤ ∑ r ∈ range M, ‖∑ m ∈ (range N).filter (fun m => M * m + r < N),
            ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (M * m + r + i + 1)‖ := by
    rw [Finset.sum_congr rfl fun n _ => hterm n]
    refine le_trans (norm_sum_periodic_le hM0 _ (fun n => smallWeight_periodic b P Q j hh D n)
      (fun n => norm_smallWeight_le_one b P Q j hh D n) N
      (fun n => ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (n + i + 1)))
      (Finset.sum_le_sum fun r hr => ?_)
    rw [class_sum_reindex hM0 (Finset.mem_range.1 hr) N]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [depthAvg]
  · rw [depthAvg, norm_div, Complex.norm_natCast]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hnum

#print axioms omegaSmall_add_primorial
#print axioms periodic_mul
#print axioms periodic_eq_mod
#print axioms norm_sum_periodic_le
#print axioms depthRoot_mul_conj
#print axioms pow_omegaLarge_eq
#print axioms norm_smallWeight_le_one
#print axioms smallWeight_periodic
#print axioms norm_depthAvg_le_omega_progressions

end CastingOut

end NormalNumbers
