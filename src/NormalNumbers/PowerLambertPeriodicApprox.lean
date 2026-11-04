/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertNearZero

/-!
# Word frequencies of a perfect-power Lambert constant exist

`u_n = orbit b S n = {v_n + R_n}` with `v_n = {periodicTail Q n}` exactly `Q`-periodic and
`R_n = aperiodicTail Q n ≥ 0` of mean `≤ 2/(D+1)` (`Q = (D!)^r`).  If `R_n < η` then `u_n ∈ I`
and `v_n ∈ I` agree for a cylinder `I = [W/b^ℓ, (W+1)/b^ℓ)` unless `u_n` lies in
`[k/b^ℓ, k/b^ℓ + η)` for some `k`, which forces `u_{n+ℓ} < b^ℓ η` (`orbit_shift_lt_of_mem_Ico`).
Near-zero density (`powerLambert_nearZero_density_aux`) and Markov for `R` make the mismatch
density small, and the periodic counts converge, so the word counts are Cauchy.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset

/-! ### Periodic counts -/

/-- Counting a `Q`-periodic predicate on `[0, Q q + s)`. -/
theorem card_filter_range_mul_add (p : ℕ → Prop) [DecidablePred p] {Q : ℕ}
    (hp : ∀ n k, p (n + k * Q) ↔ p n) (q s : ℕ) :
    ((range (Q * q + s)).filter p).card =
      q * ((range Q).filter p).card + ((range s).filter p).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_range_add]
  congr 1
  · induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.succ_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Q * q + i = i + q * Q by ring]
      exact if_congr (hp i q) rfl rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Q * q + i = i + q * Q by ring]
    exact if_congr (hp i q) rfl rfl

/-- **Periodic averages.**  For a `Q`-periodic predicate and `N ≥ 1`,
`|#{n<N : p n}/N − #{n<Q : p n}/Q| ≤ Q/N`. -/
theorem abs_card_filter_div_sub_le (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hp : ∀ n k, p (n + k * Q) ↔ p n) {N : ℕ} (hN : 0 < N) :
    |(((range N).filter p).card : ℝ) / N - (((range Q).filter p).card : ℝ) / Q| ≤
      (Q : ℝ) / N := by
  have hdecomp := card_filter_range_mul_add p hp (N / Q) (N % Q)
  rw [Nat.div_add_mod] at hdecomp
  set c := ((range Q).filter p).card with hc
  set e := ((range (N % Q)).filter p).card with he
  have hcQ : c ≤ Q := (Finset.card_filter_le _ _).trans (by simp)
  have heQ : e ≤ Q := (Finset.card_filter_le _ _).trans (by simp; exact (Nat.mod_lt _ hQ).le)
  have hsQ : N % Q ≤ Q := (Nat.mod_lt _ hQ).le
  have hNdec : (N : ℝ) = Q * (N / Q : ℕ) + (N % Q : ℕ) := by
    exact_mod_cast (Nat.div_add_mod N Q).symm
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hdecomp]
  push_cast
  have key : ((N / Q : ℕ) * (c : ℝ) + e) / N - c / Q = ((Q : ℝ) * e - (N % Q : ℕ) * c) / (Q * N) := by
    field_simp
    rw [hNdec]
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Q * N), div_le_div_iff₀
    (by positivity) hNr]
  have h1 : (e : ℝ) ≤ Q := by exact_mod_cast heQ
  have h2 : (c : ℝ) ≤ Q := by exact_mod_cast hcQ
  have h3 : ((N % Q : ℕ) : ℝ) ≤ Q := by exact_mod_cast hsQ
  have h4 : (0 : ℝ) ≤ e := by positivity
  have h5 : (0 : ℝ) ≤ c := by positivity
  have h6 : (0 : ℝ) ≤ ((N % Q : ℕ) : ℝ) := by positivity
  rw [show (Q : ℝ) * (Q * N) = Q * Q * N by ring]
  refine mul_le_mul_of_nonneg_right ?_ hNr.le
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hQr.le,
    mul_le_mul h3 h2 h5 hQr.le, mul_nonneg h6 h5, mul_nonneg hQr.le h4]

/-! ### Mismatch between the orbit and its periodic model -/

/-- **Mismatch.**  If `v ∈ [0,1)`, `0 ≤ R < η` and `u = {v + R}`, then `u ∈ [α, β)` and
`v ∈ [α, β)` agree unless `u ∈ [α, α+η)`, `u ∈ [β, β+η)` or `u < η`. -/
theorem mem_Ico_iff_of_fract_add {v R η α β : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hR : 0 ≤ R)
    (hRη : R < η) (hη : η ≤ 1) (hα : ¬ Int.fract (v + R) ∈ Set.Ico α (α + η))
    (hβ : ¬ Int.fract (v + R) ∈ Set.Ico β (β + η)) (h0 : ¬ Int.fract (v + R) < η) :
    (Int.fract (v + R) ∈ Set.Ico α β ↔ v ∈ Set.Ico α β) := by
  by_cases hw : v + R < 1
  · have hu : Int.fract (v + R) = v + R := Int.fract_eq_self.mpr ⟨by linarith, hw⟩
    rw [hu] at hα hβ ⊢
    simp only [Set.mem_Ico, not_and, not_lt] at hα hβ ⊢
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by linarith⟩
      by_contra h
      push Not at h
      linarith [hα h1]
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith, ?_⟩
      by_contra h
      push Not at h
      linarith [hβ h]
  · exfalso
    apply h0
    have hu : Int.fract (v + R) = v + R - 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 1, by push_cast; ring⟩
    rw [hu]
    linarith

/-- Orbit shift: `orbit b x (n + k) = {b^k · orbit b x n}`. -/
theorem orbit_add_shift (b : ℕ) (x : ℝ) (n k : ℕ) :
    orbit b x (n + k) = Int.fract (orbit b x n * (b : ℝ) ^ k) := by
  unfold orbit
  rw [pow_add, ← mul_assoc]
  have : Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ k
      = x * (b : ℝ) ^ n * (b : ℝ) ^ k - ((⌊x * (b : ℝ) ^ n⌋ * (b ^ k : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

/-- **Near a `b`-adic rational, shift to near `0`.**  If `orbit n ∈ [k/b^ℓ, k/b^ℓ + 1/b^(L+ℓ))`
then `orbit (n + ℓ) < 1/b^L`. -/
theorem orbit_shift_lt_of_mem_Ico {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (n ℓ L k : ℕ)
    (h : orbit b x n ∈ Set.Ico ((k : ℝ) / (b : ℝ) ^ ℓ)
      ((k : ℝ) / (b : ℝ) ^ ℓ + 1 / (b : ℝ) ^ (L + ℓ))) :
    orbit b x (n + ℓ) < 1 / (b : ℝ) ^ L := by
  have hbℓ : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  rw [orbit_add_shift]
  set y := orbit b x n * (b : ℝ) ^ ℓ with hy
  have h1 : (k : ℝ) ≤ y := by
    have := h.1
    rw [div_le_iff₀ hbℓ] at this
    exact this
  have h2 : y < k + 1 / (b : ℝ) ^ L := by
    have := mul_lt_mul_of_pos_right h.2 hbℓ
    rw [add_mul, div_mul_cancel₀ _ hbℓ.ne', pow_add, one_div, mul_inv, mul_assoc,
      inv_mul_cancel₀ hbℓ.ne', mul_one, ← one_div] at this
    exact this
  have hbL1 : 1 / (b : ℝ) ^ L ≤ 1 := by
    rw [div_le_one hbL]
    exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b))
  have hf : Int.fract y = y - k := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, ?_, k, by push_cast; ring⟩
    rcases hbL1.lt_or_eq with hlt | heq
    · linarith
    · -- `L = 0`: then `1/b^L = 1`
      linarith
  rw [hf]
  linarith

/-! ### Markov for the non-periodic tail -/

/-- The non-periodic count is supported on roots `d > D` when every `d ≤ D` has `d^r ∣ Q`. -/
theorem aperiodicPowerCount_le_bigRootCount {r Q D : ℕ}
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (m : ℕ) :
    aperiodicPowerCount r Q m ≤ bigRootCount r D m := by
  unfold aperiodicPowerCount bigRootCount
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
  obtain ⟨⟨hdm, hm0⟩, hdr, hQ⟩ := hd
  refine ⟨⟨hdm, hm0⟩, hdr, ?_⟩
  by_contra hle
  push Not at hle
  exact hQ (hQD d (Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hm0)) hle)

/-- **Mean of the non-periodic tail.**  `Σ_{n<N} R_Q(n) ≤ (2/(D+1)) (N + 2)`. -/
theorem sum_range_aperiodicTail_le {b r Q D : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (N : ℕ) :
    (∑ n ∈ range N, aperiodicTail b r Q n) ≤ 2 / ((D : ℝ) + 1) * (N + 2) := by
  have hmean : ∀ X, ((∑ m ∈ Ioc 0 X, aperiodicPowerCount r Q m : ℕ) : ℝ) ≤
      2 / ((D : ℝ) + 1) * X := by
    intro X
    have h1 : (∑ m ∈ Ioc 0 X, aperiodicPowerCount r Q m) ≤
        ∑ m ∈ Ioc 0 X, bigRootCount r D m :=
      Finset.sum_le_sum fun m _ => aperiodicPowerCount_le_bigRootCount hQD m
    have h2 := sum_card_powerDivisors_filter_le hr (fun d => D < d) X
    have h3 := sum_filter_lt_inv_sq_le D X
    calc ((∑ m ∈ Ioc 0 X, aperiodicPowerCount r Q m : ℕ) : ℝ)
        ≤ ((∑ m ∈ Ioc 0 X, bigRootCount r D m : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ X * ∑ d ∈ (Ioc 0 X).filter (fun d => D < d), ((d : ℝ) ^ 2)⁻¹ := h2
      _ ≤ X * (2 / ((D : ℝ) + 1)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 / ((D : ℝ) + 1) * X := by ring
  have h := sum_range_tail_le hb (aperiodicPowerCount r Q) (aperiodicPowerCount_le_self r Q)
    (by positivity) hmean N 0
  simp only [add_zero, Nat.cast_zero] at h
  exact h

end NormalNumbers.ArithmeticDisjunctivity
