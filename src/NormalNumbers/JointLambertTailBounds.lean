/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.SwingC2
import Mathlib.NumberTheory.Harmonic.Bounds

set_option maxHeartbeats 1000000

/-!
# Elementary divisor averaging along a coprime progression

Paper: `papers/2026-09-26-joint-lambert-disjunctivity.md`, §3.

This module is purely elementary: no analytic input, no prime counting.  It proves the
divisor-average estimate that makes the joint Lambert *shared binary tail* controllable.

**`sum_tau_progression_le`** — for `u > 0`, `A > 0`, `(u, A) = 1`, `H ≥ 1`, and all
`u + mA ≤ H²` for `m < M`:

  `∑_{m < M} τ(u + mA) ≤ 2M(1 + log H) + 2H`.

The three ingredients:

1. `tau_le_two_mul_card_dvd_le` — pairing divisors at `H`: if `0 < n ≤ H²` then every
   divisor of `n` is either `≤ H` or is `n / h` for a divisor `h ≤ H`, so
   `τ(n) ≤ 2 · #{h ∈ [1, H] : h ∣ n}`.
2. `card_prog_dvd_le` (`(h, A) = 1`): the `m < M` with `h ∣ u + mA` lie in one residue
   class mod `h`, so there are at most `M / h + 1` of them; and `card_prog_dvd_eq_zero`
   (`(h, A) > 1`): there are none at all, because `(u, A) = 1`.
3. The harmonic bound `∑_{h=1}^{H} 1/h ≤ 1 + log H` (mathlib
   `harmonic_le_one_add_log`).

Also here: `poly8_lt_two_pow`, the growth fact that lets every "for `k` large" inequality
of the tail argument be *proved* rather than assumed.
-/

namespace NormalNumbers.JointLambert

open Finset

/-! ### Divisor pairing at the square root -/

/-- Divisor pairing at `H`: for `0 < n ≤ H²`, at most half of the divisors of `n` exceed
`H`, because `d ↦ n / d` sends them injectively into the divisors `≤ H`. -/
lemma tau_le_two_mul_card_dvd_le {n H : ℕ} (hn : 0 < n) (hnH : n ≤ H ^ 2) :
    NormalNumbers.SwingC2.tau n ≤ 2 * ((Icc 1 H).filter (fun h => h ∣ n)).card := by
  classical
  set S : Finset ℕ := (Icc 1 H).filter (fun h => h ∣ n) with hS
  have hsub : n.divisors ⊆ S ∪ S.image (fun h => n / h) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    by_cases hdH : d ≤ H
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hd0, hdH⟩, hdvd⟩)
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.2 ⟨n / d, ?_, Nat.div_div_self hdvd hn.ne'⟩
      have hq : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
      have hq0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd0
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hq0, ?_⟩, hq⟩
      by_contra hqH
      push_neg at hqH
      have : H ^ 2 < (n / d) * d := by
        have h1 : H + 1 ≤ n / d := hqH
        have h2 : H + 1 ≤ d := by omega
        calc H ^ 2 = H * H := sq H
          _ < (H + 1) * (H + 1) := by nlinarith
          _ ≤ (n / d) * d := Nat.mul_le_mul h1 h2
      rw [Nat.div_mul_cancel hdvd] at this
      omega
  calc NormalNumbers.SwingC2.tau n = n.divisors.card := rfl
    _ ≤ (S ∪ S.image (fun h => n / h)).card := Finset.card_le_card hsub
    _ ≤ S.card + (S.image (fun h => n / h)).card := Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * S.card := by ring

/-! ### Counting the progression indices divisible by `h` -/

/-- If `(h, A) = 1` then the indices `m < M` with `h ∣ u + mA` form a single residue class
modulo `h`, hence number at most `M / h + 1`. -/
lemma card_prog_dvd_le {u A h M : ℕ} (hh : 0 < h) (hcop : Nat.Coprime h A) :
    ((range M).filter (fun m => h ∣ u + m * A)).card ≤ M / h + 1 := by
  classical
  have main : ((range M).filter (fun m => h ∣ u + m * A)).card ≤ (range (M / h + 1)).card := by
   refine Finset.card_le_card_of_injOn (fun m => m / h) ?_ ?_
   · intro m hm
     simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
     exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.le))
   · intro m hm m' hm' hmm
     simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm hm'
     -- `h` divides the difference of the two progression values, and `(h, A) = 1`
     have key : m % h = m' % h := by
       rcases le_total m m' with hle | hle
       · have hdvd : h ∣ (m' - m) * A := by
           have h1 : h ∣ u + m * A := hm.2
           have h2 : h ∣ u + m' * A := hm'.2
           have : (m' - m) * A = (u + m' * A) - (u + m * A) := by
             rw [Nat.sub_mul]; omega
           rw [this]
           exact Nat.dvd_sub h2 h1
         exact (Nat.modEq_iff_dvd' hle).2 (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd)
       · have hdvd : h ∣ (m - m') * A := by
           have h1 : h ∣ u + m * A := hm.2
           have h2 : h ∣ u + m' * A := hm'.2
           have : (m - m') * A = (u + m * A) - (u + m' * A) := by
             rw [Nat.sub_mul]; omega
           rw [this]
           exact Nat.dvd_sub h1 h2
         exact ((Nat.modEq_iff_dvd' hle).2 (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd)).symm
     have e1 := Nat.div_add_mod m h
     have e2 := Nat.div_add_mod m' h
     have hmm' : m / h = m' / h := hmm
     rw [hmm', key] at e1
     omega
  simpa using main

/-- If `(u, A) = 1` but `h` shares a prime with `A`, then no progression value `u + mA` is
divisible by `h`. -/
lemma card_prog_dvd_eq_zero {u A h M : ℕ} (hcop : Nat.Coprime u A)
    (hnc : ¬ Nat.Coprime h A) :
    ((range M).filter (fun m => h ∣ u + m * A)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hdvd
  set g := Nat.gcd h A with hg
  have hg1 : g ≠ 1 := hnc
  have hp : (Nat.minFac g).Prime := Nat.minFac_prime hg1
  have hph : Nat.minFac g ∣ h := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_left h A)
  have hpA : Nat.minFac g ∣ A := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_right h A)
  have hpu : Nat.minFac g ∣ u := by
    have h1 : Nat.minFac g ∣ u + m * A := hph.trans hdvd
    have h2 : Nat.minFac g ∣ m * A := Dvd.dvd.mul_left hpA m
    simpa using Nat.dvd_sub h1 h2
  have : Nat.minFac g ∣ 1 := hcop ▸ Nat.dvd_gcd hpu hpA
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- `∑_{h=1}^{H} 1/h` is the harmonic number. -/
lemma sum_inv_Icc_eq_harmonic (H : ℕ) :
    ∑ h ∈ Icc 1 H, ((h : ℝ))⁻¹ = (harmonic H : ℝ) := by
  induction H with
  | zero => simp [harmonic]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring

/-! ### The divisor average -/

/-- **Divisor averaging along a coprime progression** (paper §3).  For `u > 0`, `A > 0`,
`(u, A) = 1`, `H ≥ 1`, and every value `u + mA` (`m < M`) at most `H²`:
`∑_{m<M} τ(u + mA) ≤ 2M(1 + log H) + 2H`. -/
theorem sum_tau_progression_le {u A H M : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u A)
    (hH : 1 ≤ H) (hbd : ∀ m, m < M → u + m * A ≤ H ^ 2) :
    (∑ m ∈ range M, (NormalNumbers.SwingC2.tau (u + m * A) : ℝ)) ≤
      2 * M * (1 + Real.log H) + 2 * H := by
  classical
  -- Step 1: pointwise divisor pairing, then swap the double count.
  have step1 : ∑ m ∈ range M, NormalNumbers.SwingC2.tau (u + m * A) ≤
      2 * ∑ h ∈ Icc 1 H, ((range M).filter (fun m => h ∣ u + m * A)).card := by
    have hpt : ∀ m ∈ range M, NormalNumbers.SwingC2.tau (u + m * A) ≤
        2 * ((Icc 1 H).filter (fun h => h ∣ u + m * A)).card := by
      intro m hm
      exact tau_le_two_mul_card_dvd_le (by omega) (hbd m (Finset.mem_range.1 hm))
    calc ∑ m ∈ range M, NormalNumbers.SwingC2.tau (u + m * A)
        ≤ ∑ m ∈ range M, 2 * ((Icc 1 H).filter (fun h => h ∣ u + m * A)).card :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ m ∈ range M, ((Icc 1 H).filter (fun h => h ∣ u + m * A)).card := by
          rw [Finset.mul_sum]
      _ = 2 * ∑ h ∈ Icc 1 H, ((range M).filter (fun m => h ∣ u + m * A)).card := by
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
  -- Step 2: each inner count is at most `M / h + 1`.
  have step2 : ∀ h ∈ Icc 1 H, ((range M).filter (fun m => h ∣ u + m * A)).card ≤ M / h + 1 := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    by_cases hc : Nat.Coprime h A
    · exact card_prog_dvd_le hh.1 hc
    · rw [card_prog_dvd_eq_zero hcop hc]; exact Nat.zero_le _
  have step3 : ∑ m ∈ range M, NormalNumbers.SwingC2.tau (u + m * A) ≤
      2 * ∑ h ∈ Icc 1 H, (M / h + 1) := by
    refine step1.trans ?_
    exact Nat.mul_le_mul_left 2 (Finset.sum_le_sum step2)
  -- Step 3: cast, and bound the harmonic sum.
  have hIcc : (Icc 1 H).card = H := by simp
  have e1 : (∑ h ∈ Icc 1 H, (M / h + 1)) = (∑ h ∈ Icc 1 H, M / h) + H := by
    simp [Finset.sum_add_distrib, hIcc]
  have hcast : (∑ m ∈ range M, (NormalNumbers.SwingC2.tau (u + m * A) : ℝ)) ≤
      2 * ((∑ h ∈ Icc 1 H, ((M / h : ℕ) : ℝ)) + (H : ℝ)) := by
    have := step3
    rw [e1] at this
    have h2 : ((∑ m ∈ range M, NormalNumbers.SwingC2.tau (u + m * A) : ℕ) : ℝ) ≤
        ((2 * ((∑ h ∈ Icc 1 H, M / h) + H) : ℕ) : ℝ) := Nat.cast_le.2 this
    push_cast at h2
    exact h2
  refine hcast.trans ?_
  have hharm : ∑ h ∈ Icc 1 H, ((M / h : ℕ) : ℝ) ≤ (M : ℝ) * (1 + Real.log H) := by
    have hterm : ∀ h ∈ Icc 1 H, ((M / h : ℕ) : ℝ) ≤ (M : ℝ) * ((h : ℝ))⁻¹ := by
      intro h _
      have := Nat.cast_div_le (α := ℝ) (m := M) (n := h)
      rw [div_eq_mul_inv] at this
      exact this
    calc ∑ h ∈ Icc 1 H, ((M / h : ℕ) : ℝ)
        ≤ ∑ h ∈ Icc 1 H, (M : ℝ) * ((h : ℝ))⁻¹ := Finset.sum_le_sum hterm
      _ = (M : ℝ) * ∑ h ∈ Icc 1 H, ((h : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ = (M : ℝ) * (harmonic H : ℝ) := by rw [sum_inv_Icc_eq_harmonic]
      _ ≤ (M : ℝ) * (1 + Real.log H) := by
          exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log H) (Nat.cast_nonneg M)
  linarith

/-! ### Growth: polynomials are eventually beaten by `2^k` -/

/-- `k^8 ≤ 2^k` for `k ≥ 44` (the threshold is tight: `43^8 > 2^43`). -/
lemma pow_eight_le_two_pow {k : ℕ} (hk : 44 ≤ k) : k ^ 8 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hstep : (k + 1) ^ 8 ≤ 2 * k ^ 8 := by
        have h1 : 44 * (k + 1) ≤ 45 * k := by omega
        have h2 : (44 * (k + 1)) ^ 8 ≤ (45 * k) ^ 8 := Nat.pow_le_pow_left h1 8
        have h3 : (44 : ℕ) ^ 8 * (k + 1) ^ 8 ≤ 45 ^ 8 * k ^ 8 := by
          simpa [mul_pow] using h2
        have h4 : (45 : ℕ) ^ 8 * k ^ 8 ≤ 2 * (44 ^ 8 * k ^ 8) := by
          have : (45 : ℕ) ^ 8 ≤ 2 * 44 ^ 8 := by norm_num
          calc (45 : ℕ) ^ 8 * k ^ 8 ≤ (2 * 44 ^ 8) * k ^ 8 := Nat.mul_le_mul_right _ this
            _ = 2 * (44 ^ 8 * k ^ 8) := by ring
        have h5 : (44 : ℕ) ^ 8 * (k + 1) ^ 8 ≤ 44 ^ 8 * (2 * k ^ 8) := by
          calc (44 : ℕ) ^ 8 * (k + 1) ^ 8 ≤ 45 ^ 8 * k ^ 8 := h3
            _ ≤ 2 * (44 ^ 8 * k ^ 8) := h4
            _ = 44 ^ 8 * (2 * k ^ 8) := by ring
        exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
      calc (k + 1) ^ 8 ≤ 2 * k ^ 8 := hstep
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by ring

/-- **The growth lemma.**  For any constants `C`, `m`, once `k ≥ 2(6562C + m + 45)` we have
`m + C·k^8 + C ≤ 2^k`.  Every "for `k` large" step of the tail argument is discharged by
this, so nothing asymptotic is assumed. -/
lemma poly_eight_le_two_pow (C m : ℕ) {k : ℕ} (hk : 2 * (6562 * C + m + 45) ≤ k) :
    m + C * k ^ 8 + C ≤ 2 ^ k := by
  set i := k / 2 with hi
  have hi1 : 6562 * C + m + 45 ≤ i := by omega
  have hi44 : 44 ≤ i := by omega
  have hki : k ≤ 2 * i + 1 := by omega
  have h2i : 2 * i ≤ k := by omega
  set y := 2 ^ i with hy
  have hyi : i < y := Nat.lt_two_pow_self
  have hy1 : 1 ≤ y := by omega
  -- `k^8 ≤ 6561 y`
  have hk8 : k ^ 8 ≤ 6561 * y := by
    calc k ^ 8 ≤ (3 * i) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      _ = 6561 * i ^ 8 := by ring
      _ ≤ 6561 * 2 ^ i := Nat.mul_le_mul_left _ (pow_eight_le_two_pow hi44)
  -- `y^2 ≤ 2^k`
  have hysq : y * y ≤ 2 ^ k := by
    calc y * y = 2 ^ (2 * i) := by rw [hy]; ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2i
  have hmain : m + C * (6561 * y) + C ≤ y * y := by
    have hyge : 6562 * C + m + 45 ≤ y := by omega
    nlinarith [hy1, hyge]
  calc m + C * k ^ 8 + C ≤ m + C * (6561 * y) + C := by
        have := Nat.mul_le_mul_left C hk8; omega
    _ ≤ y * y := hmain
    _ ≤ 2 ^ k := hysq

/-! ### The crude far-range bound and summability -/

/-- `τ(n) ≤ n` (crude, but all the far range needs). -/
lemma tau_le_self (n : ℕ) : NormalNumbers.SwingC2.tau n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [NormalNumbers.SwingC2.tau]
  · have : n.divisors ⊆ Icc 1 n := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      exact Finset.mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos hd.1 hn, Nat.le_of_dvd hn hd.1⟩
    calc NormalNumbers.SwingC2.tau n = n.divisors.card := rfl
      _ ≤ (Icc 1 n).card := Finset.card_le_card this
      _ = n := by simp

/-- `t ↦ (a + t) · 2^(-t)` is summable for every real `a`. -/
lemma summable_affine_geometric (a : ℝ) :
    Summable (fun t : ℕ => (a + t) / 2 ^ t) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; rw [abs_of_pos] <;> norm_num
  have h1 : Summable (fun t : ℕ => a * (1 / 2 : ℝ) ^ t) :=
    (summable_geometric_of_norm_lt_one hr).mul_left a
  have h2 : Summable (fun t : ℕ => (t : ℝ) * (1 / 2 : ℝ) ^ t) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have := h1.add h2
  refine this.congr ?_
  intro t
  rw [div_pow, one_pow]
  field_simp

/-- The tail `∑' t, τ(N₀ + t)/2^t` converges. -/
lemma summable_tau_div (N₀ : ℕ) :
    Summable (fun t : ℕ => (NormalNumbers.SwingC2.tau (N₀ + t) : ℝ) / 2 ^ t) := by
  refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
    (summable_affine_geometric (N₀ : ℝ))
  have h1 : (NormalNumbers.SwingC2.tau (N₀ + t) : ℝ) ≤ (N₀ : ℝ) + t := by
    have := tau_le_self (N₀ + t)
    have : ((NormalNumbers.SwingC2.tau (N₀ + t) : ℕ) : ℝ) ≤ ((N₀ + t : ℕ) : ℝ) :=
      Nat.cast_le.2 this
    push_cast at this
    exact this
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- **The crude far-range tail bound**: `∑' t, τ(N₀ + t)/2^t ≤ 2 N₀ + 2`. -/
lemma tsum_tau_div_le (N₀ : ℕ) :
    ∑' t : ℕ, (NormalNumbers.SwingC2.tau (N₀ + t) : ℝ) / 2 ^ t ≤ 2 * N₀ + 2 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos] <;> norm_num
  have hval : ∑' t : ℕ, ((N₀ : ℝ) + t) / 2 ^ t = 2 * N₀ + 2 := by
    have h1 : Summable (fun t : ℕ => (N₀ : ℝ) * (1 / 2 : ℝ) ^ t) :=
      (summable_geometric_of_norm_lt_one hr).mul_left _
    have h2 : Summable (fun t : ℕ => (t : ℝ) * (1 / 2 : ℝ) ^ t) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
    have hcong : (fun t : ℕ => ((N₀ : ℝ) + t) / 2 ^ t)
        = fun t : ℕ => (N₀ : ℝ) * (1 / 2 : ℝ) ^ t + (t : ℝ) * (1 / 2 : ℝ) ^ t := by
      funext t
      rw [div_pow, one_pow]
      field_simp
    rw [hcong, h1.tsum_add h2, tsum_mul_left, tsum_geometric_two,
      tsum_coe_mul_geometric_of_norm_lt_one hr]
    norm_num
    ring
  calc ∑' t : ℕ, (NormalNumbers.SwingC2.tau (N₀ + t) : ℝ) / 2 ^ t
      ≤ ∑' t : ℕ, ((N₀ : ℝ) + t) / 2 ^ t := by
        refine Summable.tsum_le_tsum (fun t => ?_) (summable_tau_div N₀)
          (summable_affine_geometric (N₀ : ℝ))
        have h1 : ((NormalNumbers.SwingC2.tau (N₀ + t) : ℕ) : ℝ) ≤ ((N₀ + t : ℕ) : ℝ) :=
          Nat.cast_le.2 (tau_le_self _)
        push_cast at h1
        exact div_le_div_of_nonneg_right h1 (by positivity)
    _ = 2 * N₀ + 2 := hval

end NormalNumbers.JointLambert
