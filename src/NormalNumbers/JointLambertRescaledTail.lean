/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertRescaledPrimes
import NormalNumbers.JointLambertTail

set_option maxHeartbeats 2000000

/-!
# The shared binary tail majorant on the rescaled schedule, UNCONDITIONAL

This is `JointLambertTail.exists_joint_small_tail` with the prime-search endpoint raised from
`X = 2^(4k⁴)` to `X = 2^(4k¹²)` and both analytic hypotheses discharged.  Nothing in the tail
argument cared which power of `2` the endpoint was: the schedule is used only through

* `U = 2^(k¹²)`, `X = U⁴`, `H = U³`, `Z = U⁶`, with `B, Q ≤ 2^(k⁴) ≤ U`;
* `H ≤ M = X/B + 1` (why `X = U⁴`) and `n_m + j ≤ Z = H²` (why `Z = U⁶`);
* the candidate density `1/(16k¹²)` instead of `1/(16k⁴)`.

The two resulting estimates — the feasibility test of the rescale — are

* near tail: `(192k²⁴ + 128k¹²)/2^k → 0`;
* far tail: `4·2^(6k¹²)/2^(2^k) → 0`,

both discharged by `eventually_nat_poly_le_two_pow`, which replaces the explicit degree-8
thresholds of `poly_eight_le_two_pow` (those do not reach degree 24).
-/

namespace NormalNumbers.JointLambert

open Finset Filter

theorem exists_joint_small_tail_rescaled
    {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) (K N : ℕ) :
    ∃ k n : ℕ, K ≤ k ∧ r < k ∧ 1 ≤ n ∧ N ≤ n ∧
      (∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ NormalNumbers.SwingC2.tau (n + j)) ∧
      NormalNumbers.SwingC2.tau (n + r) = 2 * a ∧
      ∑' t : ℕ, (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) < ε := by
  classical
  -- ### the archimedean scale, fixed from `ε` BEFORE the prime-selection height
  obtain ⟨m₀, hm₀⟩ :=
    exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 2 by linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
  set Cn : ℕ := 320 * 2 ^ m₀ with hCn
  obtain ⟨Knear, hKnear⟩ := eventually_atTop.1 (eventually_nat_poly_le_two_pow 24 Cn)
  obtain ⟨Kfar, hKfar⟩ := eventually_atTop.1 (eventually_nat_poly_le_two_pow 12 (8 + m₀))
  set K' : ℕ := max (max K N) (max (max Knear Kfar) 16) with hK'
  obtain ⟨k, q, p, R, u, hkK', hkr, hqlo, hqhi, hqp, hpp, hR0, hRA, hu1, huB, hRu, hAQB,
    hu1q, hcopuB, hRr, hres, hkill, hsurv, hcop, hQle, hBle, hBU, hQU, hRL, hcount⟩ :=
    exists_joint_prime_candidates_rescaled hc ha hr K'
  set A := jointA c a k r q p with hA
  set B := jointB c k r q p with hB
  set Q := jointQ a q with hQ
  have hk2 : 2 ≤ k := by omega
  have hkK : K ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hkK'
  have hkN : N ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hkK'
  have hkfar : Kfar ≤ k :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hkK'
  have hknear : Knear ≤ k :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hkK'
  have hk16 : 16 ≤ k :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hkK'
  have hB0 : 0 < B := by
    rw [hB]
    exact jointB_pos hqp.pos fun j t hj ht =>
      (hpp j t (Finset.mem_range.1 (Finset.mem_of_mem_erase hj))
        (Finset.ne_of_mem_erase hj) ht).1.pos
  -- ### the dyadic schedule
  have hkk12 : k ^ 4 ≤ k ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hBU12 : B ≤ 2 ^ (k ^ 12) :=
    hBU.trans (Nat.pow_le_pow_right (by norm_num) hkk12)
  have hQU12 : Q ≤ 2 ^ (k ^ 12) :=
    hQU.trans (Nat.pow_le_pow_right (by norm_num) hkk12)
  have hk4 : 16 ≤ k ^ 12 := by
    calc (16 : ℕ) ≤ 2 ^ 12 := by norm_num
      _ ≤ k ^ 12 := Nat.pow_le_pow_left hk2 12
  have hkk4 : k ≤ k ^ 12 := Nat.le_self_pow (by norm_num) k
  have hU2 : 2 ≤ 2 ^ (k ^ 12) := Nat.one_lt_two_pow (by omega)
  have hU4 : 4 ≤ 2 ^ (k ^ 12) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k ^ 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hXU : (2 : ℕ) ^ (4 * k ^ 12) = (2 ^ (k ^ 12)) ^ 4 := by
    rw [← pow_mul]; ring_nf
  have hZU : (2 : ℕ) ^ (6 * k ^ 12) = (2 ^ (k ^ 12)) ^ 6 := by
    rw [← pow_mul]; ring_nf
  have hHU : (2 : ℕ) ^ (3 * k ^ 12) = (2 ^ (k ^ 12)) ^ 3 := by
    rw [← pow_mul]; ring_nf
  have hHsq : ((2 : ℕ) ^ (3 * k ^ 12)) ^ 2 = 2 ^ (6 * k ^ 12) := by
    rw [← pow_mul]; ring_nf
  have hLU : (2 : ℕ) ^ k ≤ 2 ^ (k ^ 12) := Nat.pow_le_pow_right (by norm_num) hkk4
  -- `M ≥ H`, the reason `X = U⁴` and `H = U³`
  have hHM : (2 : ℕ) ^ (3 * k ^ 12) ≤ 2 ^ (4 * k ^ 12) / B + 1 := by
    have : (2 : ℕ) ^ (3 * k ^ 12) * B ≤ 2 ^ (4 * k ^ 12) := by
      calc (2 : ℕ) ^ (3 * k ^ 12) * B ≤ 2 ^ (3 * k ^ 12) * 2 ^ (k ^ 12) :=
            Nat.mul_le_mul_left _ hBU12
        _ = 2 ^ (4 * k ^ 12) := by rw [← pow_add]; ring_nf
    have := (Nat.le_div_iff_mul_le hB0).2 this
    omega
  -- ### every progression value in the relevant window is at most `Z = U⁶`
  have hnZ : ∀ m, m < 2 ^ (4 * k ^ 12) / B + 1 → ∀ i, i ≤ 2 ^ k →
      R + m * A + i ≤ 2 ^ (6 * k ^ 12) := by
    intro m hm i hi
    have hmle : m ≤ 2 ^ (4 * k ^ 12) / B := by omega
    have hmA : m * A ≤ 2 ^ (k ^ 12) * 2 ^ (4 * k ^ 12) := by
      calc m * A = Q * (m * B) := by rw [hAQB]; ring
        _ ≤ Q * (2 ^ (4 * k ^ 12) / B * B) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmle)
        _ ≤ Q * 2 ^ (4 * k ^ 12) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
        _ ≤ 2 ^ (k ^ 12) * 2 ^ (4 * k ^ 12) := Nat.mul_le_mul_right _ hQU12
    have hRlt : R ≤ 2 ^ (k ^ 12) * 2 ^ (k ^ 12) := by
      have : A = Q * B := hAQB
      calc R ≤ A := hRA.le
        _ = Q * B := this
        _ ≤ 2 ^ (k ^ 12) * 2 ^ (k ^ 12) := Nat.mul_le_mul hQU12 hBU12
    set U := (2 : ℕ) ^ (k ^ 12) with hU
    have h1 : (2 : ℕ) ^ (4 * k ^ 12) = U ^ 4 := hXU
    have h2 : (2 : ℕ) ^ (6 * k ^ 12) = U ^ 6 := hZU
    rw [h2]
    have hiU : i ≤ U := le_trans hi hLU
    rw [h1] at hmA
    have : R + m * A + i ≤ U * U + U * U ^ 4 + U :=
      Nat.add_le_add (Nat.add_le_add hRlt hmA) hiU
    refine le_trans this ?_
    exact window_le_pow_six hU4
  -- ### the near range: divisor averaging, summed over the window `[k, 2^k)`
  set D := 2 ^ k - k with hD
  have hDk : k + D = 2 ^ k := by
    have : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    omega
  set S : ℝ := 2 * ((2 ^ (4 * k ^ 12) / B + 1 : ℕ) : ℝ)
      * (1 + Real.log ((2 ^ (3 * k ^ 12) : ℕ) : ℝ)) + 2 * ((2 ^ (3 * k ^ 12) : ℕ) : ℝ) with hS
  set F : ℕ → ℝ := fun m =>
    ∑ t ∈ Finset.range D, (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ) / 2 ^ (k + t)
    with hF
  have hFnn : ∀ m, 0 ≤ F m := by
    intro m
    exact Finset.sum_nonneg fun t _ => by positivity
  have hS0 : 0 ≤ S := by
    rw [hS]
    have : (0 : ℝ) ≤ Real.log ((2 ^ (3 * k ^ 12) : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow
    positivity
  have hrowbd : ∀ t ∈ Finset.range D,
      (∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1),
        (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ)) ≤ S := by
    intro t ht
    have htD : t < D := Finset.mem_range.1 ht
    have hjlo : k ≤ k + t := Nat.le_add_right _ _
    have hjhi : k + t < 2 ^ k := by omega
    have hcopt : Nat.Coprime (R + (k + t)) A := hcop (k + t) hjlo hjhi
    have heq : ∀ m : ℕ, R + m * A + k + t = (R + (k + t)) + m * A := by intro m; ring
    have hbd : ∀ m, m < 2 ^ (4 * k ^ 12) / B + 1 →
        (R + (k + t)) + m * A ≤ ((2 : ℕ) ^ (3 * k ^ 12)) ^ 2 := by
      intro m hm
      rw [hHsq, ← heq m]
      have := hnZ m hm (k + t) hjhi.le
      omega
    have := sum_tau_progression_le (u := R + (k + t)) (A := A)
      (H := (2 : ℕ) ^ (3 * k ^ 12)) (M := 2 ^ (4 * k ^ 12) / B + 1)
      (by omega) hcopt Nat.one_le_two_pow hbd
    calc (∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1),
            (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ))
        = ∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1),
            (NormalNumbers.SwingC2.tau ((R + (k + t)) + m * A) : ℝ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [heq m]
      _ ≤ S := by rw [hS]; exact this
  have hgeo : ∑ t ∈ Finset.range D, (1 : ℝ) / 2 ^ (k + t) ≤ 2 / 2 ^ k := by
    have : ∀ t ∈ Finset.range D, (1 : ℝ) / 2 ^ (k + t) = (1 / 2 ^ k) * (1 / 2) ^ t := by
      intro t _
      rw [pow_add, div_pow, one_pow]
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    have hg : ∑ t ∈ Finset.range D, (1 / 2 : ℝ) ^ t ≤ 2 := by
      calc ∑ t ∈ Finset.range D, (1 / 2 : ℝ) ^ t
          = (1 - (1/2 : ℝ) ^ D) / (1 - 1/2) := by
            rw [geom_sum_eq (by norm_num)]
            ring_nf
        _ ≤ 2 := by
            have : (0 : ℝ) ≤ (1/2 : ℝ) ^ D := by positivity
            rw [div_le_iff₀ (by norm_num)]
            linarith
    have hpk : (0 : ℝ) < 1 / 2 ^ k := by positivity
    calc (1 / 2 ^ k : ℝ) * ∑ t ∈ Finset.range D, (1 / 2 : ℝ) ^ t
        ≤ (1 / 2 ^ k : ℝ) * 2 := by exact mul_le_mul_of_nonneg_left hg hpk.le
      _ = 2 / 2 ^ k := by ring
  have htotal : ∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1), F m ≤ S * (2 / 2 ^ k) := by
    have hswap : ∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1), F m
        = ∑ t ∈ Finset.range D,
            (∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1),
              (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ)) / 2 ^ (k + t) := by
      rw [hF]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => by rw [Finset.sum_div]
    rw [hswap]
    have hstep : ∀ t ∈ Finset.range D,
        (∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1),
          (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ)) / 2 ^ (k + t)
          ≤ S * (1 / 2 ^ (k + t)) := by
      intro t ht
      rw [mul_one_div, div_le_div_iff_of_pos_right (by positivity)]
      exact hrowbd t ht
    calc ∑ t ∈ Finset.range D,
            (∑ m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1),
              (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ)) / 2 ^ (k + t)
        ≤ ∑ t ∈ Finset.range D, S * (1 / 2 ^ (k + t)) := Finset.sum_le_sum hstep
      _ = S * ∑ t ∈ Finset.range D, (1 : ℝ) / 2 ^ (k + t) := by rw [Finset.mul_sum]
      _ ≤ S * (2 / 2 ^ k) := mul_le_mul_of_nonneg_left hgeo hS0
  -- ### pigeonhole on the prime candidates
  set C := (Finset.range (2 ^ (4 * k ^ 12) / B + 1)).filter
    (fun m => (u + m * B).Prime ∧ u + m * B ≤ 2 ^ (4 * k ^ 12)) with hC
  have hk4pos : (0 : ℝ) < 16 * (k : ℝ) ^ 12 := by positivity
  have hMpos : (0 : ℝ) < ((2 ^ (4 * k ^ 12) / B + 1 : ℕ) : ℝ) := by
    have : 0 < 2 ^ (4 * k ^ 12) / B + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hCpos : (0 : ℝ) < (C.card : ℝ) := lt_of_lt_of_le (by positivity) hcount
  have hCsub : C ⊆ Finset.range (2 ^ (4 * k ^ 12) / B + 1) := Finset.filter_subset _ _
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hCpos
  have hCsum : ∑ m ∈ C, F m ≤ S * (2 / 2 ^ k) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hCsub fun i _ _ => hFnn i) htotal
  obtain ⟨m, hmC, hmF⟩ : ∃ m ∈ C, F m ≤ S * (2 / 2 ^ k) / (C.card : ℝ) := by
    refine Finset.exists_le_of_sum_le hCne ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (ne_of_gt hCpos)]
    exact hCsum
  -- ### the chosen candidate
  have hmC' : m ∈ Finset.range (2 ^ (4 * k ^ 12) / B + 1) ∧
      ((u + m * B).Prime ∧ u + m * B ≤ 2 ^ (4 * k ^ 12)) := by
    rw [hC, Finset.mem_filter] at hmC; exact hmC
  have hmM : m < 2 ^ (4 * k ^ 12) / B + 1 := Finset.mem_range.1 hmC'.1
  have hmprime : (u + m * B).Prime := hmC'.2.1
  set Mr : ℝ := ((2 ^ (4 * k ^ 12) / B + 1 : ℕ) : ℝ) with hMr
  set Hr : ℝ := ((2 ^ (3 * k ^ 12) : ℕ) : ℝ) with hHr
  -- ### the near part is at most `2^(-m₀)`
  have hlogHr : Real.log Hr ≤ 3 * (k : ℝ) ^ 12 := by
    have h1 : Hr = (2 : ℝ) ^ (3 * k ^ 12) := by rw [hHr]; push_cast; ring
    rw [h1, Real.log_pow]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have hnn : (0 : ℝ) ≤ ((3 * k ^ 12 : ℕ) : ℝ) := by positivity
    calc ((3 * k ^ 12 : ℕ) : ℝ) * Real.log 2 ≤ ((3 * k ^ 12 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 hnn
      _ = 3 * (k : ℝ) ^ 12 := by push_cast; ring
  have hHrMr : Hr ≤ Mr := by
    rw [hHr, hMr]; exact_mod_cast hHM
  have hMr0 : (0 : ℝ) < Mr := hMpos
  have hSbd : S ≤ Mr * (6 * (k : ℝ) ^ 12 + 4) := by
    rw [hS]
    nlinarith [hlogHr, hHrMr, hMr0]
  have hnear : F m ≤ (1 / 2 : ℝ) ^ m₀ := by
    have hpos2k : (0 : ℝ) < 2 ^ k := by positivity
    have hstep1 : S * (2 / 2 ^ k) / (C.card : ℝ) ≤ S * (2 / 2 ^ k) / (Mr / (16 * (k : ℝ) ^ 12)) := by
      refine div_le_div_of_nonneg_left (by positivity) ?_ hcount
      positivity
    have hstep2 : S * (2 / 2 ^ k) / (Mr / (16 * (k : ℝ) ^ 12))
        ≤ (Mr * (6 * (k : ℝ) ^ 12 + 4)) * (2 / 2 ^ k) / (Mr / (16 * (k : ℝ) ^ 12)) := by
      gcongr
    have hstep3 : (Mr * (6 * (k : ℝ) ^ 12 + 4)) * (2 / 2 ^ k) / (Mr / (16 * (k : ℝ) ^ 12))
        = (192 * (k : ℝ) ^ 24 + 128 * (k : ℝ) ^ 12) / 2 ^ k := by
      field_simp
      ring
    have hstep4 : (192 * (k : ℝ) ^ 24 + 128 * (k : ℝ) ^ 12) / 2 ^ k
        ≤ (320 * (k : ℝ) ^ 24) / 2 ^ k := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have : 128 * (k : ℝ) ^ 12 ≤ 128 * (k : ℝ) ^ 24 := by
        have := pow_le_pow_right₀ hk1 (show 12 ≤ 24 by norm_num)
        nlinarith
      exact div_le_div_of_nonneg_right (by linarith) hpos2k.le
    have hgrow : Cn * k ^ 24 ≤ 2 ^ k := hKnear k hknear
    have hstep5 : (320 * (k : ℝ) ^ 24) / 2 ^ k ≤ (1 / 2 : ℝ) ^ m₀ := by
      have hgrowR : (320 : ℝ) * 2 ^ m₀ * (k : ℝ) ^ 24 ≤ (2 : ℝ) ^ k := by
        have : ((Cn * k ^ 24 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := Nat.cast_le.2 hgrow
        rw [hCn] at this
        push_cast at this
        linarith
      rw [div_pow, one_pow, div_le_div_iff₀ hpos2k (by positivity)]
      linarith
    calc F m ≤ S * (2 / 2 ^ k) / (C.card : ℝ) := hmF
      _ ≤ S * (2 / 2 ^ k) / (Mr / (16 * (k : ℝ) ^ 12)) := hstep1
      _ ≤ (Mr * (6 * (k : ℝ) ^ 12 + 4)) * (2 / 2 ^ k) / (Mr / (16 * (k : ℝ) ^ 12)) := hstep2
      _ = (192 * (k : ℝ) ^ 24 + 128 * (k : ℝ) ^ 12) / 2 ^ k := hstep3
      _ ≤ (320 * (k : ℝ) ^ 24) / 2 ^ k := hstep4
      _ ≤ (1 / 2 : ℝ) ^ m₀ := hstep5
  -- ### the far part is at most `2^(-m₀)`
  set f : ℕ → ℝ := fun t =>
    (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ) / 2 ^ (k + t) with hf
  have hsumf : Summable f := by
    refine ((summable_tau_div (R + m * A + k)).mul_right ((1 : ℝ) / 2 ^ k)).congr ?_
    intro t
    simp only [hf]
    rw [pow_add]
    ring
  have hFf : F m = ∑ t ∈ Finset.range D, f t := rfl
  have hfar_eq : ∀ i : ℕ, f (i + D)
      = ((1 : ℝ) / 2 ^ (2 ^ k)) *
        ((NormalNumbers.SwingC2.tau (R + m * A + 2 ^ k + i) : ℝ) / 2 ^ i) := by
    intro i
    simp only [hf]
    have h1 : R + m * A + k + (i + D) = R + m * A + 2 ^ k + i := by omega
    have h2 : (2 : ℝ) ^ (k + (i + D)) = 2 ^ (2 ^ k) * 2 ^ i := by
      rw [show k + (i + D) = 2 ^ k + i by omega, pow_add]
    rw [h1, h2]
    field_simp
  have hnL : R + m * A + 2 ^ k ≤ 2 ^ (6 * k ^ 12) := by
    have := hnZ m hmM (2 ^ k) le_rfl
    omega
  have hfar : ∑' i : ℕ, f (i + D) ≤ (1 / 2 : ℝ) ^ m₀ := by
    have hval : ∑' i : ℕ, f (i + D)
        = ((1 : ℝ) / 2 ^ (2 ^ k)) *
          ∑' i : ℕ, (NormalNumbers.SwingC2.tau (R + m * A + 2 ^ k + i) : ℝ) / 2 ^ i := by
      rw [tsum_congr hfar_eq, tsum_mul_left]
    rw [hval]
    have hinner := tsum_tau_div_le (R + m * A + 2 ^ k)
    have hpos : (0 : ℝ) < 2 ^ (2 ^ k) := by positivity
    have hZbd : 2 * ((R + m * A + 2 ^ k : ℕ) : ℝ) + 2 ≤ 4 * ((2 ^ (6 * k ^ 12) : ℕ) : ℝ) := by
      have h1 : ((R + m * A + 2 ^ k : ℕ) : ℝ) ≤ ((2 ^ (6 * k ^ 12) : ℕ) : ℝ) :=
        Nat.cast_le.2 hnL
      have h2 : (1 : ℝ) ≤ ((2 ^ (6 * k ^ 12) : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_two_pow
      linarith
    have hgrow : m₀ + 2 + 6 * k ^ 12 ≤ 2 ^ k := by
      have h := hKfar k hkfar
      have hk12 : 1 ≤ k ^ 12 := Nat.one_le_pow _ _ (by omega)
      have h1 : 2 ≤ 2 * k ^ 12 := by omega
      have h2 : m₀ ≤ m₀ * k ^ 12 := Nat.le_mul_of_pos_right _ (by omega)
      have h3 : (8 + m₀) * k ^ 12 = 8 * k ^ 12 + m₀ * k ^ 12 := by ring
      omega
    have hfinal : 4 * ((2 ^ (6 * k ^ 12) : ℕ) : ℝ) / 2 ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ m₀ := by
      have hnat : 2 ^ (2 + 6 * k ^ 12 + m₀) ≤ 2 ^ (2 ^ k) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hnatR : ((2 ^ (2 + 6 * k ^ 12 + m₀) : ℕ) : ℝ) ≤ ((2 ^ (2 ^ k) : ℕ) : ℝ) :=
        Nat.cast_le.2 hnat
      push_cast at hnatR
      rw [div_pow, one_pow, div_le_div_iff₀ hpos (by positivity)]
      push_cast
      calc 4 * (2 : ℝ) ^ (6 * k ^ 12) * 2 ^ m₀
          = (2 : ℝ) ^ (2 + 6 * k ^ 12 + m₀) := by rw [pow_add, pow_add]; norm_num
        _ ≤ (2 : ℝ) ^ (2 ^ k) := hnatR
        _ = 1 * (2 : ℝ) ^ (2 ^ k) := by ring
    calc ((1 : ℝ) / 2 ^ (2 ^ k)) *
          ∑' i : ℕ, (NormalNumbers.SwingC2.tau (R + m * A + 2 ^ k + i) : ℝ) / 2 ^ i
        ≤ ((1 : ℝ) / 2 ^ (2 ^ k)) * (2 * ((R + m * A + 2 ^ k : ℕ) : ℝ) + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using hinner
      _ ≤ ((1 : ℝ) / 2 ^ (2 ^ k)) * (4 * ((2 ^ (6 * k ^ 12) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hZbd (by positivity)
      _ = 4 * ((2 ^ (6 * k ^ 12) : ℕ) : ℝ) / 2 ^ (2 ^ k) := by ring
      _ ≤ (1 / 2 : ℝ) ^ m₀ := hfinal
  -- ### assemble
  refine ⟨k, R + m * A, hkK, hkr, by omega, ?_, fun j hj hjr => hkill m j hj hjr,
    hsurv m hmprime, ?_⟩
  · have : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    omega
  · have hsplit := hsumf.sum_add_tsum_nat_add D
    have hgoal : ∑' t : ℕ, (NormalNumbers.SwingC2.tau (R + m * A + k + t) : ℝ) / 2 ^ (k + t)
        = ∑' t : ℕ, f t := rfl
    rw [hgoal, ← hsplit, ← hFf]
    linarith [hnear, hfar, hm₀]

/-- **The same `n` works in every base.**  Combining `exists_joint_small_tail` with the
base majorant `base_tail_le_half_binary_tail`: there is one common offset `n` whose
prescribed divisor data holds at every slot `j < k` and whose *base-`b`* tail is below
`ε/2` simultaneously for **all** integer bases `b ≥ 2`.  This is the form the
common-offset digit assembly consumes. -/
theorem exists_joint_small_tail_all_bases_rescaled
    {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) (K N : ℕ) :
    ∃ k n : ℕ, K ≤ k ∧ r < k ∧ 1 ≤ n ∧ N ≤ n ∧
      (∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ NormalNumbers.SwingC2.tau (n + j)) ∧
      NormalNumbers.SwingC2.tau (n + r) = 2 * a ∧
      ∑' t : ℕ, (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) < ε ∧
      ∀ b : ℕ, 2 ≤ b →
        0 ≤ ∑' t : ℕ, (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) ∧
        ∑' t : ℕ,
          (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) < ε / 2 := by
  obtain ⟨k, n, hkK, hkr, hn1, hnN, hkill, hsurv, htail⟩ :=
    exists_joint_small_tail_rescaled hc ha hr hε K N
  refine ⟨k, n, hkK, hkr, hn1, hnN, hkill, hsurv, htail, fun b hb => ?_⟩
  obtain ⟨h0, hle⟩ := base_tail_le_half_binary_tail n k hb
  exact ⟨h0, lt_of_le_of_lt hle (by linarith)⟩

end NormalNumbers.JointLambert
