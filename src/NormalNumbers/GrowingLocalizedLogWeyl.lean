/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GrowingLocalizedLogAssembly
import NormalNumbers.GrowingLocalizedLogWitness

/-!
# N9 completed: `Σ_{n<N} e(h R_n) = o(N)`

`weyl_Rs` runs `main_bound` at every large `N`, with `L = ⌊log₂ N⌋`, `ℓ = ⌊log₂ L⌋`,
`G = 2^{(ℓ+1)^3}` blocks and `H = ⌊N/G⌋`.  The growth hypothesis
`π(Z N) ≤ (1−ε) log₂ log N` gives `π ≤ ℓ+1` and `2^π ≤ (log N)^{1−ε}`.  So the depth satisfies
`k ≤ π + 3`, the cost is `≤ 2^{62(ℓ+3)^4}`, and the saving is
`H^{2^{−k−4}} ≥ exp((log N)^ε/512) ≥ exp(2^{εℓ}/(512·2^ε))`.
-/

namespace NormalNumbers.GrowingLocalizedLog

open Finset Filter NormalNumbers.Literature.VandeheyDiff NormalNumbers.G4

set_option maxHeartbeats 1000000 in
/-- The analytic core at one scale: the saving beats the cost. -/
theorem saving_beats_cost {N L ℓ g H π k c' : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hc' : 4 / δ ≤ (2 : ℝ) ^ c')
    (hNL : 2 ^ L ≤ N) (hNL' : N < 2 ^ (L + 1)) (hLℓ : 2 ^ ℓ ≤ L) (hLℓ' : L < 2 ^ (ℓ + 1))
    (hgL : 2 * g ≤ L) (hH : 2 ^ (L - g) ≤ H) (hπ : π ≤ ℓ + 1) (hk : k ≤ π + 3)
    (hπN : (2 : ℝ) ^ (π : ℝ) ≤ Real.log N ^ (1 - ε))
    (hbig : 512 * Real.exp (ε * Real.log 2) * ((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4 ≤
      Real.exp (ε * Real.log 2 * ℓ)) :
    (2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * (1 + π * Real.log N) ≤
      δ / 4 * (H : ℝ) ^ (1 / (2 : ℝ) ^ (k + 4)) := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hL1 : 1 ≤ L := le_trans (Nat.one_le_two_pow) hLℓ
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (Nat.two_pow_pos L) hNL
    exact_mod_cast this
  -- `log N` versus `L`
  have s1 : (L : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast hNL)
  have s2 : Real.log N ≤ (L + 1) * Real.log 2 := by
    have : Real.log N ≤ Real.log ((2 : ℝ) ^ (L + 1)) :=
      Real.log_le_log hN0 (by exact_mod_cast hNL'.le)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hlN0 : 0 < Real.log N := by nlinarith
  -- `log H ≥ log N / 4`
  have hH0 : 0 < H := lt_of_lt_of_le (Nat.two_pow_pos _) hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH0
  have s3 : ((L - g : ℕ) : ℝ) * Real.log 2 ≤ Real.log H := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast hH)
  have hLg : (L : ℝ) / 2 ≤ ((L - g : ℕ) : ℝ) := by
    have : L ≤ 2 * (L - g) := by omega
    have : (L : ℝ) ≤ 2 * ((L - g : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have s4 : Real.log N / 4 ≤ Real.log H := by nlinarith
  -- the cost side, as a power of two
  have hcost : (2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * (1 + π * Real.log N) ≤
      (2 : ℝ) ^ (62 * (ℓ + 3) ^ 4) := by
    have e1 : 60 * (π + 2) ^ 4 + (k + 5) * π ≤ 61 * (ℓ + 3) ^ 4 := by
      have h1 : (π + 2) ^ 4 ≤ (ℓ + 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have h2 : (k + 5) * π ≤ (ℓ + 9) * (ℓ + 1) := Nat.mul_le_mul (by omega) hπ
      have h3 : (ℓ + 9) * (ℓ + 1) ≤ (ℓ + 3) ^ 4 := by
        have a1 : (ℓ + 9) * (ℓ + 1) ≤ (ℓ + 3) ^ 3 := by ring_nf; nlinarith
        exact a1.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
      omega
    have e2 : (1 + π * Real.log N) ≤ (2 : ℝ) ^ (2 * ℓ + 4) := by
      have h1 : (π : ℝ) ≤ ℓ + 1 := by exact_mod_cast hπ
      have h2 : Real.log N ≤ 2 * L := by nlinarith
      have h3 : (L : ℝ) < 2 ^ (ℓ + 1) := by exact_mod_cast hLℓ'
      have h4 : (ℓ : ℝ) + 1 ≤ 2 ^ (ℓ + 1) := by
        have := two_pow_ge (ℓ + 1); push_cast at this; linarith
      have hp : (2 : ℝ) ^ (2 * ℓ + 4) = 4 * (2 ^ (ℓ + 1) * 2 ^ (ℓ + 1)) := by
        rw [← pow_add]; rw [show 2 * ℓ + 4 = 2 + (ℓ + 1 + (ℓ + 1)) by ring, pow_add]; norm_num
      have hπ0 : (0 : ℝ) ≤ π := by positivity
      have : (π : ℝ) * Real.log N ≤ (2 ^ (ℓ + 1)) * (2 * 2 ^ (ℓ + 1)) := by
        apply mul_le_mul (h1.trans h4) (by linarith) hlN0.le (by positivity)
      have : (1 : ℝ) ≤ 2 ^ (ℓ + 1) * 2 ^ (ℓ + 1) := one_le_mul_of_one_le_of_one_le
        (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
      nlinarith
    have e3 : 2 * ℓ + 4 ≤ (ℓ + 3) ^ 4 := by
      have a1 : 2 * ℓ + 4 ≤ (ℓ + 3) ^ 2 := by ring_nf; nlinarith
      exact a1.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    calc (2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * (1 + π * Real.log N)
        ≤ (2 : ℝ) ^ (60 * (π + 2) ^ 4) * 2 ^ ((k + 5) * π) * 2 ^ (2 * ℓ + 4) := by gcongr
      _ = 2 ^ (60 * (π + 2) ^ 4 + (k + 5) * π + (2 * ℓ + 4)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (62 * (ℓ + 3) ^ 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- the saving side
  set lN := Real.log N
  have hpow2 : (2 : ℝ) ^ (π + 7) ≤ 128 * lN ^ (1 - ε) := by
    have : (2 : ℝ) ^ (π + 7) = (2 : ℝ) ^ (π : ℝ) * 128 := by
      rw [pow_add, Real.rpow_natCast]; norm_num
    rw [this]; linarith
  have hsplit : lN = lN ^ (1 - ε) * lN ^ ε := by
    rw [← Real.rpow_add hlN0]; simp
  have hlNe : 0 < lN ^ ε := Real.rpow_pos_of_pos hlN0 _
  have hlN1e : 0 < lN ^ (1 - ε) := Real.rpow_pos_of_pos hlN0 _
  have s8 : lN ^ ε / 512 ≤ Real.log H / 2 ^ (π + 7) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : lN ^ ε * 2 ^ (π + 7) ≤ lN ^ ε * (128 * lN ^ (1 - ε)) :=
      mul_le_mul_of_nonneg_left hpow2 hlNe.le
    nlinarith
  have s9 : Real.exp (ε * Real.log 2 * ℓ) / Real.exp (ε * Real.log 2) ≤ lN ^ ε := by
    have hb : (2 : ℝ) ^ ℓ / 2 ≤ lN := by
      have : ((2 : ℝ) ^ ℓ) ≤ L := by exact_mod_cast hLℓ
      nlinarith
    have hpos : (0 : ℝ) < 2 ^ ℓ / 2 := by positivity
    calc Real.exp (ε * Real.log 2 * ℓ) / Real.exp (ε * Real.log 2)
        = ((2 : ℝ) ^ ℓ / 2) ^ ε := by
          rw [← Real.exp_sub, Real.rpow_def_of_pos hpos, Real.log_div (by positivity)
            (by norm_num), Real.log_pow]; ring_nf
      _ ≤ lN ^ ε := Real.rpow_le_rpow hpos.le hb hε.le
  have hbe : 0 < Real.exp (ε * Real.log 2) := Real.exp_pos _
  have hX : ((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4 ≤ Real.log H / 2 ^ (π + 7) := by
    have : ((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4 ≤
        Real.exp (ε * Real.log 2 * ℓ) / Real.exp (ε * Real.log 2) / 512 := by
      rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have ha : 1 / (2 : ℝ) ^ (π + 7) ≤ 1 / (2 : ℝ) ^ (k + 4) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlogH0 : 0 ≤ Real.log H := by linarith
  have hHa : Real.exp (((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4) ≤
      (H : ℝ) ^ (1 / (2 : ℝ) ^ (k + 4)) := by
    rw [Real.rpow_def_of_pos hHr]
    apply Real.exp_le_exp.2
    calc ((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4 ≤ Real.log H / 2 ^ (π + 7) := hX
      _ = Real.log H * (1 / 2 ^ (π + 7)) := by ring
      _ ≤ Real.log H * (1 / 2 ^ (k + 4)) := mul_le_mul_of_nonneg_left ha hlogH0
  -- combine: `2^{62(ℓ+3)^4} ≤ (δ/4) exp((62+c') log 2 (ℓ+3)^4)`
  have hfin : (2 : ℝ) ^ (62 * (ℓ + 3) ^ 4) ≤
      δ / 4 * Real.exp (((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4) := by
    have e : Real.exp (((62 + c') * Real.log 2) * ((ℓ : ℝ) + 3) ^ 4) =
        (2 : ℝ) ^ (62 * (ℓ + 3) ^ 4) * Real.exp (c' * Real.log 2 * ((ℓ : ℝ) + 3) ^ 4) := by
      have h2 : (2 : ℝ) ^ (62 * (ℓ + 3) ^ 4) =
          Real.exp (Real.log 2 * ((62 : ℝ) * ((ℓ : ℝ) + 3) ^ 4)) := by
        rw [← Real.rpow_def_of_pos two_pos, ← Real.rpow_natCast]; push_cast; ring_nf
      rw [h2, ← Real.exp_add]; ring_nf
    have h1 : (2 : ℝ) ^ c' ≤ Real.exp (c' * Real.log 2 * ((ℓ : ℝ) + 3) ^ 4) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos]
      apply Real.exp_le_exp.2
      have : (1 : ℝ) ≤ ((ℓ : ℝ) + 3) ^ 4 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) ℓ])
      have : 0 ≤ (c' : ℝ) * Real.log 2 := by positivity
      nlinarith
    rw [e]
    have h4 : 1 ≤ δ / 4 * Real.exp (c' * Real.log 2 * ((ℓ : ℝ) + 3) ^ 4) := by
      have : 4 / δ ≤ Real.exp (c' * Real.log 2 * ((ℓ : ℝ) + 3) ^ 4) := hc'.trans h1
      rw [div_le_iff₀ hδ] at this; linarith
    have hp : (0 : ℝ) ≤ 2 ^ (62 * (ℓ + 3) ^ 4) := by positivity
    nlinarith
  calc _ ≤ (2 : ℝ) ^ (62 * (ℓ + 3) ^ 4) := hcost
    _ ≤ _ := hfin
    _ ≤ δ / 4 * (H : ℝ) ^ (1 / (2 : ℝ) ^ (k + 4)) := by gcongr

end NormalNumbers.GrowingLocalizedLog
