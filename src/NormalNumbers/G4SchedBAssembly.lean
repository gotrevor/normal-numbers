/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBBudget
import NormalNumbers.G4ScheduleB
import NormalNumbers.G4ScheduleAssembly

/-!
# G4B §5 assembly: the schedule witness in base `b ≥ 3`, and **`isDisjunctive_base`**

For every base `b ≥ 3` and every omitted base-`b` cylinder `[w/b^ℓ, (w+1)/b^ℓ)` with `ℓ ≥ 1`
we build a `ScheduleWitnessB b ℓ w` from the explicit schedule

    k₄ = 8464·ℓ²·b^{2ℓ+2},  K = 4k₄,  M = ⌈K log 2 / (4ℓ log b)⌉
    G = gridOf K (Sched.N K),  X = X b K,  η = 2^{−k₄},  ε = 1/K,  D = Dj K k₄
    R = R b K, Y = Y b K, Mc = Mc b K, lam' = e, lam = 13/2, δ's = 1/8.

The five inequalities: `hB` is `G4ScheduleB.gridB_bound` (already base-general; the `K`
hypothesis `8464 ℓ² b^{2ℓ} ⌈log₂ b⌉² ≤ K` holds because `⌈log₂ b⌉ ≤ b`), `hbudget` is
`SchedB.hbudget_holds`, and `hbig`, `hfar` are proved here at the worst case `b = 3`:
`rowL1 b K ≤ (2/3)^K/2 ≤ η²/2`, `rowL2 b K ≤ (2/9)^K/8 ≤ η⁸/8`, `farBound b ≤ farBound 3`
(`η = 2^{−K/4}`, and `(2/3)⁴ < 1/4`, `(2/9)⁴ < 1/256`).  The result is
`isDisjunctive_base : 3 ≤ b → IsDisjunctive b (primeLambertAtBase b)`, with
`isDisjunctive_four'` the `b = 4` instance.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (J W H T logP₀Nat m₂ Dj T_pos N_pos logP₀Nat_le J_le m_le pow_le_two_pow_mul
  two_Dj_add_one_le k₄_bounds)

/-! ### The schedule in `(b, ℓ)` -/

/-- `k₄ = 8464·ℓ²·b^{2ℓ+2}`. -/
def k₄bℓ (b ℓ : ℕ) : ℕ := 8464 * ℓ ^ 2 * b ^ (2 * ℓ + 2)
/-- `K = 4k₄`. -/
def Kbℓ (b ℓ : ℕ) : ℕ := 4 * k₄bℓ b ℓ

lemma clog_two_le_self (b : ℕ) : Nat.clog 2 b ≤ b :=
  (Nat.clog_le_iff_le_pow (by norm_num)).2 (Nat.lt_two_pow_self).le

lemma Kbℓ_ge {b ℓ : ℕ} :
    8464 * ℓ ^ 2 * b ^ (2 * ℓ) * Nat.clog 2 b ^ 2 ≤ Kbℓ b ℓ := by
  unfold Kbℓ k₄bℓ
  have h := clog_two_le_self b
  have h2 : Nat.clog 2 b ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h 2
  calc 8464 * ℓ ^ 2 * b ^ (2 * ℓ) * Nat.clog 2 b ^ 2
      ≤ 8464 * ℓ ^ 2 * b ^ (2 * ℓ) * b ^ 2 := by gcongr
    _ = 8464 * ℓ ^ 2 * b ^ (2 * ℓ + 2) := by rw [pow_add]; ring
    _ ≤ 4 * (8464 * ℓ ^ 2 * b ^ (2 * ℓ + 2)) := Nat.le_mul_of_pos_left _ (by norm_num)

lemma hyp_Kbℓ {b ℓ : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) : Hyp b (Kbℓ b ℓ) := by
  have hb2 : b ^ 2 ≤ b ^ (2 * ℓ + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hℓ2 : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ
  have hb9 : 9 ≤ b ^ 2 := by nlinarith
  refine ⟨hb, ?_, ?_⟩ <;> unfold Kbℓ k₄bℓ <;> nlinarith

/-- `M = ⌈K log 2 / (4 ℓ log b)⌉`. -/
noncomputable def Mbℓ (b ℓ : ℕ) : ℕ :=
  ⌈(Kbℓ b ℓ : ℝ) * Real.log 2 / (4 * ℓ * Real.log b)⌉₊

lemma Mbℓ_lo {b ℓ : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    (Kbℓ b ℓ : ℝ) / 4 * Real.log 2 ≤ (Mbℓ b ℓ : ℝ) * ℓ * Real.log b := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hden : 0 < 4 * (ℓ : ℝ) * Real.log b := by positivity
  have h := Nat.le_ceil ((Kbℓ b ℓ : ℝ) * Real.log 2 / (4 * ℓ * Real.log b))
  unfold Mbℓ
  rw [div_le_iff₀ hden] at h
  nlinarith

lemma Mbℓ_hi {b ℓ : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    (Mbℓ b ℓ : ℝ) * ℓ * Real.log b ≤ (Kbℓ b ℓ : ℝ) / 4 * Real.log 2 + ℓ * Real.log b := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hden : 0 < 4 * (ℓ : ℝ) * Real.log b := by positivity
  have hnn : 0 ≤ (Kbℓ b ℓ : ℝ) * Real.log 2 / (4 * ℓ * Real.log b) := by
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
  have h := Nat.ceil_lt_add_one hnn
  unfold Mbℓ
  have h' : (⌈(Kbℓ b ℓ : ℝ) * Real.log 2 / (4 * ℓ * Real.log b)⌉₊ : ℝ) * (4 * ℓ * Real.log b)
      < (Kbℓ b ℓ : ℝ) * Real.log 2 + 4 * ℓ * Real.log b := by
    have := mul_lt_mul_of_pos_right h hden
    rwa [add_mul, div_mul_cancel₀ _ hden.ne', one_mul] at this
  nlinarith [h']

/-- `hM`: `b^{−ℓM} ≤ 2^{−k₄}`. -/
lemma hM_holds {b ℓ : ℕ} (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    1 / ((b : ℝ) ^ ℓ) ^ Mbℓ b ℓ ≤ (1 / 2 : ℝ) ^ k₄bℓ b ℓ := by
  have hbr : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hlo := Mbℓ_lo hb hℓ
  have hK4 : (Kbℓ b ℓ : ℝ) / 4 = k₄bℓ b ℓ := by unfold Kbℓ; push_cast; ring
  rw [hK4] at hlo
  have e1 : ((b : ℝ) ^ ℓ) ^ Mbℓ b ℓ = Real.exp ((Mbℓ b ℓ : ℝ) * ℓ * Real.log b) := by
    rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    push_cast; ring_nf
  have e2 : (2 : ℝ) ^ k₄bℓ b ℓ = Real.exp ((k₄bℓ b ℓ : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [one_div_pow, e1, one_div, one_div, e2]
  exact inv_anti₀ (Real.exp_pos _) (Real.exp_le_exp.2 hlo)

/-- `hN`: `2^K · D ≤ 2^{N−1}`, hence `1 + ⌈log_b(2^K D)⌉ ≤ N` for every `b ≥ 2`. -/
lemma two_pow_mul_Dj_le_two_pow {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    2 ^ K * Dj K k₄ ≤ 2 ^ (Sched.N K - 1) := by
  have hk : 25 ≤ k₄ := by omega
  have h1 := two_Dj_add_one_le hK4 hk
  have h4 : (4 : ℕ) ^ K = 2 ^ (2 * K) := by rw [pow_mul]; norm_num
  have h2 : 2 ^ K * Dj K k₄ ≤ 2 ^ K * 2 ^ (2 * K) := by
    rw [← h4]; exact Nat.mul_le_mul_left _ (by omega)
  rw [← pow_add] at h2
  refine h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold Sched.N
  have : 3 * K + 1 ≤ 100 * K ^ 2 := by nlinarith
  omega

lemma hN_holds {b K k₄ : ℕ} (hb : 2 ≤ b) (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    1 + Nat.clog b (2 ^ K * Dj K k₄) ≤ Sched.N K := by
  have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 (two_pow_mul_Dj_le_two_pow hK4 hK)
  have h' := Nat.clog_anti_left (b := b) (c := 2) (n := 2 ^ K * Dj K k₄) (by norm_num) hb
  have hN : 1 ≤ Sched.N K := N_pos (by omega)
  omega

/-! ### The row masses at the worst case `b = 3`, against `η = 2^{−k₄}` -/

lemma rowL1_le_three {b : ℕ} (hb : 3 ≤ b) (K : ℕ) : rowL1 b K ≤ (2 / 3 : ℝ) ^ K / 2 := by
  unfold rowL1
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : (2 : ℝ) / b ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2 : (0 : ℝ) ≤ 2 / b := by positivity
  have h3 : (2 : ℝ) ≤ b - 1 := by linarith
  calc (2 / (b : ℝ)) ^ K / (b - 1) ≤ (2 / 3 : ℝ) ^ K / (b - 1) := by gcongr
    _ ≤ (2 / 3 : ℝ) ^ K / 2 := by gcongr

lemma rowL2_le_three {b : ℕ} (hb : 3 ≤ b) (K : ℕ) : rowL2 b K ≤ (2 / 9 : ℝ) ^ K / 8 := by
  unfold rowL2
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hb2 : (9 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
  have h1 : (2 : ℝ) / (b : ℝ) ^ 2 ≤ 2 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : (0 : ℝ) ≤ 2 / (b : ℝ) ^ 2 := by positivity
  have h3 : (8 : ℝ) ≤ (b : ℝ) ^ 2 - 1 := by linarith
  calc (2 / (b : ℝ) ^ 2) ^ K / ((b : ℝ) ^ 2 - 1) ≤ (2 / 9 : ℝ) ^ K / ((b : ℝ) ^ 2 - 1) := by gcongr
    _ ≤ (2 / 9 : ℝ) ^ K / 8 := by gcongr

lemma two_thirds_pow_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) :
    (2 / 3 : ℝ) ^ K ≤ ((1 / 2 : ℝ) ^ k₄) ^ 2 := by
  calc (2 / 3 : ℝ) ^ K = ((2 / 3 : ℝ) ^ 4) ^ k₄ := by rw [hK4, pow_mul]
    _ ≤ ((1 / 2 : ℝ) ^ 2) ^ k₄ := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ = ((1 / 2 : ℝ) ^ k₄) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]

lemma two_ninths_pow_le {K k₄ : ℕ} (hK4 : K = 4 * k₄) :
    (2 / 9 : ℝ) ^ K ≤ ((1 / 2 : ℝ) ^ k₄) ^ 8 := by
  calc (2 / 9 : ℝ) ^ K = ((2 / 9 : ℝ) ^ 4) ^ k₄ := by rw [hK4, pow_mul]
    _ ≤ ((1 / 2 : ℝ) ^ 8) ^ k₄ := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ = ((1 / 2 : ℝ) ^ k₄) ^ 8 := by rw [← pow_mul, ← pow_mul, mul_comm]

/-- `Y²/|P| ≤ 2^{−K}/2`. -/
lemma sample_ratio_le {b K : ℕ} (h : Hyp b K) :
    (Y b K : ℝ) ^ 2 / ((apSample (X b K) (gridOf K (Sched.N K) h.hK1).P₀ (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ)
      ≤ (1 / 2 : ℝ) ^ K / 2 := by
  have hK := h.hK
  set G := gridOf K (Sched.N K) h.hK1 with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXr : (0 : ℝ) < X b K := by unfold X; positivity
  have hcard := Sched.card_apSample_ge_half (X b K) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ (two_mul_P₀_le_X h)
  have hcard0 : (0 : ℝ) < (apSample (X b K) G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X b K : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hP₀2 := P₀_le_two_pow h
  have hY : (Y b K : ℝ) ^ 2 = (2 : ℝ) ^ (2 * 2 ^ m b K) := by
    unfold Y; push_cast; rw [← pow_mul]; ring_nf
  have hX : (X b K : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m b K) := by unfold X; push_cast; rfl
  have hkey : (Y b K : ℝ) ^ 2 * G.P₀ * 4 ≤ (X b K : ℝ) * (1 / 2 : ℝ) ^ K := by
    have hpow : (2 : ℝ) ^ (2 * 2 ^ m b K) * (2 : ℝ) ^ (2 * 2 ^ m b K) * 4 * (2 : ℝ) ^ K
        ≤ (2 : ℝ) ^ (100 * 2 ^ m b K) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have h1 : K ≤ 2 ^ m b K := by
        calc K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
          _ ≤ m₁ b K := m₁_ge_cube h.hb h.hK1
          _ ≤ m b K := m₁_le_m b K
          _ ≤ 2 ^ m b K := (Nat.lt_two_pow_self).le
      have h2 : 2 ≤ 2 ^ m b K := by
        calc 2 ≤ K := by omega
          _ ≤ 2 ^ m b K := h1
      omega
    have hη : (1 / 2 : ℝ) ^ K = 1 / (2 : ℝ) ^ K := by rw [one_div_pow]
    rw [hY, hX, hη]
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (2 * 2 ^ m b K) * G.P₀ * 4 * 2 ^ K
        ≤ (2 : ℝ) ^ (2 * 2 ^ m b K) * (2 : ℝ) ^ (2 * 2 ^ m b K) * 4 * 2 ^ K := by gcongr
      _ ≤ _ := hpow
  rw [div_le_iff₀ hcard0]
  have hc : (X b K : ℝ) / (2 * G.P₀) ≤ (apSample (X b K) G.P₀ G.b₀).card := hcard
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
  calc (Y b K : ℝ) ^ 2 = ((Y b K : ℝ) ^ 2 * G.P₀ * 4) / (4 * G.P₀) := by field_simp
    _ ≤ ((X b K : ℝ) * (1 / 2 : ℝ) ^ K) / (4 * G.P₀) := by gcongr
    _ = (1 / 2 : ℝ) ^ K / 2 * ((X b K : ℝ) / (2 * G.P₀)) := by field_simp; ring
    _ ≤ (1 / 2 : ℝ) ^ K / 2 * (apSample (X b K) G.P₀ G.b₀).card := by gcongr

lemma k₄_bound_three {k₄ : ℕ} (hk : 25 ≤ k₄) : 512 * k₄ ^ 2 ≤ 2 ^ (3 * k₄) := by
  have h1 : k₄ ^ 2 ≤ 2 ^ (2 * k₄) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  calc 512 * k₄ ^ 2 ≤ 2 ^ 9 * 2 ^ (2 * k₄) := by gcongr; norm_num
    _ = 2 ^ (9 + 2 * k₄) := by rw [← pow_add]
    _ ≤ 2 ^ (3 * k₄) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma k₄_bound_one {k₄ : ℕ} (hk : 25 ≤ k₄) : 4096 * k₄ ≤ 2 ^ k₄ := by
  obtain ⟨t, rfl⟩ : ∃ t, k₄ = t + 12 := ⟨k₄ - 12, by omega⟩
  have ht : 13 ≤ t := by omega
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have hu : u < 2 ^ u := Nat.lt_two_pow_self
  have h2 : 2 * (u + 1) ≤ 2 ^ (u + 1) := by rw [pow_succ]; omega
  have h3 : u + 1 + 12 ≤ 2 * (u + 1) := by omega
  calc 4096 * (u + 1 + 12) ≤ 4096 * 2 ^ (u + 1) := by
        apply Nat.mul_le_mul_left; omega
    _ = 2 ^ (u + 1 + 12) := by rw [pow_add]; norm_num; ring

/-- **`hbig` in base `b ≥ 3`**, with `K = 4k₄`, `η = 2^{−k₄}`, `ε = 1/K`, `δbig = 1/8`,
`Mx = X + J·Dm`. -/
theorem hbig_holds {b K k₄ : ℕ} (hK4 : K = 4 * k₄) (h : Hyp b K) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y b K)) - Real.log (Nat.log 2 (R b K))) * rowL2 b K
          + 2 * (Y b K : ℝ) ^ 2 * (rowL1 b K) ^ 2
            / ((apSample (X b K) (gridOf K (Sched.N K) h.hK1).P₀ (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ))
      + (Real.log ((X b K + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (Y b K)) * rowL1 b K
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.hb; have hK := h.hK
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hb1r : (512 : ℝ) * k₄ ^ 2 ≤ 2 ^ (3 * k₄) := by exact_mod_cast k₄_bound_three hk
  have hb2r : (4096 : ℝ) * k₄ ≤ 2 ^ k₄ := by exact_mod_cast k₄_bound_one hk
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hL1 : rowL1 b K ≤ a ^ 2 / 2 := by
    have := rowL1_le_three hb K; have := two_thirds_pow_le (k₄ := k₄) hK4; linarith
  have hL2 : rowL2 b K ≤ a ^ 8 / 8 := by
    have := rowL2_le_three hb K; have := two_ninths_pow_le (k₄ := k₄) hK4; linarith
  have hL10 := rowL1_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
  have hL20 := rowL2_nonneg (by exact_mod_cast (show 2 ≤ b by omega) : (2:ℝ) ≤ b) K
  set Psz : ℝ := ((apSample (X b K) (gridOf K (Sched.N K) h.hK1).P₀ (gridOf K (Sched.N K) h.hK1).b₀).card : ℝ)
    with hPsz
  have hPsz0 : 0 < Psz := by
    rw [hPsz]; exact_mod_cast (sample_nonempty h).card_pos
  -- the square root
  have hs1 := dyadic_factor_le b K
  have hs2 := sample_ratio_le h
  rw [← hPsz] at hs2
  have hsq : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y b K)) - Real.log (Nat.log 2 (R b K))) * rowL2 b K
        + 2 * (Y b K : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz) ≤ 2 * K * a ^ 4 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hfac : 4 * (1 + Real.log (Nat.log 2 (Y b K)) - Real.log (Nat.log 2 (R b K))) * rowL2 b K
        ≤ 4 * (1 + 6 * (K : ℝ) ^ 2) * (a ^ 8 / 8) := by
      have h0 : 0 ≤ 1 + Real.log (Nat.log 2 (Y b K)) - Real.log (Nat.log 2 (R b K)) := by
        have hRY : Nat.log 2 (R b K) ≤ Nat.log 2 (Y b K) := by
          rw [natLog_R, natLog_Y]; exact Nat.pow_le_pow_right (by norm_num) (m₁_le_m b K)
        have hRpos : (0 : ℝ) < Nat.log 2 (R b K) := by
          rw [natLog_R]; positivity
        have hRY' : (Nat.log 2 (R b K) : ℝ) ≤ (Nat.log 2 (Y b K) : ℝ) := by exact_mod_cast hRY
        have := Real.log_le_log hRpos hRY'
        linarith
      gcongr
    have hsamp : 2 * (Y b K : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz ≤ a ^ 8 / 4 := by
      have h2K : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4]; ring_nf
      have hL1sq : (rowL1 b K) ^ 2 ≤ (a ^ 2 / 2) ^ 2 := by gcongr
      calc 2 * (Y b K : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz
          = 2 * (rowL1 b K) ^ 2 * ((Y b K : ℝ) ^ 2 / Psz) := by ring
        _ ≤ 2 * (a ^ 2 / 2) ^ 2 * ((1 / 2 : ℝ) ^ K / 2) := by gcongr
        _ = a ^ 8 / 4 := by rw [h2K]; ring
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have ha8 : 0 ≤ a ^ 8 := by positivity
    calc 4 * (1 + Real.log (Nat.log 2 (Y b K)) - Real.log (Nat.log 2 (R b K))) * rowL2 b K
          + 2 * (Y b K : ℝ) ^ 2 * (rowL1 b K) ^ 2 / Psz
        ≤ 4 * (1 + 6 * (K : ℝ) ^ 2) * (a ^ 8 / 8) + a ^ 8 / 4 := add_le_add hfac hsamp
      _ ≤ 4 * (K : ℝ) ^ 2 * a ^ 8 := by nlinarith
      _ = (2 * K * a ^ 4) ^ 2 := by ring
  -- the third term
  have ht3 : (Real.log ((X b K + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (Y b K)) * rowL1 b K
      ≤ 51 * a ^ 2 := by
    have := log_Mx_div_le h
    have hl : 0 ≤ Real.log ((X b K + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (Y b K) := by
      apply div_nonneg
      · apply Real.log_nonneg
        have hX1 : (1 : ℝ) ≤ X b K := by unfold X; exact_mod_cast Nat.one_le_two_pow
        push_cast
        have := (Nat.cast_nonneg (J K) : (0 : ℝ) ≤ _)
        have := (Nat.cast_nonneg (gridDm K (Sched.N K)) : (0 : ℝ) ≤ _)
        nlinarith
      · apply Real.log_nonneg; unfold Y; push_cast; exact one_le_pow₀ (by norm_num)
    calc (Real.log ((X b K + J K * gridDm K (Sched.N K) : ℕ) : ℝ) / Real.log (Y b K)) * rowL1 b K
        ≤ 101 * (a ^ 2 / 2) := by gcongr
      _ ≤ 51 * a ^ 2 := by nlinarith
  -- close: `2K a⁴ ≤ (1/16)(1/K) a` and `51 a² ≤ (1/16)(1/K) a`
  have hc1 : 2 * K * a ^ 4 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have : (32 : ℝ) * K ^ 2 * a ^ 3 ≤ 1 := by
      have e : a ^ 3 = 1 / (2 : ℝ) ^ (3 * k₄) := by rw [ha, ← pow_mul, one_div_pow, mul_comm]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  have hc2 : 51 * a ^ 2 ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := by
    have : (816 : ℝ) * K * a ≤ 1 := by
      have e : a = 1 / (2 : ℝ) ^ k₄ := by rw [ha, one_div_pow]
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      nlinarith
    rw [show (1 / 16 : ℝ) * ((1 / K : ℝ) * a) = a / (16 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [ha0]
  calc _ ≤ 2 * K * a ^ 4 + 51 * a ^ 2 := add_le_add hsq ht3
    _ ≤ (1 / 16 : ℝ) * ((1 / K : ℝ) * a) + (1 / 16 : ℝ) * ((1 / K : ℝ) * a) := add_le_add hc1 hc2
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by rw [ha]; ring

/-! ### `hfar` in base `b ≥ 3` -/

lemma four_mul_le_two_pow_N {b K : ℕ} (h : Hyp b K) :
    4 * K * (logP₀Nat K + m b K + 2 * J K + 13) ≤ 2 ^ Sched.N K := by
  have hK := h.hK
  have h1 := logP₀Nat_le hK
  have h2 := m_le h
  have h3 := J_le hK
  have hK2 : 2 ≤ K := by omega
  have hA : logP₀Nat K + m b K + 2 * J K + 13 ≤ K ^ (20 * K + 18) := by
    have a1 : m b K ≤ K ^ (20 * K + 17) := h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have a2 : 2 * J K ≤ K ^ (20 * K + 17) := by
      have : K ^ 4 ≤ K ^ (20 * K + 16) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 * K ^ (20 * K + 16) ≤ K ^ (20 * K + 17) := by
        calc 2 * K ^ (20 * K + 16) ≤ K * K ^ (20 * K + 16) := Nat.mul_le_mul_right _ (by omega)
          _ = K ^ (20 * K + 17) := by ring
      omega
    have a3 : 13 ≤ K ^ (20 * K + 17) := by
      calc 13 ≤ K := by omega
        _ ≤ K ^ (20 * K + 17) := Nat.le_self_pow (by omega) K
    have a4 : 4 * K ^ (20 * K + 17) ≤ K ^ (20 * K + 18) := by
      calc 4 * K ^ (20 * K + 17) ≤ K * K ^ (20 * K + 17) := Nat.mul_le_mul_right _ (by omega)
        _ = K ^ (20 * K + 18) := by ring
    omega
  have hB : 4 * K * K ^ (20 * K + 18) ≤ K ^ (20 * K + 20) := by
    calc 4 * K * K ^ (20 * K + 18) ≤ K * K * K ^ (20 * K + 18) := by gcongr; omega
      _ = K ^ (20 * K + 20) := by ring
  have hC : K ^ (20 * K + 20) ≤ 2 ^ (100 * K ^ 2) := by
    calc K ^ (20 * K + 20) ≤ 2 ^ (K * (20 * K + 20)) := pow_le_two_pow_mul _ _
      _ ≤ 2 ^ (100 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  unfold Sched.N
  calc 4 * K * (logP₀Nat K + m b K + 2 * J K + 13) ≤ 4 * K * K ^ (20 * K + 18) := by gcongr
    _ ≤ K ^ (20 * K + 20) := hB
    _ ≤ 2 ^ (100 * K ^ 2) := hC

lemma farBound_le_three {b : ℕ} (hb : 3 ≤ b) (J : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    farBound b J C ≤ farBound 3 J C := by
  unfold farBound
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : (1 : ℝ) / b ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2 : (0 : ℝ) ≤ 1 / b := by positivity
  have h3 : (2 : ℝ) ≤ b - 1 := by linarith
  have hJ : (0 : ℝ) ≤ C + 2 * J + 2 := by positivity
  calc (1 / (b : ℝ)) ^ J * ((C + 2 * J + 2) / (b - 1) + 2 / (b - 1) ^ 2)
      ≤ (1 / 3 : ℝ) ^ J * ((C + 2 * J + 2) / (b - 1) + 2 / (b - 1) ^ 2) := by
        gcongr
    _ ≤ (1 / 3 : ℝ) ^ J * ((C + 2 * J + 2) / (3 - 1) + 2 / (3 - 1) ^ 2) := by
        gcongr <;> norm_num

/-- **`hfar` in base `b ≥ 3`**, against `η = 2^{−k₄}`. -/
theorem hfar_holds {b K k₄ : ℕ} (hK4 : K = 4 * k₄) (h : Hyp b K) :
    (2 : ℝ) ^ K / Real.log 2 * farBound b (K + Sched.N K) (farC (gridOf K (Sched.N K) h.hK1) (X b K) (gridDm K (Sched.N K)))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hb := h.hb; have hK := h.hK
  have hfarC := farC_le h
  have hfar0 := farC_nonneg (gridOf K (Sched.N K) h.hK1) (X b K) (sample_nonempty h) (gridDm K (Sched.N K))
  set C := farC (gridOf K (Sched.N K) h.hK1) (X b K) (gridDm K (Sched.N K)) with hC
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by
    rw [ha]
    calc (1 / 2 : ℝ) ^ k₄ ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  -- reduce to `b = 3`
  have hfb := farBound_le_three hb (K + Sched.N K) hfar0
  -- the bracket at `b = 3` is at most `A/2`
  set A : ℕ := logP₀Nat K + m b K + 2 * J K + 13 with hA
  have hbr : (C + 2 * (K + Sched.N K : ℕ) + 2) / (3 - 1) + 2 / (3 - 1) ^ 2 ≤ (A : ℝ) / 2 := by
    have hJ : (J K : ℝ) = K + Sched.N K := by unfold J; push_cast; ring
    rw [hA]; push_cast; rw [hJ]
    linarith
  have hN := four_mul_le_two_pow_N h
  have hNr : (4 : ℝ) * K * A ≤ (2 : ℝ) ^ Sched.N K := by exact_mod_cast hN
  have h3N : (2 : ℝ) ^ Sched.N K ≤ (3 : ℝ) ^ Sched.N K := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hq : (1 / 3 : ℝ) ^ Sched.N K * (A : ℝ) ≤ 1 / (4 * K) := by
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h23 : (2 : ℝ) ^ K * (1 / 3 : ℝ) ^ K = (2 / 3 : ℝ) ^ K := by rw [← mul_pow]; norm_num
  have h23a := two_thirds_pow_le (k₄ := k₄) hK4
  have hA0 : (0 : ℝ) ≤ A := by positivity
  calc (2 : ℝ) ^ K / Real.log 2 * farBound b (K + Sched.N K) C
      ≤ (2 : ℝ) ^ K / Real.log 2 * farBound 3 (K + Sched.N K) C := by gcongr
    _ = (2 : ℝ) ^ K / Real.log 2 * ((1 / 3 : ℝ) ^ (K + Sched.N K)
          * ((C + 2 * (K + Sched.N K : ℕ) + 2) / (3 - 1) + 2 / (3 - 1) ^ 2)) := by
        unfold farBound; push_cast; ring_nf
    _ ≤ (2 : ℝ) ^ K / Real.log 2 * ((1 / 3 : ℝ) ^ (K + Sched.N K) * ((A : ℝ) / 2)) := by gcongr
    _ = (2 / 3 : ℝ) ^ K * ((1 / 3 : ℝ) ^ Sched.N K * A) / (2 * Real.log 2) := by
        rw [pow_add, ← h23]; field_simp
    _ ≤ a ^ 2 * (1 / (4 * K)) / (2 * (2 / 3)) := by
        gcongr
    _ = a * a * (3 / (16 * K)) := by field_simp; ring
    _ ≤ a * (1 / 2) * (3 / (16 * K)) := by gcongr
    _ ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * a) := by
        rw [show (1 / 8 : ℝ) * ((1 / K : ℝ) * a) = a * (1 / (8 * K)) by field_simp]
        have : (1 / 2 : ℝ) * (3 / (16 * K)) ≤ 1 / (8 * K) := by
          rw [show (1 / 2 : ℝ) * (3 / (16 * K)) = 3 / (32 * K) by field_simp; ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        nlinarith

/-! ### The witness -/

lemma R_le_Y (b K : ℕ) : R b K ≤ Y b K :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (m₁_le_m b K))

lemma Kbℓ_eq (b ℓ : ℕ) : Kbℓ b ℓ = 4 * k₄bℓ b ℓ := rfl

/-- **The schedule witness in base `b ≥ 3`** for every omitted cylinder of depth `ℓ ≥ 1`. -/
noncomputable def scheduleWitnessB (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) :
    ScheduleWitnessB b ℓ w :=
  let k₄ := k₄bℓ b ℓ
  let K := Kbℓ b ℓ
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp b K := hyp_Kbℓ hb hℓ
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  { G := gridOf K (Sched.N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    X := X b K
    hne := sample_nonempty h
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := Mbℓ b ℓ
    hM := hM_holds hb hℓ
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      intro g hglo hghi
      have hr : (gridOf K (Sched.N K) hK1).rDim = (K ^ 2) ^ K := rfl
      have hH : (gridOf K (Sched.N K) hK1).hDim = (K ^ 2 + 1) ^ K := rfl
      rw [hr] at hglo hghi
      rw [hr, hH]
      have hη : ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K := by
        rw [← pow_mul, hK4, mul_comm]
      exact gridB_bound (bb := b) (by omega) hℓ Kbℓ_ge (Mbℓ_lo hb hℓ) (Mbℓ_hi hb hℓ)
        (by positivity) hη le_rfl hglo hghi
    R := R b K
    hR := R_ge_two b K
    Y := Y b K
    hRY := R_le_Y b K
    D := Dj K k₄
    hN := hN_holds (by omega) hK4 hK100
    Mc := Mc b K
    hMc := Mc_pos (by omega) hK1
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    Mx := ((X b K + J K * gridDm K (Sched.N K) : ℕ) : ℝ)
    hMx1 := by
      have : 1 ≤ X b K := Nat.one_le_two_pow
      exact_mod_cast le_add_right this
    hMx := fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    Dm := gridDm K (Sched.N K)
    hDm := gridOf.d_le hK1
    δbig := 1 / 8
    δfar := 1 / 8
    hbig := hbig_holds hK4 h
    hfar := hfar_holds hK4 h
    hbudget := by
      have h := hbudget_holds hK4 h
      have hc : Fintype.card (gridOf K (Sched.N K) hK1).Idx = T K := gridOf.card_Idx hK1
      rw [← hc] at h
      exact h }

end SchedB

/-- **The base-`b` theorem: `∑_n ω(n)/bⁿ` is disjunctive in base `b` for every `b ≥ 3`.** -/
theorem isDisjunctive_base {b : ℕ} (hb : 3 ≤ b) : IsDisjunctive b (primeLambertAtBase b) := by
  refine isDisjunctive_of_witnessB b (by omega) fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · -- the empty word: the cylinder is `[0,1)`, which every orbit point hits
    exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico b (primeLambertAtBase b) 0)
  · exact ⟨SchedB.scheduleWitnessB b ℓ w hb hℓ⟩

/-- The base-four theorem as an instance of the general one. -/
theorem isDisjunctive_four' : IsDisjunctive 4 primeLambertFour :=
  isDisjunctive_base (by norm_num)

/-- **In the prime-sum form: `∑_{p prime} 1/(bᵖ − 1)` is disjunctive in base `b` for every
`b ≥ 3`** (`primeSumAtBase_eq_primeLambertAtBase`). -/
theorem isDisjunctive_primeSum {b : ℕ} (hb : 3 ≤ b) : IsDisjunctive b (primeSumAtBase b) := by
  rw [primeSumAtBase_eq_primeLambertAtBase (by omega)]
  exact isDisjunctive_base hb

/-- **Every finite base-`b` word occurs in the base-`b` expansion of `∑_n ω(n)/bⁿ`**, `b ≥ 3`. -/
theorem every_word_occurs_base {b : ℕ} (hb : 3 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    ∃ n, OccursAt b (primeLambertAtBase b) w n :=
  (isDisjunctive_iff_forall_occursAt b (by omega) _).1 (isDisjunctive_base hb) w hw

/-- **Root bases**: `∑_n ω(n)/(cᵏ)ⁿ` is disjunctive in base `c` whenever `c ≥ 2`, `k ≥ 1` and
`cᵏ ≥ 3` — e.g. `∑ ω(n)/8ⁿ` and `∑ ω(n)/16ⁿ` in base two, `∑ ω(n)/9ⁿ` in base three. -/
theorem isDisjunctive_root {c k : ℕ} (hc : 2 ≤ c) (hk : 1 ≤ k) (h3 : 3 ≤ c ^ k) :
    IsDisjunctive c (primeLambertAtBase (c ^ k)) :=
  (isDisjunctive_pow_iff c k hc hk _).2 (isDisjunctive_base h3)

end NormalNumbers.G4
