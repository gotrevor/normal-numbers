/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleGrid

/-!
# G4 §5: the explicit parameter schedule in `K`, and the size ladder

The schedule is chosen **`K` first, then everything else as an explicit function of `K`**
(and `X` last, hyper-exponentially large).  With `N = 100K²` the grid of `G4ScheduleGrid`
has `J = K + N`, `W = U + K + N + 2` (so `Q = W!`), `H = (K²+1)^K`, `T = H·N`, and the
progression modulus satisfies

  `log P₀ ≤ logP₀Nat K := (2H + T²)(3W² + J) + (2T+1)²`          (`log_gridP₀Bound_le`).

The remaining schedule scales are `m₁ = 100·8^K·K^{2K+1}` (the small-prime cutoff is
`R = 2^{2^{m₁}}`), `m₂ = 8K²`, `m = m₁ + m₂` (`Y = 2^{2^m}`, `X = Y^{100}`) and the moment
order `Mc = 3·10⁴·T·m₁`.

Everything is compared on the **ladder** `K^{cK+d}` (for `K ≥ 100`): `N ≤ K³`, `J ≤ K⁴`,
`B ≤ K⁷`, `U ≤ K^{7K+3}`, `W ≤ K^{7K+4}`, `H ≤ K^{3K}`, `T ≤ K^{3K+3}`,
`logP₀Nat ≤ K^{20K+17}`, `m₁ ≤ K^{3K+3}`, `m ≤ K^{3K+4}`, `Mc ≤ K^{6K+9}`, and
`K^e ≤ 2^{Ke}`.  These are the only size facts the four `X`-dependent witness inequalities
use.
-/

open Finset
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

/-- `N = 100K²`. -/
def N (K : ℕ) : ℕ := 100 * K ^ 2
/-- `J = K + N`. -/
def J (K : ℕ) : ℕ := K + N K
/-- `W = U + K + N + 2`, so `Q = W!`. -/
def W (K : ℕ) : ℕ := gridUmax K (N K) + K + N K + 2
/-- `H = (K²+1)^K`. -/
def H (K : ℕ) : ℕ := gridH K
/-- `T = H·N`. -/
def T (K : ℕ) : ℕ := gridT K (N K)
/-- The ℕ bound for `log P₀`. -/
def logP₀Nat (K : ℕ) : ℕ := (2 * H K + T K ^ 2) * (3 * W K ^ 2 + J K) + (2 * T K + 1) ^ 2
/-- `m₁ = 100·8^K·K^{2K+1}`: `log₂ log₂ R`. -/
def m₁ (K : ℕ) : ℕ := 100 * 8 ^ K * K ^ (2 * K + 1)
/-- `m₂ = 8K²`: `log₂(log Y / log R)`. -/
def m₂ (K : ℕ) : ℕ := 8 * K ^ 2
/-- `m = m₁ + m₂`: `log₂ log₂ Y`. -/
def m (K : ℕ) : ℕ := m₁ K + m₂ K
/-- The moment order `Mc = 3·10⁴·T·m₁`. -/
def Mc (K : ℕ) : ℕ := 30000 * T K * m₁ K

lemma N_pos {K : ℕ} (hK : 1 ≤ K) : 0 < N K := by unfold N; positivity

/-! ### The ladder -/

lemma pow_le_two_pow_mul (K e : ℕ) : K ^ e ≤ 2 ^ (K * e) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le e

lemma N_le {K : ℕ} (hK : 100 ≤ K) : N K ≤ K ^ 3 := by
  unfold N
  calc 100 * K ^ 2 ≤ K * K ^ 2 := Nat.mul_le_mul_right _ hK
    _ = K ^ 3 := by ring

lemma J_le {K : ℕ} (hK : 100 ≤ K) : J K ≤ K ^ 4 := by
  unfold J
  have h1 := N_le hK
  have h2 : K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have h3 : 2 * K ^ 3 ≤ K ^ 4 := by
    calc 2 * K ^ 3 ≤ K * K ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 4 := by ring
  omega

lemma gridB_le {K : ℕ} (hK : 100 ≤ K) : gridB K (N K) ≤ K ^ 7 := by
  unfold gridB
  have h1 : K + N K ≤ K ^ 4 := J_le hK
  have h2 : K ^ 2 * (K + N K) ≤ K ^ 2 * K ^ 4 := Nat.mul_le_mul_left _ h1
  have h3 : K ^ 2 * K ^ 4 + 1 ≤ K ^ 7 := by
    have : 1 ≤ K ^ 6 := Nat.one_le_pow _ _ (by omega)
    calc K ^ 2 * K ^ 4 + 1 = K ^ 6 + 1 := by ring
      _ ≤ K ^ 6 + K ^ 6 := by omega
      _ = 2 * K ^ 6 := by ring
      _ ≤ K * K ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 7 := by ring
  omega

lemma gridSum_le (K B : ℕ) (hB : 1 ≤ B) : gridSum K B ≤ K * B ^ K := by
  unfold gridSum
  calc ∑ i : Fin K, B ^ ((i : ℕ) + 1) ≤ ∑ _i : Fin K, B ^ K :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_right hB (by omega)
    _ = K * B ^ K := by simp

lemma gridUmax_le {K : ℕ} (hK : 100 ≤ K) : gridUmax K (N K) ≤ K ^ (7 * K + 3) := by
  unfold gridUmax
  have hB1 : 1 ≤ gridB K (N K) := by unfold gridB; omega
  calc K ^ 2 * gridSum K (gridB K (N K)) ≤ K ^ 2 * (K * gridB K (N K) ^ K) :=
        Nat.mul_le_mul_left _ (gridSum_le _ _ hB1)
    _ ≤ K ^ 2 * (K * (K ^ 7) ^ K) := by gcongr; exact gridB_le hK
    _ = K ^ (7 * K + 3) := by rw [← pow_mul]; ring

lemma W_le {K : ℕ} (hK : 100 ≤ K) : W K ≤ K ^ (7 * K + 4) := by
  unfold W
  have h1 := gridUmax_le hK
  have h2 := N_le hK
  have h3 : K ^ 3 ≤ K ^ (7 * K + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have h5 : 2 ≤ K ^ 3 := by have : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega); nlinarith
  have h6 : 4 * K ^ (7 * K + 3) ≤ K ^ (7 * K + 4) := by
    calc 4 * K ^ (7 * K + 3) ≤ K * K ^ (7 * K + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ (7 * K + 4) := by ring
  omega

lemma H_le {K : ℕ} (hK : 100 ≤ K) : H K ≤ K ^ (3 * K) := by
  unfold H gridH
  have : K ^ 2 + 1 ≤ K ^ 3 := by
    have : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc K ^ 2 + 1 ≤ K ^ 2 + K ^ 2 := by omega
      _ = 2 * K ^ 2 := by ring
      _ ≤ K * K ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 3 := by ring
  calc (K ^ 2 + 1) ^ K ≤ (K ^ 3) ^ K := Nat.pow_le_pow_left this K
    _ = K ^ (3 * K) := by rw [← pow_mul]

lemma T_eq (K : ℕ) : T K = H K * N K := rfl

lemma T_le {K : ℕ} (hK : 100 ≤ K) : T K ≤ K ^ (3 * K + 3) := by
  rw [T_eq]
  calc H K * N K ≤ K ^ (3 * K) * K ^ 3 := Nat.mul_le_mul (H_le hK) (N_le hK)
    _ = K ^ (3 * K + 3) := by rw [← pow_add]

lemma H_pos (K : ℕ) : 0 < H K := by unfold H gridH; positivity

lemma T_pos {K : ℕ} (hK : 1 ≤ K) : 0 < T K := Nat.mul_pos (H_pos K) (N_pos hK)

lemma H_le_T {K : ℕ} (hK : 1 ≤ K) : H K ≤ T K :=
  Nat.le_mul_of_pos_right _ (N_pos hK)

/-- `r = (K²)^K ≤ H`. -/
lemma r_le_H (K : ℕ) : (K ^ 2) ^ K ≤ H K := by
  unfold H gridH
  exact Nat.pow_le_pow_left (by omega) K

lemma logP₀Nat_le {K : ℕ} (hK : 100 ≤ K) : logP₀Nat K ≤ K ^ (20 * K + 17) := by
  unfold logP₀Nat
  have hH := H_le hK
  have hT := T_le hK
  have hW := W_le hK
  have hJ := J_le hK
  have hK2 : 2 ≤ K := by omega
  -- `2H + T² ≤ K^{6K+7}`
  have h1 : 2 * H K + T K ^ 2 ≤ K ^ (6 * K + 7) := by
    have a1 : H K ≤ K ^ (6 * K + 6) := hH.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have a2 : T K ^ 2 ≤ K ^ (6 * K + 6) := by
      calc T K ^ 2 ≤ (K ^ (3 * K + 3)) ^ 2 := Nat.pow_le_pow_left hT 2
        _ = K ^ (6 * K + 6) := by rw [← pow_mul]; ring_nf
    have a3 : 3 * K ^ (6 * K + 6) ≤ K ^ (6 * K + 7) := by
      calc 3 * K ^ (6 * K + 6) ≤ K * K ^ (6 * K + 6) := Nat.mul_le_mul_right _ (by omega)
        _ = K ^ (6 * K + 7) := by ring
    omega
  -- `3W² + J ≤ K^{14K+9}`
  have h2 : 3 * W K ^ 2 + J K ≤ K ^ (14 * K + 9) := by
    have a1 : W K ^ 2 ≤ K ^ (14 * K + 8) := by
      calc W K ^ 2 ≤ (K ^ (7 * K + 4)) ^ 2 := Nat.pow_le_pow_left hW 2
        _ = K ^ (14 * K + 8) := by rw [← pow_mul]; ring_nf
    have a2 : J K ≤ K ^ (14 * K + 8) := hJ.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have a3 : 4 * K ^ (14 * K + 8) ≤ K ^ (14 * K + 9) := by
      calc 4 * K ^ (14 * K + 8) ≤ K * K ^ (14 * K + 8) := Nat.mul_le_mul_right _ (by omega)
        _ = K ^ (14 * K + 9) := by ring
    omega
  -- `(2T+1)² ≤ K^{6K+8}`
  have h3 : (2 * T K + 1) ^ 2 ≤ K ^ (6 * K + 8) := by
    have a1 : 2 * T K + 1 ≤ 3 * K ^ (3 * K + 3) := by
      have : 1 ≤ K ^ (3 * K + 3) := Nat.one_le_pow _ _ (by omega)
      omega
    calc (2 * T K + 1) ^ 2 ≤ (3 * K ^ (3 * K + 3)) ^ 2 := Nat.pow_le_pow_left a1 2
      _ = 9 * K ^ (6 * K + 6) := by rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ K ^ 2 * K ^ (6 * K + 6) := Nat.mul_le_mul_right _ (by nlinarith)
      _ = K ^ (6 * K + 8) := by rw [← pow_add]; ring_nf
  have h4 : K ^ (6 * K + 7) * K ^ (14 * K + 9) = K ^ (20 * K + 16) := by
    rw [← pow_add]; ring_nf
  have h5 : K ^ (6 * K + 8) ≤ K ^ (20 * K + 16) := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : 2 * K ^ (20 * K + 16) ≤ K ^ (20 * K + 17) := by
    calc 2 * K ^ (20 * K + 16) ≤ K * K ^ (20 * K + 16) := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ (20 * K + 17) := by ring
  calc (2 * H K + T K ^ 2) * (3 * W K ^ 2 + J K) + (2 * T K + 1) ^ 2
      ≤ K ^ (6 * K + 7) * K ^ (14 * K + 9) + K ^ (6 * K + 8) := by
        gcongr
    _ = K ^ (20 * K + 16) + K ^ (6 * K + 8) := by rw [h4]
    _ ≤ K ^ (20 * K + 17) := by omega

lemma m₁_le {K : ℕ} (hK : 100 ≤ K) : m₁ K ≤ K ^ (3 * K + 3) := by
  unfold m₁
  have h1 : 100 ≤ K ^ 2 := by nlinarith
  have h2 : 8 ^ K ≤ K ^ K := Nat.pow_le_pow_left (by omega) K
  calc 100 * 8 ^ K * K ^ (2 * K + 1) ≤ K ^ 2 * K ^ K * K ^ (2 * K + 1) := by gcongr
    _ = K ^ (3 * K + 3) := by rw [← pow_add, ← pow_add]; ring_nf

lemma m₁_ge (K : ℕ) : 8 ^ K * K ^ (2 * K + 1) ≤ m₁ K := by
  unfold m₁
  have : 8 ^ K * K ^ (2 * K + 1) ≤ 100 * (8 ^ K * K ^ (2 * K + 1)) :=
    Nat.le_mul_of_pos_left _ (by norm_num)
  linarith [this]

lemma m_le {K : ℕ} (hK : 100 ≤ K) : m K ≤ K ^ (3 * K + 4) := by
  unfold m m₂
  have h1 := m₁_le hK
  have h2 : 8 * K ^ 2 ≤ K ^ (3 * K + 3) := by
    calc 8 * K ^ 2 ≤ K * K ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ 3 := by ring
      _ ≤ K ^ (3 * K + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * K ^ (3 * K + 3) ≤ K ^ (3 * K + 4) := by
    calc 2 * K ^ (3 * K + 3) ≤ K * K ^ (3 * K + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = K ^ (3 * K + 4) := by ring
  omega

lemma Mc_le {K : ℕ} (hK : 100 ≤ K) : Mc K ≤ K ^ (6 * K + 9) := by
  unfold Mc
  have h1 : 30000 ≤ K ^ 3 := by
    calc 30000 ≤ 100 ^ 3 := by norm_num
      _ ≤ K ^ 3 := Nat.pow_le_pow_left hK 3
  calc 30000 * T K * m₁ K ≤ K ^ 3 * K ^ (3 * K + 3) * K ^ (3 * K + 3) := by
        gcongr
        · exact T_le hK
        · exact m₁_le hK
    _ = K ^ (6 * K + 9) := by rw [← pow_add, ← pow_add]; ring_nf

lemma Mc_pos {K : ℕ} (hK : 1 ≤ K) : 0 < Mc K := by
  unfold Mc m₁
  have := T_pos hK
  positivity

/-! ### The real-log bound on `P₀` -/

lemma log_nat_le (n : ℕ) : Real.log n ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := Real.log_le_sub_one_of_pos (by exact_mod_cast h : (0 : ℝ) < n)
    linarith

lemma gridDm_le_mul (K : ℕ) : gridDm K (N K) ≤ gridQ K (N K) * ((K + 1) * W K) := by
  unfold gridDm gridD₀ W
  have hQ : 1 ≤ gridQ K (N K) := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  set Q := gridQ K (N K)
  set U := gridUmax K (N K)
  have : K * U + U + 1 ≤ (K + 1) * (U + K + N K + 2) := by nlinarith
  calc 1 + Q * (K * U + U) ≤ Q * (K * U + U + 1) := by nlinarith
    _ ≤ Q * ((K + 1) * (U + K + N K + 2)) := Nat.mul_le_mul_left _ this

lemma log_gridDm_le (K : ℕ) : Real.log (gridDm K (N K)) ≤ 3 * (W K : ℝ) ^ 2 := by
  have hW1 : 1 ≤ W K := by unfold W; omega
  have hWr : (1 : ℝ) ≤ W K := by exact_mod_cast hW1
  have hKW : (K : ℝ) ≤ W K := by unfold W; exact_mod_cast (by omega : K ≤ _)
  have hDm : (0 : ℝ) < gridDm K (N K) := by exact_mod_cast gridDm_pos K (N K)
  have hQ : (0 : ℝ) < gridQ K (N K) := by exact_mod_cast Nat.factorial_pos _
  have h1 : (gridDm K (N K) : ℝ) ≤ gridQ K (N K) * ((K + 1) * W K) := by
    exact_mod_cast gridDm_le_mul K
  -- `log Q ≤ W log W ≤ W²`
  have hlogQ : Real.log (gridQ K (N K)) ≤ (W K : ℝ) ^ 2 := by
    have hfac : (gridQ K (N K) : ℝ) ≤ (W K : ℝ) ^ W K := by
      have : gridQ K (N K) ≤ W K ^ W K := Nat.factorial_le_pow _
      exact_mod_cast this
    calc Real.log (gridQ K (N K)) ≤ Real.log ((W K : ℝ) ^ W K) :=
          Real.log_le_log hQ hfac
      _ = W K * Real.log (W K) := by rw [Real.log_pow]
      _ ≤ W K * W K := by gcongr; exact log_nat_le _
      _ = (W K : ℝ) ^ 2 := by ring
  have hlogK : Real.log ((K : ℝ) + 1) ≤ W K := by
    have := log_nat_le (K + 1)
    push_cast at this
    have : (K : ℝ) + 1 ≤ W K + 1 := by linarith
    calc Real.log ((K : ℝ) + 1) ≤ (K : ℝ) + 1 - 1 := by
          have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < K + 1); linarith
      _ ≤ W K := by linarith [hKW]
  have hlogW : Real.log (W K) ≤ W K := log_nat_le _
  calc Real.log (gridDm K (N K)) ≤ Real.log (gridQ K (N K) * ((K + 1) * W K)) :=
        Real.log_le_log hDm h1
    _ = Real.log (gridQ K (N K)) + (Real.log ((K : ℝ) + 1) + Real.log (W K)) := by
        rw [Real.log_mul hQ.ne' (by positivity), Real.log_mul (by positivity) (by positivity)]
    _ ≤ (W K : ℝ) ^ 2 + (W K + W K) := by linarith
    _ ≤ 3 * (W K : ℝ) ^ 2 := by nlinarith

/-- **`log P₀ ≤ logP₀Nat K`** for the explicit grid. -/
theorem log_gridP₀Bound_le {K : ℕ} (hK : 1 ≤ K) :
    Real.log (gridP₀Bound K (N K)) ≤ logP₀Nat K := by
  unfold gridP₀Bound logP₀Nat
  have hDm : (0 : ℝ) < gridDm K (N K) := by exact_mod_cast gridDm_pos K (N K)
  have hT : (0 : ℝ) < 2 * gridT K (N K) + 1 := by positivity
  have hJ : (0 : ℝ) < K + N K := by
    have : (0 : ℝ) ≤ N K := by positivity
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hJDm : (0 : ℝ) < (K + N K) * gridDm K (N K) := by positivity
  have e1 : ((gridDm K (N K) ^ (2 * gridH K) * (2 * gridT K (N K) + 1) ^ (2 * gridT K (N K) + 1)
      * ((K + N K) * gridDm K (N K)) ^ (gridT K (N K) ^ 2) : ℕ) : ℝ)
      = (gridDm K (N K) : ℝ) ^ (2 * gridH K) * ((2 * gridT K (N K) + 1 : ℝ)) ^ (2 * gridT K (N K) + 1)
      * (((K : ℝ) + N K) * gridDm K (N K)) ^ (gridT K (N K) ^ 2) := by push_cast; ring
  rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul hJ.ne' hDm.ne']
  have hlDm := log_gridDm_le K
  have hlT : Real.log (2 * (gridT K (N K) : ℝ) + 1) ≤ 2 * gridT K (N K) + 1 := by
    have := log_nat_le (2 * gridT K (N K) + 1); push_cast at this; exact this
  have hlJ : Real.log ((K : ℝ) + N K) ≤ K + N K := by
    have := log_nat_le (K + N K); push_cast at this; exact this
  have hH : (H K : ℝ) = gridH K := rfl
  have hTT : (T K : ℝ) = gridT K (N K) := rfl
  have hJJ : (J K : ℝ) = K + N K := by unfold J; push_cast; ring
  push_cast
  rw [hH, hTT, hJJ] at *
  have hH0 : (0 : ℝ) ≤ gridH K := by positivity
  have hT0 : (0 : ℝ) ≤ gridT K (N K) := by positivity
  have hJ0 : (0 : ℝ) ≤ K + N K := hJ.le
  nlinarith [mul_le_mul_of_nonneg_left hlDm hH0, mul_le_mul_of_nonneg_left hlT hT.le,
    mul_le_mul_of_nonneg_left hlDm (sq_nonneg (gridT K (N K) : ℝ)),
    mul_le_mul_of_nonneg_left hlJ (sq_nonneg (gridT K (N K) : ℝ)),
    mul_nonneg hH0 hJ0]

/-- `P₀ ≤ exp(logP₀Nat K)`. -/
theorem P₀_le_exp {K : ℕ} (hK : 1 ≤ K) :
    ((gridOf K (N K) hK).P₀ : ℝ) ≤ Real.exp (logP₀Nat K) := by
  have h1 : ((gridOf K (N K) hK).P₀ : ℝ) ≤ gridP₀Bound K (N K) := by
    exact_mod_cast gridOf.P₀_le hK
  have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
    have := (gridOf K (N K) hK).P₀_pos
    have := gridOf.P₀_le (N := N K) hK
    exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
  calc ((gridOf K (N K) hK).P₀ : ℝ) ≤ gridP₀Bound K (N K) := h1
    _ = Real.exp (Real.log (gridP₀Bound K (N K))) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (logP₀Nat K) := Real.exp_le_exp.2 (log_gridP₀Bound_le hK)

end Sched

end NormalNumbers.G4
