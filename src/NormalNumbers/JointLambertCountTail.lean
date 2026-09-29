/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertGcdAverage

/-!
# The near and middle tail ranges

§4 of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` splits the discrepancy tail
`∑_{m<M} ∑_{j≥k} τ(n_m + j) 2^{-j}` into three ranges.  This module proves the first two,
which are the ones carrying the *new* mathematics:

* **near** `k ≤ j < L`: the CRT still forces `gcd(R+j, A) = 1` (every allocation prime
  exceeds `L`), so the frozen coprime average `sum_tau_progression_le` applies;
* **middle** `L ≤ j < J`: coprimality may fail, and the price is exactly one factor `τ(A)`,
  via `sum_tau_progression_le_noncoprime`.

`near_middle_tail_le` is the combined bound

    ∑_{m<M} ∑_{j ∈ [k, J)} τ(R + j + mA) (1/2)^j ≤ W · (2 (1/2)^k + τ(A) · 2 (1/2)^L),

with `W = 2M(1 + log H) + 2H` the one divisor-average bracket.  The *structural* point of
the small-pool route is visible in this single inequality: the middle range pays `τ(A)` but
is discounted by `(1/2)^L = 2^{-k³}`, while `jointA_tau_le` bounds `τ(A)` by
`(a+1)(c+1)^{k²}`.  The cube beats the square, which is why the pool may be polynomial in
`k` rather than in `log X`.

The far range `j ≥ J` uses a different estimate (`τ(n) ≤ 2√n`) and is not in this file.
-/

namespace NormalNumbers.JointLambert

open Finset NormalNumbers.SwingC2

/-- `∑_{j ∈ [k, J)} (1/2)^j ≤ 2 (1/2)^k`. -/
theorem sum_half_Ico_le (k J : ℕ) :
    (∑ j ∈ Ico k J, (1 / 2 : ℝ) ^ j) ≤ 2 * (1 / 2 : ℝ) ^ k := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hrw : ∀ i ∈ range (J - k), (1 / 2 : ℝ) ^ (k + i) = (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ i := by
    intro i _; rw [pow_add]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have := sum_geometric_two_le (J - k)
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  calc (1 / 2 : ℝ) ^ k * ∑ i ∈ range (J - k), (1 / 2 : ℝ) ^ i
      ≤ (1 / 2 : ℝ) ^ k * 2 := mul_le_mul_of_nonneg_left this hpos.le
    _ = 2 * (1 / 2 : ℝ) ^ k := by ring

/-- **Near + middle tail** (note §4).  `W = 2M(1 + log H) + 2H` is the divisor-average
bracket; the near range costs `2 (1/2)^k` copies of it and the middle range costs
`τ(A) · 2 (1/2)^L`. -/
theorem near_middle_tail_le {R A M H k L J : ℕ} (hA : 0 < A) (hR : 0 < R) (hH : 1 ≤ H)
    (hkL : k ≤ L) (hLJ : L ≤ J)
    (hbd : ∀ j, j < J → ∀ m, m < M → (R + j) + m * A ≤ H ^ 2)
    (hcop : ∀ j, k ≤ j → j < L → Nat.Coprime (R + j) A) :
    (∑ m ∈ range M, ∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j)
      ≤ (2 * M * (1 + Real.log H) + 2 * H)
          * (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ L)) := by
  classical
  set W : ℝ := 2 * M * (1 + Real.log H) + 2 * H with hW
  have hlogH : (0 : ℝ) ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hWpos : (0 : ℝ) ≤ W := by rw [hW]; positivity
  -- swap the two sums
  have hswap : (∑ m ∈ range M, ∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j)
      = ∑ j ∈ Ico k J, (1 / 2 : ℝ) ^ j * ∑ m ∈ range M, (tau (R + j + m * A) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hswap]
  -- the per-`j` divisor average, with the `τ(A)` factor only in the middle range
  have hrow : ∀ j ∈ Ico k J,
      (1 / 2 : ℝ) ^ j * ∑ m ∈ range M, (tau (R + j + m * A) : ℝ)
        ≤ (1 / 2 : ℝ) ^ j * (if j < L then W else (tau A : ℝ) * W) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hRj : 0 < R + j := by omega
    have hbdj : ∀ m, m < M → (R + j) + m * A ≤ H ^ 2 := hbd j hj.2
    have hinner : (∑ m ∈ range M, (tau (R + j + m * A) : ℝ))
        ≤ (if j < L then W else (tau A : ℝ) * W) := by
      have hidx : ∀ m : ℕ, R + j + m * A = (R + j) + m * A := fun m => by ring
      by_cases hjL : j < L
      · simp only [hjL, if_true]
        have := sum_tau_progression_le (u := R + j) (A := A) (H := H) (M := M)
          hRj (hcop j hj.1 hjL) hH hbdj
        simpa [hidx, hW] using this
      · simp only [hjL, if_false]
        have := sum_tau_progression_le_noncoprime (u := R + j) (A := A) (H := H) (M := M)
          hRj hA hH hbdj
        simpa [hidx, hW] using this
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  refine le_trans (Finset.sum_le_sum hrow) ?_
  -- split the range at `L`
  have hsplit : (∑ j ∈ Ico k J, (1 / 2 : ℝ) ^ j * (if j < L then W else (tau A : ℝ) * W))
      = (∑ j ∈ Ico k L, (1 / 2 : ℝ) ^ j * W)
        + ∑ j ∈ Ico L J, (1 / 2 : ℝ) ^ j * ((tau A : ℝ) * W) := by
    rw [← Finset.sum_Ico_consecutive _ hkL hLJ]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      simp [hj.2]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      simp [Nat.not_lt.mpr hj.1]
  rw [hsplit, ← Finset.sum_mul, ← Finset.sum_mul]
  have hτ : (0 : ℝ) ≤ (tau A : ℝ) := by positivity
  have h1 : (∑ j ∈ Ico k L, (1 / 2 : ℝ) ^ j) * W ≤ (2 * (1 / 2 : ℝ) ^ k) * W :=
    mul_le_mul_of_nonneg_right (sum_half_Ico_le k L) hWpos
  have h2 : (∑ j ∈ Ico L J, (1 / 2 : ℝ) ^ j) * ((tau A : ℝ) * W)
      ≤ (2 * (1 / 2 : ℝ) ^ L) * ((tau A : ℝ) * W) :=
    mul_le_mul_of_nonneg_right (sum_half_Ico_le L J) (by positivity)
  nlinarith [h1, h2]

/-! ### Window arithmetic for the three-range bound

`three_range_tail_le` needs two size facts about the progression: every start `n_m = R + mA`
is at most `Y`, and every value `n_m + j` in the tail window is at most `H²`.  Both are pure
arithmetic in the CRT data, and both are proved here once so the assembly never re-derives
them.  `Y = 2QX` is the note's choice, and it is exactly what `A = QB`, `R < A` and
`m < ⌊X/B⌋ + 1` give. -/

/-- **Every progression start is at most `2QX`.**  `m A = Q(mB) ≤ QX` and `R < A = QB ≤ QX`. -/
theorem progression_le_window {R A B Q X m : ℕ} (hAQB : A = Q * B) (hRA : R < A)
    (hB : 1 ≤ B) (hBX : B ≤ X) (hm : m < X / B + 1) :
    R + m * A ≤ 2 * Q * X := by
  have hmle : m ≤ X / B := by omega
  have hmA : m * A ≤ Q * X := by
    calc m * A = Q * (m * B) := by rw [hAQB]; ring
      _ ≤ Q * (X / B * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmle)
      _ ≤ Q * X := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  have hR : R ≤ Q * X := by
    calc R ≤ A := hRA.le
      _ = Q * B := hAQB
      _ ≤ Q * X := Nat.mul_le_mul_left _ hBX
  calc R + m * A ≤ Q * X + Q * X := Nat.add_le_add hR hmA
    _ = 2 * Q * X := by ring

/-- **The square window.**  With `H = ⌊√Z⌋ + 1` one has `1 ≤ H` and `Z ≤ H²`, so `H` is a
legitimate divisor-average parameter for every value below `Z`. -/
theorem le_sqrt_succ_sq (Z : ℕ) : 1 ≤ Nat.sqrt Z + 1 ∧ Z ≤ (Nat.sqrt Z + 1) ^ 2 := by
  refine ⟨by omega, ?_⟩
  have h := Nat.lt_succ_sqrt' Z
  exact h.le

/-- The window bound in the shape `three_range_tail_le` consumes: with `H = ⌊√(Y+J)⌋ + 1`,
every tail value `(R + j) + mA` with `j < J` and `m < M` is at most `H²`. -/
theorem progression_window_le_sq {R A B Q X J M Y : ℕ} (hAQB : A = Q * B) (hRA : R < A)
    (hB : 1 ≤ B) (hBX : B ≤ X) (hM : M ≤ X / B + 1) (hY : 2 * Q * X + J ≤ Y) :
    ∀ j, j < J → ∀ m, m < M → (R + j) + m * A ≤ (Nat.sqrt Y + 1) ^ 2 := by
  intro j hj m hm
  have hstart : R + m * A ≤ 2 * Q * X :=
    progression_le_window hAQB hRA hB hBX (by omega)
  have hZ := (le_sqrt_succ_sq Y).2
  omega

/-! ### The far range, and the full three-range bound -/

/-- **Far range** (note §4, simplified).  Beyond `J` the crude `τ(n) ≤ n` bound already
suffices: `∑_{j≥J} τ(n_m+j)2^{-j} ≤ (2(Y+J)+2) 2^{-J}` when `n_m ≤ Y`.

The note reaches for `τ(n) ≤ 2√n` here, to get `(√Y + √J)2^{-J}`.  That refinement is
unnecessary: at the schedule `J = ⌊(log₂ X)²⌋` one has `2^J = X^{log₂ X}`, which dwarfs
`Y = 2QX` with room to spare, so the linear bound is already negligible.  Avoiding the
square root removes an entire estimate from the dependency chain. -/
theorem far_tail_le {M Y J : ℕ} (n : ℕ → ℕ) (hY : ∀ m, m < M → n m ≤ Y) :
    (∑ m ∈ range M, (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau (n m + J + t) : ℝ) / 2 ^ t)
      ≤ (M : ℝ) * ((2 * (Y : ℝ) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J) := by
  have hterm : ∀ m ∈ range M,
      (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau (n m + J + t) : ℝ) / 2 ^ t
        ≤ (2 * (Y : ℝ) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J := by
    intro m hm
    have hmM : m < M := Finset.mem_range.mp hm
    have h1 := tsum_tau_div_le (n m + J)
    have h2 : (2 : ℝ) * ((n m + J : ℕ) : ℝ) + 2 ≤ 2 * (Y : ℝ) + 2 * (J : ℝ) + 2 := by
      have : ((n m : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY m hmM
      push_cast
      linarith
    have hchain : (∑' t : ℕ, (tau (n m + J + t) : ℝ) / 2 ^ t)
        ≤ 2 * (Y : ℝ) + 2 * (J : ℝ) + 2 := by
      refine le_trans h1 ?_
      push_cast at h2 ⊢
      linarith
    calc (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau (n m + J + t) : ℝ) / 2 ^ t
        ≤ (1 / 2 : ℝ) ^ J * (2 * (Y : ℝ) + 2 * (J : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = (2 * (Y : ℝ) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The full three-range tail bound** (note §4).  The tail of each candidate index is
split as `[k, J)` plus `[J, ∞)`; the first part is `near_middle_tail_le`, the second
`far_tail_le`. -/
theorem three_range_tail_le {R A M H k L J Y : ℕ} (hA : 0 < A) (hR : 0 < R) (hH : 1 ≤ H)
    (hkL : k ≤ L) (hLJ : L ≤ J)
    (hbd : ∀ j, j < J → ∀ m, m < M → (R + j) + m * A ≤ H ^ 2)
    (hcop : ∀ j, k ≤ j → j < L → Nat.Coprime (R + j) A)
    (hY : ∀ m, m < M → R + m * A ≤ Y) :
    (∑ m ∈ range M, ((∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j)
        + (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau ((R + m * A) + J + t) : ℝ) / 2 ^ t))
      ≤ (2 * M * (1 + Real.log H) + 2 * H)
          * (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ L))
        + (M : ℝ) * ((2 * (Y : ℝ) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J) := by
  rw [Finset.sum_add_distrib]
  exact add_le_add (near_middle_tail_le hA hR hH hkL hLJ hbd hcop)
    (far_tail_le (M := M) (Y := Y) (J := J) (fun m => R + m * A) hY)

/-! ### The adaptive far-range split point

The note fixes `J = ⌊(log₂ X)²⌋` and reaches for `τ(n) ≤ 2√n`.  Neither is needed: `J` may
be chosen *adaptively* at each height from the window bound `Y₀ = 2QX`, large enough that
`2^J ≥ (Y₀+1)²(X+1)²2^{k³}`, and then the far cost is `O(X^{-2})` with the crude
`τ(n) ≤ n` already frozen in `tsum_tau_div_le`. -/


/-- The far-range split point, chosen adaptively at each height from the window bound
`Y₀ = 2QX` and the height `X`: `J = k³ + 2S` with `2^S > (Y₀+1)(X+1)`. -/
def countJ (k Y0 X : ℕ) : ℕ :=
  k ^ 3 + 2 * (Nat.log 2 (Y0 + 1) + 1 + (Nat.log 2 (X + 1) + 1))

theorem le_countJ (k Y0 X : ℕ) : k ^ 3 ≤ countJ k Y0 X := Nat.le_add_right _ _

theorem two_pow_countJ_ge (k Y0 X : ℕ) :
    ((Y0 : ℝ) + 1) ^ 2 * ((X : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (k ^ 3)
      ≤ (2 : ℝ) ^ (countJ k Y0 X) := by
  have hY : (Y0 : ℝ) + 1 < 2 ^ (Nat.log 2 (Y0 + 1) + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Y0 + 1)
    have h : ((Y0 + 1 : ℕ) : ℝ) < ((2 ^ (Nat.log 2 (Y0 + 1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h
    linarith
  have hX : (X : ℝ) + 1 < 2 ^ (Nat.log 2 (X + 1) + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (X + 1)
    have h : ((X + 1 : ℕ) : ℝ) < ((2 ^ (Nat.log 2 (X + 1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h
    linarith
  set S : ℕ := Nat.log 2 (Y0 + 1) + 1 + (Nat.log 2 (X + 1) + 1) with hS
  have hprod : ((Y0 : ℝ) + 1) * ((X : ℝ) + 1) ≤ (2 : ℝ) ^ S := by
    rw [hS, pow_add]
    nlinarith [hY, hX, pow_pos (by norm_num : (0:ℝ) < 2) (Nat.log 2 (Y0 + 1) + 1),
      pow_pos (by norm_num : (0:ℝ) < 2) (Nat.log 2 (X + 1) + 1)]
  have hsq : (((Y0 : ℝ) + 1) * ((X : ℝ) + 1)) ^ 2 ≤ ((2 : ℝ) ^ S) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hprod
  have hexp : ((2 : ℝ) ^ S) ^ 2 * (2 : ℝ) ^ (k ^ 3) = (2 : ℝ) ^ (countJ k Y0 X) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    simp only [countJ, ← hS]
    omega
  calc ((Y0 : ℝ) + 1) ^ 2 * ((X : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (k ^ 3)
      = (((Y0 : ℝ) + 1) * ((X : ℝ) + 1)) ^ 2 * (2 : ℝ) ^ (k ^ 3) := by ring
    _ ≤ ((2 : ℝ) ^ S) ^ 2 * (2 : ℝ) ^ (k ^ 3) := by
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := hexp

/-- **The far-range cost at the adaptive split point** is `O(X^{-2})`, uniformly in `k`
and in the window bound `Y₀`.  This is the estimate that replaces the note's
`τ(n) ≤ 2√n`: at `J = countJ`, `2^J` dwarfs the window, and no divisor bound is needed. -/
theorem far_cost_le {k Y0 X : ℕ} (hX : 1 ≤ X) (hXY : X ≤ Y0) :
    (2 * ((Y0 : ℝ) + (countJ k Y0 X : ℕ)) + 2 * ((countJ k Y0 X : ℕ) : ℝ) + 2)
        * (1 / 2 : ℝ) ^ (countJ k Y0 X)
      ≤ 24 / ((X : ℝ) + 1) ^ 2 := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXYR : (X : ℝ) ≤ (Y0 : ℝ) := by exact_mod_cast hXY
  set J : ℕ := countJ k Y0 X with hJ
  set T : ℝ := (2 : ℝ) ^ (k ^ 3) with hT
  set u : ℝ := (Y0 : ℝ) + 1 with hu
  set v : ℝ := (X : ℝ) + 1 with hv
  have hT1 : (1 : ℝ) ≤ T := one_le_pow₀ (by norm_num)
  have hv2 : (2 : ℝ) ≤ v := by simp only [hv]; linarith
  have hvu : v ≤ u := by simp only [hu, hv]; linarith
  have hden : u ^ 2 * v ^ 2 * T ≤ (2 : ℝ) ^ J := two_pow_countJ_ge k Y0 X
  have hden0 : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  have hlogY : (Nat.log 2 (Y0 + 1) : ℝ) ≤ u := by
    have h : ((Nat.log 2 (Y0 + 1) : ℕ) : ℝ) ≤ ((Y0 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.log_le_self 2 (Y0 + 1)
    push_cast at h; simp only [hu]; linarith
  have hlogX : (Nat.log 2 (X + 1) : ℝ) ≤ v := by
    have h : ((Nat.log 2 (X + 1) : ℕ) : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.log_le_self 2 (X + 1)
    push_cast at h; simp only [hv]; linarith
  have hk3 : ((k ^ 3 : ℕ) : ℝ) ≤ T := by
    have h : ((k ^ 3 : ℕ) : ℝ) ≤ ((2 ^ (k ^ 3) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k ^ 3)).le
    simp only [hT]; exact_mod_cast h
  have hJR : (J : ℝ) ≤ T + 2 * (u + v + 2) := by
    have hJn : (J : ℝ) = ((k ^ 3 : ℕ) : ℝ)
        + 2 * ((Nat.log 2 (Y0 + 1) : ℝ) + 1 + ((Nat.log 2 (X + 1) : ℝ) + 1)) := by
      simp only [hJ, countJ]; push_cast; ring
    rw [hJn]
    linarith [hlogY, hlogX, hk3]
  have huv : u + v + 2 ≤ 2 * (u * v) := by nlinarith
  have hnum : 2 * ((Y0 : ℝ) + (J : ℝ)) + 2 * (J : ℝ) + 2 ≤ 2 * u + 4 * T + 16 * (u * v) := by
    have hY0u : (Y0 : ℝ) = u - 1 := by simp only [hu]; ring
    rw [hY0u]; linarith [hJR, huv]
  have hfinal : (2 * u + 4 * T + 16 * (u * v)) / (2 : ℝ) ^ J ≤ 24 / v ^ 2 := by
    rw [div_le_div_iff₀ hden0 (by positivity)]
    have hu1 : (1 : ℝ) ≤ u := by linarith
    have hv0 : (0 : ℝ) < v := by linarith
    have hu0 : (0 : ℝ) < u := by linarith
    have hut : (1 : ℝ) ≤ u * T := by nlinarith
    have hbase : (0 : ℝ) ≤ u * v ^ 2 := by positivity
    have e1 : 2 * u * v ^ 2 ≤ 2 * (u ^ 2 * v ^ 2 * T) := by
      have := mul_le_mul_of_nonneg_left hut hbase
      nlinarith [this]
    have e2 : 4 * T * v ^ 2 ≤ 4 * (u ^ 2 * v ^ 2 * T) := by
      have hu2' : (1 : ℝ) ≤ u ^ 2 := by nlinarith
      have hb : (0 : ℝ) ≤ T * v ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hu2' hb]
    have e3 : 16 * (u * v) * v ^ 2 ≤ 16 * (u ^ 2 * v ^ 2 * T) := by
      have hvuT : v ≤ u * T := by nlinarith
      have hb : (0 : ℝ) ≤ u * v ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hvuT hb]
    have key : (2 * u + 4 * T + 16 * (u * v)) * v ^ 2 ≤ 24 * (u ^ 2 * v ^ 2 * T) := by
      nlinarith [e1, e2, e3, mul_pos (mul_pos (mul_pos hu0 hu0) (mul_pos hv0 hv0))
        (show (0:ℝ) < T by linarith)]
    linarith [key, hden]
  calc (2 * ((Y0 : ℝ) + (J : ℝ)) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J
      = (2 * ((Y0 : ℝ) + (J : ℝ)) + 2 * (J : ℝ) + 2) / (2 : ℝ) ^ J := by
        rw [div_pow, one_pow]; ring
    _ ≤ (2 * u + 4 * T + 16 * (u * v)) / (2 : ℝ) ^ J := by
        gcongr
    _ ≤ 24 / v ^ 2 := hfinal

/-! ### Permanent boundary controls -/

/-- Empty tail range: `k = J` gives the zero sum, and the bound is nonnegative. -/
example {R A M H k : ℕ} (hA : 0 < A) (hR : 0 < R) (hH : 1 ≤ H) :
    (∑ m ∈ range M, ∑ j ∈ Ico k k, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j) = 0 := by
  simp

/-- Degenerate `M = 0`: no candidate indices, zero tail. -/
example {R A H k J : ℕ} :
    (∑ m ∈ range 0, ∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j) = 0 := by
  simp

/-- `L = k` collapses the near range: every `j` is paid at `τ(A)`.  This is the control that
the middle-range factor is not silently dropped. -/
example : (2 : ℝ) * (1 / 2 : ℝ) ^ 3 + (tau 12 : ℝ) * (2 * (1 / 2 : ℝ) ^ 3)
    = 2 * (1 / 2 : ℝ) ^ 3 * (1 + (tau 12 : ℝ)) := by ring

/-- `τ(12) = 6`, so the middle-range factor is genuinely larger than `1`. -/
example : tau 12 = 6 := by decide

end NormalNumbers.JointLambert
