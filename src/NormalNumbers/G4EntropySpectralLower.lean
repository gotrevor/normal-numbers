/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Tensor

/-!
# The `√K` in the cover bound is real: a matching lower bound

Laps 32–33 *measured* the deficit `δ_K ≍ √K` of `entropy_E1` and traced it to
`log_det_one_add_tensorGram_le'`, concluding "beating the order needs cancellation across `j`
in `∑_j log(1 + Λ_j)`".  This module settles that as a **theorem**: there is no cancellation
to be had, because

    `log det (1 + T_{K²}^{⊗K}) ≥ c · (K²)^K · √K`

for an explicit `c > 0` and all large `K`.  So the upper bound
`log det (1 + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 12√K)` is of the **right order**, and the
expedition's word-length ceiling `ℓ = o(√K)` is a property of the object, not of the estimate.

The proof is a fourth-moment (Paley–Zygmund / Khintchine) lower bound, entirely finite:

* `posPart_le_log_one_add` — `(log Λ)^+ ≤ log(1 + Λ)`, so the determinant dominates the
  positive part of the log-spectrum;
* centering the one-site log-spectrum makes `∑_j log Λ̃_j = 0` **exactly**, so
  `∑_j (log Λ̃_j)^+ = ½ ∑_j |log Λ̃_j|`, and `(log Λ)^+ ≥ (log Λ̃)^+` because the centering
  shift `K log(s+1)/s` is nonnegative;
* `sum_abs_ge_sq_mul_sqrt` — two Cauchy–Schwarz steps give `(∑X²)³ ≤ (∑|X|)² (∑X⁴)`;
* `sum_pi_quad` — the exact fourth moment of `X_j = ∑_i ℓ(j_i)` for centered `ℓ`:
  `s² ∑_j X_j⁴ = K s^{K+1} ∑ ℓ⁴ + 3K(K−1) s^K (∑ ℓ²)²` — the `3K²` here is what turns the
  ratio `(∑X²)³/(∑X⁴)` into `Θ(K)` and produces the `√K`;
* `sum_sq_log_lam_ge` / `sum_quad_log_lam_le` — the one-site spectrum has second log-moment
  `≥ (log²2/2) s` (half the eigenvalues are `≥ 2`) and fourth log-moment `O(s)`.
-/

open Finset Real

namespace NormalNumbers.G4

/-! ### §1  Elementary inequalities -/

/-- `(log Λ)^+ ≤ log (1 + Λ)` for `Λ > 0`. -/
theorem posPart_le_log_one_add {Λ : ℝ} (h : 0 < Λ) :
    max (Real.log Λ) 0 ≤ Real.log (1 + Λ) := by
  refine max_le ?_ ?_
  · exact Real.log_le_log h (by linarith)
  · exact Real.log_nonneg (by linarith)

/-- Two Cauchy–Schwarz steps: `(∑ X²)³ ≤ (∑ |X|)² (∑ X⁴)`. -/
theorem sum_sq_cube_le {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    (∑ j, X j ^ 2) ^ 3 ≤ (∑ j, |X j|) ^ 2 * ∑ j, X j ^ 4 := by
  set A := ∑ j, |X j| with hA
  set B := ∑ j, X j ^ 2 with hB
  set C := ∑ j, X j ^ 4 with hC
  set D := ∑ j, |X j| * X j ^ 2 with hD
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => by positivity
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => by positivity
  -- Step 1: `B² ≤ A · D` (Cauchy–Schwarz with `√|X|` and `|X|√|X|`)
  have h1 : B ^ 2 ≤ A * D := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => Real.sqrt |X j|) (fun j => |X j| * Real.sqrt |X j|)
    have e1 : ∀ j : ι, Real.sqrt |X j| * (|X j| * Real.sqrt |X j|) = X j ^ 2 := by
      intro j
      have : Real.sqrt |X j| * Real.sqrt |X j| = |X j| :=
        Real.mul_self_sqrt (abs_nonneg _)
      calc Real.sqrt |X j| * (|X j| * Real.sqrt |X j|)
          = (Real.sqrt |X j| * Real.sqrt |X j|) * |X j| := by ring
        _ = |X j| * |X j| := by rw [this]
        _ = X j ^ 2 := by rw [abs_mul_abs_self]; ring
    have e2 : ∀ j : ι, Real.sqrt |X j| ^ 2 = |X j| := fun j => Real.sq_sqrt (abs_nonneg _)
    have e3 : ∀ j : ι, (|X j| * Real.sqrt |X j|) ^ 2 = |X j| * X j ^ 2 := by
      intro j
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
      ring
    simp_rw [e1, e2, e3] at h
    exact h
  -- Step 2: `D² ≤ B · C`
  have h2 : D ^ 2 ≤ B * C := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |X j|) (fun j => X j ^ 2)
    have e2 : ∀ j : ι, |X j| ^ 2 = X j ^ 2 := fun j => sq_abs _
    have e3 : ∀ j : ι, (X j ^ 2) ^ 2 = X j ^ 4 := fun j => by ring
    simp_rw [e2, e3] at h
    exact h
  rcases eq_or_lt_of_le hB0 with hB1 | hB1
  · rw [← hB1]
    have : (0 : ℝ) ≤ A ^ 2 * C := mul_nonneg (sq_nonneg A) hC0
    linarith [this]
  · -- `B⁴ ≤ A²D² ≤ A²BC`
    have h3 : B ^ 4 ≤ A ^ 2 * D ^ 2 := by
      nlinarith [h1, hB0, mul_nonneg hA0 hD0]
    have h4 : A ^ 2 * D ^ 2 ≤ A ^ 2 * (B * C) := mul_le_mul_of_nonneg_left h2 (sq_nonneg A)
    have h6 : B ^ 3 * B ≤ (A ^ 2 * C) * B := by nlinarith
    exact le_of_mul_le_mul_right h6 hB1

/-- The Paley–Zygmund form: `∑ |X| ≥ (∑X²) √((∑X²)/(∑X⁴))`. -/
theorem sum_abs_ge_sq_mul_sqrt {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    (∑ j, X j ^ 2) * Real.sqrt ((∑ j, X j ^ 2) / ∑ j, X j ^ 4) ≤ ∑ j, |X j| := by
  set A := ∑ j, |X j| with hA
  set B := ∑ j, X j ^ 2 with hB
  set C := ∑ j, X j ^ 4 with hC
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => by positivity
  rcases eq_or_lt_of_le hC0 with hC1 | hC1
  · rw [← hC1, div_zero, Real.sqrt_zero, mul_zero]; exact hA0
  · have hkey : B ^ 3 ≤ A ^ 2 * C := sum_sq_cube_le X
    have hsplit : B * Real.sqrt (B / C) = Real.sqrt (B ^ 2 * (B / C)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB0]
    rw [hsplit]
    have hle : B ^ 2 * (B / C) ≤ A ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hC1]
      calc B ^ 2 * B = B ^ 3 := by ring
        _ ≤ A ^ 2 * C := hkey
    calc Real.sqrt (B ^ 2 * (B / C)) ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hle
      _ = A := Real.sqrt_sq hA0

/-! ### §2  The fourth moment of a sum of `K` independent coordinates -/

/-- **Exact fourth moment** for a centered one-site weight `ℓ`. -/
theorem sum_pi_quad {s : ℕ} (hs : 1 ≤ s) (ℓ : Fin s → ℝ) (h1 : ∑ k, ℓ k = 0) (K : ℕ) :
    (s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 4
      = K * (s : ℝ) ^ (K + 1) * (∑ k, ℓ k ^ 4)
        + 3 * K * (K - 1) * (s : ℝ) ^ K * (∑ k, ℓ k ^ 2) ^ 2 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  induction K with
  | zero => simp
  | succ K ih =>
    -- the first moment vanishes, and the second is `K s^{K−1} ∑ ℓ²`
    have hP : ∑ j : Fin K → Fin s, ∑ i, ℓ (j i) = 0 := by
      have h := sum_pi_linear ℓ K
      rw [h1, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hs'.ne'
    have hQ2 : (s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 2
        = K * (s : ℝ) ^ (K + 1) * (∑ k, ℓ k ^ 2) := by
      have h := sum_pi_sq ℓ K
      rw [h1] at h
      simpa using h
    have key : ∀ a : Fin s, ∑ j' : Fin K → Fin s, (ℓ a + ∑ i, ℓ (j' i)) ^ 4
        = (s : ℝ) ^ K * ℓ a ^ 4
          + 6 * (ℓ a ^ 2 * ∑ j' : Fin K → Fin s, (∑ i, ℓ (j' i)) ^ 2)
          + 4 * (ℓ a * ∑ j' : Fin K → Fin s, (∑ i, ℓ (j' i)) ^ 3)
          + ∑ j' : Fin K → Fin s, (∑ i, ℓ (j' i)) ^ 4 := by
      intro a
      have e : ∀ j' : Fin K → Fin s, (ℓ a + ∑ i, ℓ (j' i)) ^ 4
          = ℓ a ^ 4 + 4 * ℓ a ^ 3 * (∑ i, ℓ (j' i))
            + 6 * (ℓ a ^ 2 * (∑ i, ℓ (j' i)) ^ 2)
            + 4 * (ℓ a * (∑ i, ℓ (j' i)) ^ 3) + (∑ i, ℓ (j' i)) ^ 4 :=
        fun j' => by ring
      simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hP, Finset.sum_const,
        Finset.card_univ, Fintype.card_pi, Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_fin]
      push_cast
      ring
    rw [sum_pi_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h1,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    push_cast at ih hQ2
    linear_combination (6 * ∑ i, ℓ i ^ 2) * hQ2 + (s : ℝ) * ih

/-! ### §3  The one-site log-spectrum: second moment from below, fourth from above -/

/-- For the upper half of the indices the angle is at least `π/2`, hence `λ_j ≥ 2`. -/
theorem two_le_lam {s : ℕ} {j : Fin s} (hj : s / 2 ≤ (j : ℕ)) : 2 ≤ lam s j := by
  have hhalf : π / 2 ≤ angle s j := by
    unfold angle
    rw [le_div_iff₀ (by positivity)]
    have h2 : (s : ℝ) ≤ 2 * (j : ℕ) + 1 := by
      have : s ≤ 2 * (s / 2) + 1 := by omega
      have h3 : s ≤ 2 * (j : ℕ) + 1 := by omega
      exact_mod_cast h3
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (angle s j) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [angle_lt_pi j, Real.pi_pos])
  unfold lam; linarith

/-- At least half the eigenvalues satisfy `λ_j ≥ 2`, so `∑_j log²λ_j ≥ (log²2)·s/2`. -/
theorem sum_sq_log_lam_ge (s : ℕ) :
    Real.log 2 ^ 2 * ((s : ℝ) / 2) ≤ ∑ j : Fin s, Real.log (lam s j) ^ 2 := by
  classical
  set T : Finset (Fin s) := Finset.univ.filter (fun j : Fin s => s / 2 ≤ (j : ℕ)) with hT
  have himg : T.image (Fin.val) = Finset.Ico (s / 2) s := by
    ext n
    simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨hj, j.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  have hcard : T.card = s - s / 2 := by
    rw [← Finset.card_image_of_injective T Fin.val_injective, himg, Nat.card_Ico]
  have hlow : ∀ j ∈ T, Real.log 2 ^ 2 ≤ Real.log (lam s j) ^ 2 := by
    intro j hj
    have hj' : s / 2 ≤ (j : ℕ) := by simpa [hT] using hj
    have h2 : Real.log 2 ≤ Real.log (lam s j) :=
      Real.log_le_log (by norm_num) (two_le_lam hj')
    have h0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hsub : ∑ j ∈ T, Real.log (lam s j) ^ 2 ≤ ∑ j : Fin s, Real.log (lam s j) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun j _ _ => sq_nonneg _)
  have hconst : (T.card : ℝ) * Real.log 2 ^ 2 ≤ ∑ j ∈ T, Real.log (lam s j) ^ 2 := by
    calc (T.card : ℝ) * Real.log 2 ^ 2 = ∑ _j ∈ T, Real.log 2 ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hlow
  have hcast : (s : ℝ) / 2 ≤ (T.card : ℝ) := by
    rw [hcard, Nat.cast_sub (Nat.div_le_self s 2)]
    have := Nat.cast_div_le (α := ℝ) (m := s) (n := 2)
    push_cast at this ⊢
    linarith
  nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num), sq_nonneg (Real.log 2)]

/-- `log⁴ y ≤ 4096 √y` for `y ≥ 1` (via `log y = 8 log y^{1/8} ≤ 8 y^{1/8}`). -/
theorem quad_log_le_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 4 ≤ 4096 * Real.sqrt y := by
  have h0 : 0 ≤ y := by linarith
  set q := Real.sqrt (Real.sqrt (Real.sqrt y)) with hq
  have hs1 : 1 ≤ Real.sqrt y := (Real.le_sqrt zero_le_one h0).mpr (by rw [one_pow]; exact hy)
  have hs2 : 1 ≤ Real.sqrt (Real.sqrt y) :=
    (Real.le_sqrt zero_le_one (Real.sqrt_nonneg _)).mpr (by rw [one_pow]; exact hs1)
  have hq1 : 1 ≤ q :=
    (Real.le_sqrt zero_le_one (Real.sqrt_nonneg _)).mpr (by rw [one_pow]; exact hs2)
  have hlog : Real.log y = 8 * Real.log q := by
    rw [hq, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
      Real.log_sqrt h0]
    ring
  have hlq : Real.log q ≤ q := by
    have := Real.log_le_sub_one_of_pos (x := q) (by linarith)
    linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have h4 : Real.log q ^ 4 ≤ q ^ 4 := by
    have := pow_le_pow_left₀ hlq0 hlq 4
    exact this
  have hq4 : q ^ 4 = Real.sqrt y := by
    rw [hq, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [hlog, mul_pow, ← hq4]
  nlinarith [h4]

/-- `∑_j √((s+1)/(j+1)) ≤ 2(s+1)`. -/
theorem sum_sqrt_ratio_le (s : ℕ) :
    ∑ j : Fin s, Real.sqrt (((s : ℝ) + 1) / ((j : ℝ) + 1)) ≤ 2 * ((s : ℝ) + 1) := by
  calc ∑ j : Fin s, Real.sqrt (((s : ℝ) + 1) / ((j : ℝ) + 1))
      = Real.sqrt ((s : ℝ) + 1) * ∑ k ∈ Finset.range s, 1 / Real.sqrt ((k : ℝ) + 1) := by
        rw [Finset.mul_sum, Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.sqrt_div (by positivity)]; ring
    _ ≤ Real.sqrt ((s : ℝ) + 1) * (2 * Real.sqrt s) := by
        gcongr
        exact sum_inv_sqrt_le s
    _ ≤ 2 * ((s : ℝ) + 1) := by
        have h1 := Real.sqrt_le_sqrt (show (s : ℝ) ≤ s + 1 by linarith)
        have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ s + 1 by positivity)
        nlinarith [Real.sqrt_nonneg (s : ℝ), Real.sqrt_nonneg ((s : ℝ) + 1)]

/-- Fourth log-moment of the spectrum: `∑_j log⁴λ_j = O(s)`. -/
theorem sum_quad_log_lam_le {s : ℕ} (hs : 1 ≤ s) :
    ∑ j : Fin s, Real.log (lam s j) ^ 4 ≤ 4194304 * (s : ℝ) := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hterm : ∀ j : Fin s, Real.log (lam s j) ^ 4
      ≤ 128 + 128 * Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 4 := by
    intro j
    have ha : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have ha2 : Real.log 4 ≤ 2 := le_of_lt log_four_lt_two
    have hb : 0 ≤ Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) := Real.log_nonneg (one_le_ratio j)
    have h1 := log_lam_le j
    have h2 := log_lam_ge j
    set a := Real.log 4
    set b := Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1))
    set x := Real.log (lam s j)
    have hx1 : x ≤ a + 2 * b := by linarith
    have hx2 : -(a + 2 * b) ≤ x := by linarith
    have hpow : x ^ 4 ≤ (a + 2 * b) ^ 4 := by
      have habs : |x| ≤ a + 2 * b := abs_le.mpr ⟨hx2, hx1⟩
      have : |x| ^ 4 ≤ (a + 2 * b) ^ 4 := pow_le_pow_left₀ (abs_nonneg x) habs 4
      rwa [show |x| ^ 4 = x ^ 4 by rw [← abs_pow, abs_of_nonneg (by positivity)]] at this
    have hstep1 : (a + 2 * b) ^ 4 ≤ (2 + 2 * b) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hstep2 : (2 + 2 * b) ^ 4 ≤ 128 + 128 * b ^ 4 := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (b ^ 2 - b),
        sq_nonneg b, hb, mul_nonneg hb hb]
    linarith
  have hsum : ∑ j : Fin s, Real.log (lam s j) ^ 4
      ≤ 128 * s + 128 * ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 4 := by
    calc ∑ j : Fin s, Real.log (lam s j) ^ 4
        ≤ ∑ j : Fin s, (128 + 128 * Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 4) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = 128 * s + 128 * ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 4 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have hratio : ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 4
      ≤ 8192 * ((s : ℝ) + 1) := by
    calc ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 4
        ≤ ∑ j : Fin s, 4096 * Real.sqrt (((s : ℝ) + 1) / ((j : ℝ) + 1)) :=
          Finset.sum_le_sum fun j _ => quad_log_le_sqrt (one_le_ratio j)
      _ = 4096 * ∑ j : Fin s, Real.sqrt (((s : ℝ) + 1) / ((j : ℝ) + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ 4096 * (2 * ((s : ℝ) + 1)) := by
          gcongr
          exact sum_sqrt_ratio_le s
      _ = 8192 * ((s : ℝ) + 1) := by ring
  nlinarith [hsum, hratio, hs']

/-! ### §4  The Khintchine lower bound for a centered product weight -/

set_option maxHeartbeats 800000 in
/-- **The fourth-moment lower bound.**  For a centered one-site weight `ℓ` whose second moment
is bounded below by `c s` and above by `U s`, and whose fourth moment is at most `M s`,
the `K`-fold sums `X_j = ∑_i ℓ(j_i)` satisfy

    `∑_j |X_j| ≥ c √(c/(M + 3U²)) · s^K · √K`.

The `√K` is produced by the `3K(K−1)(∑ℓ²)²` term of `sum_pi_quad`: the fourth moment is only
`O(K²)` times the square of the second, so the ratio `(∑X²)³/(∑X⁴)` is of order `K`. -/
theorem sum_abs_pi_ge {s : ℕ} (hs : 1 ≤ s) (ℓ : Fin s → ℝ) (h1 : ∑ k, ℓ k = 0) {K : ℕ}
    (hK : 1 ≤ K) {c U M : ℝ} (hc : 0 < c) (hU : 0 ≤ U) (hM : 0 < M)
    (hlow : c * s ≤ ∑ k, ℓ k ^ 2) (hup : ∑ k, ℓ k ^ 2 ≤ U * s)
    (h4 : ∑ k, ℓ k ^ 4 ≤ M * s) :
    c * Real.sqrt (c / (M + 3 * U ^ 2)) * (s : ℝ) ^ K * Real.sqrt K
      ≤ ∑ j : Fin K → Fin s, |∑ i, ℓ (j i)| := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set P : ℝ := M + 3 * U ^ 2 with hP
  have hPpos : 0 < P := by positivity
  set X : (Fin K → Fin s) → ℝ := fun j => ∑ i, ℓ (j i) with hX
  set B : ℝ := ∑ j, X j ^ 2 with hBdef
  set C : ℝ := ∑ j, X j ^ 4 with hCdef
  have hspow : (0 : ℝ) < (s : ℝ) ^ K := by positivity
  have hexp1 : (s : ℝ) ^ (K + 1) = (s : ℝ) ^ K * s := by ring
  have hs2 : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  -- second moment from below
  have hB : c * K * (s : ℝ) ^ K ≤ B := by
    have h := sum_pi_sq ℓ K
    rw [h1] at h
    have h' : (s : ℝ) ^ 2 * B = K * (s : ℝ) ^ (K + 1) * ∑ k, ℓ k ^ 2 := by
      simpa [hBdef, hX] using h
    have hmul : K * (s : ℝ) ^ (K + 1) * (c * s) ≤ K * (s : ℝ) ^ (K + 1) * ∑ k, ℓ k ^ 2 :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    rw [← h', hexp1] at hmul
    refine le_of_mul_le_mul_left ?_ hs2
    linarith
  -- fourth moment from above
  have hC : C ≤ (K : ℝ) ^ 2 * P * (s : ℝ) ^ K := by
    have h := sum_pi_quad hs ℓ h1 K
    have hsq : (∑ k, ℓ k ^ 2) ^ 2 ≤ (U * s) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => sq_nonneg _) hup 2
    have hsq0 : (0 : ℝ) ≤ (U * s) ^ 2 := sq_nonneg _
    have hstep : (s : ℝ) ^ 2 * C
        ≤ K * (s : ℝ) ^ (K + 1) * (M * s) + 3 * K * K * (s : ℝ) ^ K * (U * s) ^ 2 := by
      rw [show (s : ℝ) ^ 2 * C = (s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 4 by
        rw [hCdef, hX], h]
      have ha : K * (s : ℝ) ^ (K + 1) * (∑ k, ℓ k ^ 4)
          ≤ K * (s : ℝ) ^ (K + 1) * (M * s) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have hk1 : (0 : ℝ) ≤ 3 * (K : ℝ) * (K - 1) * (s : ℝ) ^ K := by
        have : (0 : ℝ) ≤ (K : ℝ) - 1 := by linarith
        positivity
      have hkk : 3 * (K : ℝ) * (K - 1) * (s : ℝ) ^ K ≤ 3 * (K : ℝ) * K * (s : ℝ) ^ K := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (K : ℝ)) hspow.le]
      have hb : 3 * (K : ℝ) * (K - 1) * (s : ℝ) ^ K * (∑ k, ℓ k ^ 2) ^ 2
          ≤ 3 * K * K * (s : ℝ) ^ K * (U * s) ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left hsq hk1) (mul_le_mul_of_nonneg_right hkk hsq0)
      linarith
    refine le_of_mul_le_mul_left (hstep.trans ?_) hs2
    rw [hexp1]
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hMt : 0 ≤ M * ((s : ℝ) ^ K * s ^ 2) := by positivity
    have key : (K : ℝ) * (M * ((s : ℝ) ^ K * s ^ 2))
        ≤ (K : ℝ) ^ 2 * (M * ((s : ℝ) ^ K * s ^ 2)) := mul_le_mul_of_nonneg_right hKK hMt
    have hPe : (s : ℝ) ^ 2 * ((K : ℝ) ^ 2 * P * (s : ℝ) ^ K)
        = (K : ℝ) ^ 2 * (M * ((s : ℝ) ^ K * s ^ 2))
          + (K : ℝ) ^ 2 * (3 * U ^ 2) * ((s : ℝ) ^ K * s ^ 2) := by rw [hP]; ring
    rw [hPe]
    nlinarith [key]
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hBpos : 0 < B := lt_of_lt_of_le (mul_pos (mul_pos hc hKpos) hspow) hB
  have hCpos : 0 < C := by
    by_contra hcon
    push_neg at hcon
    have hcube : B ^ 3 ≤ (∑ j, |X j|) ^ 2 * C := sum_sq_cube_le X
    have hb3 : B ^ 3 ≤ 0 := by nlinarith [sq_nonneg (∑ j, |X j|)]
    nlinarith [pow_pos hBpos 3]
  -- Paley–Zygmund
  have hPZ : B * Real.sqrt (B / C) ≤ ∑ j, |X j| := sum_abs_ge_sq_mul_sqrt X
  have hratio : c / ((K : ℝ) * P) ≤ B / C := by
    rw [div_le_div_iff₀ (mul_pos hKpos hPpos) hCpos]
    calc c * C ≤ c * ((K : ℝ) ^ 2 * P * (s : ℝ) ^ K) := mul_le_mul_of_nonneg_left hC hc.le
      _ = ((K : ℝ) * P) * (c * K * (s : ℝ) ^ K) := by ring
      _ ≤ ((K : ℝ) * P) * B := mul_le_mul_of_nonneg_left hB (mul_pos hKpos hPpos).le
      _ = B * ((K : ℝ) * P) := by ring
  have hmono : (c * K * (s : ℝ) ^ K) * Real.sqrt (c / ((K : ℝ) * P)) ≤ B * Real.sqrt (B / C) := by
    have h1' : Real.sqrt (c / ((K : ℝ) * P)) ≤ Real.sqrt (B / C) := Real.sqrt_le_sqrt hratio
    have h2' : (0 : ℝ) ≤ Real.sqrt (c / ((K : ℝ) * P)) := Real.sqrt_nonneg _
    exact mul_le_mul hB h1' h2' hBpos.le
  refine le_trans (le_of_eq ?_) (le_trans hmono hPZ)
  -- `c K s^K √(c/(KP)) = c √(c/P) s^K √K`
  have hsK : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt (by linarith)
  have hsKpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKpos
  have hsplit : Real.sqrt (c / ((K : ℝ) * P)) = Real.sqrt (c / P) / Real.sqrt K := by
    rw [show c / ((K : ℝ) * P) = (c / P) / K by field_simp,
      Real.sqrt_div (by positivity)]
  rw [hsplit]
  field_simp
  nlinarith [hsK, hsKpos]

end NormalNumbers.G4
