/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4UnboundedJunk
import Mathlib.NumberTheory.Primorial

/-!
# Campaign B: `c_p ≤ ⌊log₂ p⌋` is tame

`Tame c A` asks for a linear prime-prefix bound and a convergent tail.  Both hold for the
logarithmic coefficient vector, and hence for anything dominated by it (in particular the
doubly-logarithmic vectors the schedule can actually pay for — see
`DESIGN-2026-09-16-prime-subset.md`).

* **prefix**: `2^{∑_{p<M} ⌊log₂ p⌋} = ∏_{p<M} 2^{⌊log₂ p⌋} ≤ ∏_{p<M} p ≤ M# ≤ 4^M`, so the sum
  is at most `2M` — Chebyshev, with no analysis;
* **tail**: `⌊log₂ n⌋ = #{j ≥ 1 : 2^j ≤ n}`, so after swapping the order of summation the tail
  is at most `∑_{j ≥ 1} ∑_{n ≥ 2^j} 1/(n(n−1)) = ∑_{j ≥ 1} 1/(2^j − 1) ≤ 2`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- **The Chebyshev prefix bound**: `∑_{p < M} ⌊log₂ p⌋ ≤ 2M`. -/
theorem sum_natLog_primesBelow_le (M : ℕ) :
    ∑ p ∈ M.primesBelow, Nat.log 2 p ≤ 2 * M := by
  classical
  have hpow : (2 : ℕ) ^ (∑ p ∈ M.primesBelow, Nat.log 2 p)
      = ∏ p ∈ M.primesBelow, 2 ^ Nat.log 2 p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
  have hle : ∏ p ∈ M.primesBelow, 2 ^ Nat.log 2 p ≤ ∏ p ∈ M.primesBelow, p := by
    refine Finset.prod_le_prod' fun p hp => ?_
    have hp1 : 0 < p := (Nat.mem_primesBelow.1 hp).2.pos
    exact Nat.pow_log_le_self 2 hp1.ne'
  have hsub : ∏ p ∈ M.primesBelow, p ≤ primorial M := by
    rw [primorial]
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      have h1 := Nat.mem_primesBelow.1 hp
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h1.2⟩
    · intro p _ _
      exact (Nat.prime_of_mem_primesLE (by
        simpa [Nat.primesLE] using ‹_›)).one_lt.le
  have h4 : primorial M ≤ 4 ^ M := primorial_le_four_pow M
  have hchain : (2 : ℕ) ^ (∑ p ∈ M.primesBelow, Nat.log 2 p) ≤ 2 ^ (2 * M) := by
    calc (2 : ℕ) ^ (∑ p ∈ M.primesBelow, Nat.log 2 p)
        = ∏ p ∈ M.primesBelow, 2 ^ Nat.log 2 p := hpow
      _ ≤ ∏ p ∈ M.primesBelow, p := hle
      _ ≤ primorial M := hsub
      _ ≤ 4 ^ M := h4
      _ = 2 ^ (2 * M) := by rw [pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hchain


/-! ### The telescoping tail from an arbitrary start -/

/-- `∑_{n=m}^{M} 1/(n(n−1)) = 1/(m−1) − 1/M` for `2 ≤ m` and `m − 1 ≤ M`. -/
lemma sum_inv_mul_pred_Icc_eq {m : ℕ} (hm : 2 ≤ m) {M : ℕ} (hM : m - 1 ≤ M) :
    ∑ n ∈ Icc m M, 1 / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / ((m : ℝ) - 1) - 1 / (M : ℝ) := by
  have hmr : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub this]
    ring
  induction M, hM using Nat.le_induction with
  | base =>
      have hempty : Icc m (m - 1) = (∅ : Finset ℕ) := by
        refine Finset.Icc_eq_empty ?_
        omega
      rw [hempty, hmr]
      simp
  | succ M hM ih =>
      have hmM : m ≤ M + 1 := by omega
      have hM0 : 1 ≤ M := by omega
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
      rw [Finset.sum_Icc_succ_top hmM, ih]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have h1 : (M : ℝ) + 1 - 1 = (M : ℝ) := by ring
      rw [h1]
      field_simp
      ring

/-- `∑_{n=m}^{M} 1/(n(n−1)) ≤ 1/(m−1)`. -/
lemma sum_inv_mul_pred_Icc_le {m : ℕ} (hm : 2 ≤ m) (M : ℕ) :
    ∑ n ∈ Icc m M, 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / ((m : ℝ) - 1) := by
  rcases le_or_gt (m - 1) M with hM | hM
  · rw [sum_inv_mul_pred_Icc_eq hm hM]
    have : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  · have hempty : Icc m M = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

/-! ### The tail: swap the order of summation -/

/-- **The convergent tail**: `∑_{p < M} ⌊log₂ p⌋/(p(p−1)) ≤ 4`, by writing
`⌊log₂ p⌋ = #{j ≥ 1 : 2^j ≤ p}` and summing over `j` first. -/
theorem sum_natLog_div_primesBelow_le (M : ℕ) :
    ∑ p ∈ M.primesBelow, (Nat.log 2 p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 4 := by
  classical
  set S := M.primesBelow with hS
  set J := Nat.log 2 M with hJ
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * ((n : ℝ) - 1)) with hf
  have hf0 : ∀ n : ℕ, 2 ≤ n → 0 ≤ f n := by
    intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    simp only [hf]
    positivity
  have hmem : ∀ p ∈ S, 2 ≤ p ∧ p < M := by
    intro p hp
    have h := Nat.mem_primesBelow.1 hp
    exact ⟨h.2.two_le, h.1⟩
  -- the filter identity
  have hfil : ∀ p ∈ S, (Icc 1 J).filter (fun j => 2 ^ j ≤ p) = Icc 1 (Nat.log 2 p) := by
    intro p hp
    obtain ⟨hp2, hpM⟩ := hmem p hp
    have hlogle : Nat.log 2 p ≤ J := Nat.log_mono_right (le_of_lt hpM)
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans hlogle⟩,
        (Nat.le_log_iff_pow_le (by norm_num) (by omega)).1 h2⟩
  have hsplit : ∀ p ∈ S, (Nat.log 2 p : ℝ) * f p
      = ∑ j ∈ Icc 1 J, (if 2 ^ j ≤ p then f p else 0) := by
    intro p hp
    rw [← Finset.sum_filter, hfil p hp, Finset.sum_const, Nat.card_Icc]
    simp [mul_comm]
  have hgoal : ∑ p ∈ S, (Nat.log 2 p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      = ∑ j ∈ Icc 1 J, ∑ p ∈ S, (if 2 ^ j ≤ p then f p else 0) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hsplit p hp, hf]
    ring
  rw [hgoal]
  -- each layer is at most `2·(1/2)^j`
  have hlayer : ∀ j ∈ Icc 1 J, ∑ p ∈ S, (if 2 ^ j ≤ p then f p else 0)
      ≤ 2 * (1 / 2 : ℝ) ^ j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hsub : ∑ p ∈ S, (if 2 ^ j ≤ p then f p else 0) ≤ ∑ n ∈ Icc (2 ^ j) M, f n := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        have h := Finset.mem_filter.1 hp
        obtain ⟨hp2, hpM⟩ := hmem p h.1
        exact Finset.mem_Icc.2 ⟨h.2, by omega⟩
      · intro n hn _
        have h2 : 2 ≤ n := by
          have := (Finset.mem_Icc.1 hn).1
          have h2j : 2 ≤ 2 ^ j := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
          omega
        exact hf0 n h2
    have h2j : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    have htel := sum_inv_mul_pred_Icc_le (m := 2 ^ j) h2j M
    have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
    rw [hcast] at htel
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast h2j
    have hfinal : 1 / ((2 : ℝ) ^ j - 1) ≤ 2 * (1 / 2 : ℝ) ^ j := by
      have hx : (2 : ℝ) ^ j / 2 ≤ (2 : ℝ) ^ j - 1 := by linarith
      have hpos : (0 : ℝ) < (2 : ℝ) ^ j / 2 := by positivity
      have hstep : 1 / ((2 : ℝ) ^ j - 1) ≤ 1 / ((2 : ℝ) ^ j / 2) :=
        one_div_le_one_div_of_le hpos hx
      have heq : 1 / ((2 : ℝ) ^ j / 2) = 2 * (1 / 2 : ℝ) ^ j := by
        rw [one_div_pow]
        field_simp
      linarith [hstep, heq.le, heq.ge]
    exact le_trans (le_trans hsub htel) hfinal
  calc ∑ j ∈ Icc 1 J, ∑ p ∈ S, (if 2 ^ j ≤ p then f p else 0)
      ≤ ∑ j ∈ Icc 1 J, 2 * (1 / 2 : ℝ) ^ j := Finset.sum_le_sum hlayer
    _ = 2 * ∑ j ∈ Icc 1 J, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
        intro j hj
        have := Finset.mem_Icc.1 hj
        exact Finset.mem_range.2 (by omega)
    _ ≤ 2 * 2 := by
        have := sum_geometric_two_le (J + 1)
        linarith
    _ = 4 := by norm_num

/-- **`c_p ≤ ⌊log₂ p⌋` is tame** (with `A = 4`), so every doubly-logarithmic coefficient
vector is tame too. -/
theorem tame_of_natLog_le {c : ℕ → ℕ} (h : ∀ p, c p ≤ Nat.log 2 p) :
    PrimeLambert.Tame c 4 := by
  refine ⟨by norm_num, fun M => ?_, fun M => ?_⟩
  · refine le_trans (Finset.sum_le_sum fun p hp => ?_) (sum_natLog_div_primesBelow_le M)
    have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
    have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    gcongr
    exact_mod_cast h p
  · have hstep : ∑ p ∈ M.primesBelow, (c p : ℝ) ≤ ∑ p ∈ M.primesBelow, (Nat.log 2 p : ℝ) :=
      Finset.sum_le_sum fun p _ => by exact_mod_cast h p
    have hnat : ∑ p ∈ M.primesBelow, Nat.log 2 p ≤ 2 * M := sum_natLog_primesBelow_le M
    have hcast : ∑ p ∈ M.primesBelow, (Nat.log 2 p : ℝ) ≤ 2 * (M : ℝ) := by
      have : ((∑ p ∈ M.primesBelow, Nat.log 2 p : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at this
      exact this
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
    linarith

end NormalNumbers.G4
