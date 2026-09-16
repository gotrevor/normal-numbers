/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4LogTame

/-!
# Campaign B: the growth class `c_p ≤ A₀·(1 + log₂log₂ p)^s`

The headline `isDisjunctive_weight_logLog` was proved for `c_p ≤ ⌊log₂log₂ p⌋`.  The schedule
can in fact pay for any *fixed power* of `log₂log₂`, because the two places the coefficient
size enters are both polynomial in `K`:

* `cMax ≤ A₀·(1 + V)^s` with `V = 23K²` (the schedule's prime-size exponent), still polynomial;
* tameness, which only needs a linear prime-prefix bound.

The elementary inequality behind both is `(1 + ℓ)^s ≤ (s+1)^s · 2^ℓ`: writing `q = ℓ / s`,
`1 + ℓ ≤ (s+1)(q+1)` and `(q+1)^s ≤ (2^q)^s = 2^{sq} ≤ 2^ℓ`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- **The elementary polynomial-versus-exponential bound**, with an explicit constant. -/
theorem one_add_pow_le_mul_two_pow (s ℓ : ℕ) : (1 + ℓ) ^ s ≤ (s + 1) ^ s * 2 ^ ℓ := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simpa using Nat.one_le_two_pow
  set q := ℓ / s with hq
  have hlt : ℓ < (q + 1) * s := by
    have hdm := Nat.div_add_mod ℓ s
    have hmod : ℓ % s < s := Nat.mod_lt _ hs
    have : s * q + ℓ % s = ℓ := by rw [hq]; exact hdm
    nlinarith [this, hmod]
  have h1 : 1 + ℓ ≤ (s + 1) * (q + 1) := by nlinarith
  have h2 : (q + 1) ^ s ≤ 2 ^ (s * q) := by
    have : (q + 1) ≤ 2 ^ q := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
    calc (q + 1) ^ s ≤ (2 ^ q) ^ s := Nat.pow_le_pow_left this s
      _ = 2 ^ (s * q) := by rw [← pow_mul]; ring_nf
  have h3 : s * q ≤ ℓ := by
    rw [hq, mul_comm]
    exact Nat.div_mul_le_self ℓ s
  calc (1 + ℓ) ^ s ≤ ((s + 1) * (q + 1)) ^ s := Nat.pow_le_pow_left h1 s
    _ = (s + 1) ^ s * (q + 1) ^ s := by rw [mul_pow]
    _ ≤ (s + 1) ^ s * 2 ^ (s * q) := Nat.mul_le_mul_left _ h2
    _ ≤ (s + 1) ^ s * 2 ^ ℓ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h3)

/-- `(1 + log₂log₂ x)^s ≤ (s+1)^s (1 + log₂ x)` — a power of `log log` is linear in `log`. -/
theorem one_add_logLog_pow_le (s x : ℕ) :
    (1 + Nat.log 2 (Nat.log 2 x)) ^ s ≤ (s + 1) ^ s * (1 + Nat.log 2 x) := by
  have h := one_add_pow_le_mul_two_pow s (Nat.log 2 (Nat.log 2 x))
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  rcases Nat.eq_zero_or_pos (Nat.log 2 x) with h0 | h0
  · rw [h0]; simp
  · calc 2 ^ Nat.log 2 (Nat.log 2 x) ≤ Nat.log 2 x := Nat.pow_log_le_self 2 (by omega)
      _ ≤ 1 + Nat.log 2 x := by omega

/-! ### Tameness of an affine-in-`log₂` coefficient vector -/

/-- `∑_{p < M} 1/(p(p−1)) ≤ 1`. -/
lemma sum_inv_mul_pred_primesBelow_le (M : ℕ) :
    ∑ p ∈ M.primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  classical
  have hsub : M.primesBelow ⊆ Icc 2 M := by
    intro p hp
    have h := Nat.mem_primesBelow.1 hp
    exact Finset.mem_Icc.2 ⟨h.2.two_le, by omega⟩
  have hnn : ∀ n ∈ Icc 2 M, n ∉ M.primesBelow → 0 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn _
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have h := sum_inv_mul_pred_Icc_le (m := 2) (by norm_num) M
  norm_num at h ⊢
  exact h

/-- **An affine bound in `log₂` is tame.** -/
theorem tame_of_affine_natLog {c : ℕ → ℕ} (m : ℕ)
    (h : ∀ p, c p ≤ m * (1 + Nat.log 2 p)) :
    PrimeLambert.Tame c ((5 * m + 1 : ℕ) : ℝ) := by
  classical
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  refine ⟨by
    have : (0 : ℝ) ≤ 5 * (m : ℝ) := by linarith
    push_cast
    linarith, fun M => ?_, fun M => ?_⟩
  · -- tail
    have hstep : ∑ p ∈ M.primesBelow, (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ M.primesBelow,
            ((m : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1)))
              + (m : ℝ) * ((Nat.log 2 p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h2 := (Nat.mem_primesBelow.1 hp).2.two_le
      have h2' : (2 : ℝ) ≤ p := by exact_mod_cast h2
      have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      have hc : (c p : ℝ) ≤ (m : ℝ) * (1 + (Nat.log 2 p : ℝ)) := by
        have := h p
        have : ((c p : ℕ) : ℝ) ≤ ((m * (1 + Nat.log 2 p) : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith
      have hdiv : (c p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
          ≤ ((m : ℝ) * (1 + (Nat.log 2 p : ℝ))) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        gcongr
      refine hdiv.trans (le_of_eq ?_)
      field_simp
    refine hstep.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_inv_mul_pred_primesBelow_le M
    have h2 := sum_natLog_div_primesBelow_le M
    push_cast
    nlinarith
  · -- prefix
    have hcard : (M.primesBelow.card : ℝ) ≤ (M : ℝ) := by
      have : M.primesBelow.card ≤ M := by
        classical
        have hsub : M.primesBelow ⊆ Finset.range M := by
          intro p hp
          exact Finset.mem_range.2 (Nat.mem_primesBelow.1 hp).1
        simpa using Finset.card_le_card hsub
      exact_mod_cast this
    have hstep : ∑ p ∈ M.primesBelow, (c p : ℝ)
        ≤ ∑ p ∈ M.primesBelow, ((m : ℝ) + (m : ℝ) * (Nat.log 2 p : ℝ)) := by
      refine Finset.sum_le_sum fun p _ => ?_
      have := h p
      have h' : ((c p : ℕ) : ℝ) ≤ ((m * (1 + Nat.log 2 p) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    refine hstep.trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
    have hlog : ∑ p ∈ M.primesBelow, (Nat.log 2 p : ℝ) ≤ 2 * (M : ℝ) := by
      have hnat : ∑ p ∈ M.primesBelow, Nat.log 2 p ≤ 2 * M := sum_natLog_primesBelow_le M
      have : ((∑ p ∈ M.primesBelow, Nat.log 2 p : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at this
      exact this
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
    simp only [nsmul_eq_mul]
    push_cast
    nlinarith

/-- **The growth class is tame.**  `c_p ≤ A₀(1 + log₂log₂ p)^s` is tame at
`A = 5·A₀·(s+1)^s + 1`. -/
theorem tame_of_logLog_pow {c : ℕ → ℕ} (A₀ s : ℕ)
    (hc : ∀ x, c x ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 x)) ^ s) :
    PrimeLambert.Tame c ((5 * (A₀ * (s + 1) ^ s) + 1 : ℕ) : ℝ) := by
  refine tame_of_affine_natLog (A₀ * (s + 1) ^ s) fun p => ?_
  calc c p ≤ A₀ * (1 + Nat.log 2 (Nat.log 2 p)) ^ s := hc p
    _ ≤ A₀ * ((s + 1) ^ s * (1 + Nat.log 2 p)) :=
        Nat.mul_le_mul_left _ (one_add_logLog_pow_le s p)
    _ = A₀ * (s + 1) ^ s * (1 + Nat.log 2 p) := by ring

end NormalNumbers.G4
