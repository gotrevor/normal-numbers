/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4MertensAP

/-!
# Campaign A, step A3: from a Mertens rate to a schedule-admissible cutoff exponent

The base-`b` schedule (`G4SchedB*`) uses the cutoff `R = 2^{2^e}` with `e = m₁ b K`, and consumes
the lower Mertens bound only through

    `Sg = ∑_{p ∈ smallPrimes R P₀} 1/p ≥ (2·K·r + 4)/(4θ)`   (`G4SchedBBudget.main_term_le`),

a demand depending on `K` alone (`DESIGN-2026-09-16-prime-subset.md`).  The exponent `e` is free
between that demand and the moment cap `10⁵·T K·e ≤ 2^{8K²}`.

This module is the bridge: `MertensRate S c C` (proved for residue classes in `G4MertensAP`)
produces, for **any** demand `M`, an exponent `e` meeting it, together with the explicit bound
`e ≤ (M + C + c)/(c log 2) + 1` that the cap check needs.  Since the demand is
`exp(O(K log K))` and the cap is `exp(Θ(K²))`, the bound is satisfied for all large `K` — that
is the whole content of "a constant-factor Mertens loss is free for this schedule".
-/

open Finset Real

namespace NormalNumbers.G4.MertensAP

variable {S : ℕ → Prop} [DecidablePred S]

/-- `log log 2 ≥ −1/2`, the only numeric fact needed to convert `log log (2^{2^e})` into
`e · log 2` up to a constant. -/
lemma neg_half_le_log_log_two : (-(1 / 2) : ℝ) ≤ Real.log (Real.log 2) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log (Real.log 2)⁻¹ ≤ (Real.log 2)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at hle
  have hlow : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hinv : (Real.log 2)⁻¹ ≤ 1.4427 := by
    rw [inv_le_comm₀ h2 (by norm_num)]
    nlinarith
  linarith

/-- `log log (2^{2^e}) ≥ e·log 2 − 1/2`. -/
lemma log_log_tower_ge (e : ℕ) :
    (e : ℝ) * Real.log 2 - 1 / 2 ≤ Real.log (Real.log ((2 ^ 2 ^ e : ℕ) : ℝ)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log ((2 ^ 2 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ e * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog, Real.log_mul (by positivity) h2.ne', Real.log_pow]
  push_cast
  linarith [neg_half_le_log_log_two]

/-- **The bridge.**  A Mertens rate meets any demand `M` at an explicitly bounded cutoff
exponent.  The schedule then only has to check `e` against its moment cap. -/
theorem exists_exponent {c C : ℝ} (h : MertensRate S c C) (M : ℝ) :
    ∃ e : ℕ, M ≤ sumInvPrimesIn S (2 ^ 2 ^ e)
      ∧ (e : ℝ) ≤ max 0 ((M + C + c) / (c * Real.log 2)) + 1 := by
  obtain ⟨hc, hMert⟩ := h
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set t : ℝ := (M + C + c) / (c * Real.log 2) with ht
  refine ⟨⌈t⌉₊, ?_, ?_⟩
  · have hN : 2 ≤ (2 : ℕ) ^ 2 ^ ⌈t⌉₊ := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ ⌈t⌉₊ := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    have hM := hMert _ hN
    have hge : (⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2
        ≤ Real.log (Real.log ((2 ^ 2 ^ ⌈t⌉₊ : ℕ) : ℝ)) := log_log_tower_ge _
    have hceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hkey : M + C + c ≤ (⌈t⌉₊ : ℝ) * (c * Real.log 2) := by
      have := mul_le_mul_of_nonneg_right hceil (by positivity : (0 : ℝ) ≤ c * Real.log 2)
      rw [ht, div_mul_cancel₀] at this
      · linarith
      · positivity
    have hcc : c * ((⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2) - C ≤ c * Real.log (Real.log ((2 ^ 2 ^ ⌈t⌉₊ : ℕ) : ℝ)) - C := by
      have := mul_le_mul_of_nonneg_left hge hc.le
      linarith
    have hfin : M ≤ c * ((⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2) - C := by
      have hexp : c * ((⌈t⌉₊ : ℝ) * Real.log 2 - 1 / 2)
          = (⌈t⌉₊ : ℝ) * (c * Real.log 2) - c / 2 := by ring
      rw [hexp]
      linarith
    linarith [hM, hcc, hfin]
  · rcases le_or_gt 0 t with ht0 | ht0
    · have hlt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
      have : t ≤ max 0 t := le_max_right _ _
      linarith
    · have h0 : ⌈t⌉₊ = 0 := by
        rw [Nat.ceil_eq_zero]
        exact ht0.le
      rw [h0]
      have : (0 : ℝ) ≤ max 0 t := le_max_left _ _
      push_cast
      linarith

end NormalNumbers.G4.MertensAP
