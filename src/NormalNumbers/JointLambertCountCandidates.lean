/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertCountSchedule

/-!
# Candidate count at a chosen height

§3 of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` turns the prime supply
`π(X; B, u) ≥ X / (2 φ(B) log X)` into a count of **candidate indices**
`m < M = ⌊X/B⌋ + 1` for which `u + mB` is prime, namely at least `M / (4 log X)`.

`candidate_count_ge` is the arithmetic of that step, at a caller-chosen height and with no
schedule hypothesis: the only slack used is `φ(B) ≤ B` and `⌊X/B⌋ + 1 ≤ 2X/B`, the latter
because `B ≤ X`.  This is where the `+1` in `M` is paid for, and it is paid by the factor
`2` between `2 φ(B) log X` and `4 log X`, *not* by any property of `log X`; the older
`count_lower_bound` spent `2/log 2 > 2` instead because its height was `2^(4k⁴)`.

`exists_candidate_indices_every_height` then packages §1 + §3: at every large chosen `X`,
for every modulus `B` in the small-pool range coprime to the excised conductor and every
reduced residue `u < B`, at least `M / (4 log X)` indices `m < M` give a prime `u + mB ≤ X`.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-- **The candidate-count reduction, at any height.**  `M / (4 log X) ≤ N` whenever
`X / (2 φ(B) log X) ≤ N`, `1 ≤ B ≤ X` and `2 ≤ X`, with `M = ⌊X/B⌋ + 1`. -/
theorem candidate_count_ge {B X : ℕ} {N : ℝ} (hB : 1 ≤ B) (hBX : B ≤ X) (hX2 : 2 ≤ X)
    (hN : (X : ℝ) / (2 * (B.totient : ℝ) * Real.log (X : ℝ)) ≤ N) :
    ((X / B + 1 : ℕ) : ℝ) / (4 * Real.log (X : ℝ)) ≤ N := by
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hXR : (0 : ℝ) < (X : ℝ) := by
    have h : 0 < X := by omega
    exact_mod_cast h
  have hlog : 0 < Real.log (X : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    linarith
  have hφ0 : (0 : ℝ) < (B.totient : ℝ) := by
    have h : 0 < B.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hφB : (B.totient : ℝ) ≤ (B : ℝ) := by exact_mod_cast Nat.totient_le B
  -- `M ≤ 2 X / B`
  have hdiv1 : (1 : ℕ) ≤ X / B := Nat.one_le_div_iff (by omega) |>.mpr hBX
  have hMle : ((X / B + 1 : ℕ) : ℝ) ≤ 2 * ((X : ℝ) / (B : ℝ)) := by
    have h1 : ((X / B : ℕ) : ℝ) ≤ (X : ℝ) / (B : ℝ) := Nat.cast_div_le
    have h2 : (1 : ℝ) ≤ ((X / B : ℕ) : ℝ) := by exact_mod_cast hdiv1
    push_cast
    linarith
  calc ((X / B + 1 : ℕ) : ℝ) / (4 * Real.log (X : ℝ))
      ≤ (2 * ((X : ℝ) / (B : ℝ))) / (4 * Real.log (X : ℝ)) := by
        exact div_le_div_of_nonneg_right hMle (by positivity) |>.trans_eq rfl
    _ = (X : ℝ) / (2 * (B : ℝ) * Real.log (X : ℝ)) := by field_simp; ring
    _ ≤ (X : ℝ) / (2 * (B.totient : ℝ) * Real.log (X : ℝ)) := by
        refine div_le_div_of_nonneg_left hXR.le (by positivity) ?_
        have := mul_le_mul_of_nonneg_left hφB (show (0:ℝ) ≤ 2 by norm_num)
        exact mul_le_mul_of_nonneg_right this hlog.le
    _ ≤ N := hN

/-- **§1 + §3 at every chosen height.**  With `k = countK X` and any modulus `B` in the
small-pool range `B ≤ (2k³)^(1 + c k²)` coprime to the single excised conductor, and any
reduced residue `u < B`, the number of indices `m < M = ⌊X/B⌋ + 1` with `u + mB` a prime
`≤ X` is at least `M / (4 log X)`. -/
theorem exists_candidate_indices_every_height (c : ℕ) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → ∃ P : ℕ, (P = 1 ∨ P.Prime) ∧
      ∀ B u : ℕ, 1 ≤ B → B ≤ (2 * (countK X) ^ 3) ^ (1 + c * (countK X) ^ 2) →
        u < B → Nat.Coprime u B → Nat.Coprime B P →
        ((X / B + 1 : ℕ) : ℝ) / (4 * Real.log (X : ℝ))
          ≤ (((range (X / B + 1)).filter
              (fun m => (u + m * B).Prime ∧ u + m * B ≤ X)).card : ℝ) := by
  classical
  obtain ⟨η, C, hη, hC, X1, hsupply⟩ := exists_prime_supply_every_height
  obtain ⟨X2, hsched⟩ := eventually_atTop.1 (eventually_schedule_feasible c hC hη)
  refine ⟨max (max X1 X2) 2, fun X hX => ?_⟩
  have hX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨P, hPprime, hPbound⟩ := hsupply X hX1
  refine ⟨P, hPprime, fun B u hB1 hBle huB hcopuB hcopBP => ?_⟩
  obtain ⟨hcube, herr⟩ := hsched X hX2' B hB1 hBle
  have hprimes := hPbound B u hB1 hcube hcopuB hcopBP herr
  -- `B ≤ X` from `B³ ≤ X` and `B ≥ 1`
  have hBX : B ≤ X := by
    have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
    have hcu : (B : ℝ) ≤ (B : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (B:ℝ) by linarith)
        (sub_nonneg.mpr hBR)) (show (0:ℝ) ≤ (B:ℝ) + 1 by linarith)]
    have : (B : ℝ) ≤ (X : ℝ) := le_trans hcu hcube
    exact_mod_cast this
  refine candidate_count_ge hB1 hBX hX2 (le_trans hprimes ?_)
  have := card_agp_le_card_candidates (B := B) (u := u) (X := X) hB1 huB
  exact_mod_cast this

end NormalNumbers.JointLambert
