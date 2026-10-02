/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterConjectures
import NormalNumbers.PowerBaseReal
import NormalNumbers.Disjunctive
import NormalNumbers.EquidistTransfer

/-!
# Phase 2: the consequence graph of the master conjectures

Edges out of `BorelConjecture` and `BaileyCrandallHypA` beyond the three planted theorems.
-/

namespace NormalNumbers.MasterConjectures

open NormalNumbers

/-- Borel ⇒ every irrational algebraic real is disjunctive (rich) in every base. -/
theorem borel_isDisjunctive (hB : BorelConjecture) (x : ℝ) (hx : Irrational x)
    (halg : IsAlgebraic ℚ x) (b : ℕ) (hb : 2 ≤ b) : IsDisjunctive b x :=
  (hB x hx halg b hb).isDisjunctive hb

/-- Borel ⇒ `√2` is normal in every base. -/
theorem borel_sqrt_two_all (hB : BorelConjecture) (b : ℕ) (hb : 2 ≤ b) :
    IsNormal b (Real.sqrt 2) :=
  hB _ irrational_sqrt_two isAlgebraic_sqrt_two b hb

/-- Hypothesis A ⇒ `ln 2` normal in every base `2^k`, `k ≥ 1`. -/
theorem hypA_lnTwo_pow (hA : BaileyCrandallHypA) (k : ℕ) (hk : 0 < k) :
    IsNormal (2 ^ k) (Real.log 2) :=
  PowerBase.isNormal_pow (by norm_num) hk (hypA_lnTwo hA)

/-- Hypothesis A + BBP ⇒ `π` normal in every base `16^k`, `k ≥ 1`. -/
theorem hypA_pi_pow (hA : BaileyCrandallHypA) (hπ : PiBBP) (k : ℕ) (hk : 0 < k) :
    IsNormal (16 ^ k) Real.pi :=
  PowerBase.isNormal_pow (by norm_num) hk (hypA_pi_base16 hA hπ)

/-- Hypothesis A + BBP ⇒ every finite binary word occurs in the binary expansion of `π`. -/
theorem hypA_pi_isDisjunctive_two (hA : BaileyCrandallHypA) (hπ : PiBBP) :
    IsDisjunctive 2 Real.pi := by
  rw [isDisjunctive_pow_iff 2 4 le_rfl (by norm_num)]
  exact (hypA_pi_base16 hA hπ).isDisjunctive (by norm_num)

/-- Hypothesis A + BBP ⇒ `π` is disjunctive in every base `2^k`, `k ≥ 1`. -/
theorem hypA_pi_isDisjunctive_two_pow (hA : BaileyCrandallHypA) (hπ : PiBBP) (k : ℕ)
    (hk : 1 ≤ k) : IsDisjunctive (2 ^ k) Real.pi :=
  (isDisjunctive_pow_iff 2 k le_rfl hk _).1 (hypA_pi_isDisjunctive_two hA hπ)

/-- Hypothesis A + BBP ⇒ `π` normal in base 2 (base descent `16 = 2⁴`,
`isNormal_of_isNormal_pow`). -/
theorem hypA_pi_base2 (hA : BaileyCrandallHypA) (hπ : PiBBP) : IsNormal 2 Real.pi :=
  isNormal_of_isNormal_pow (b := 2) (K := 4) le_rfl (by norm_num) (hypA_pi_base16 hA hπ)

/-- Hypothesis A + BBP ⇒ `π` normal in base 4 (`16 = 4²`). -/
theorem hypA_pi_base4 (hA : BaileyCrandallHypA) (hπ : PiBBP) : IsNormal 4 Real.pi :=
  isNormal_of_isNormal_pow (b := 4) (K := 2) (by norm_num) (by norm_num) (hypA_pi_base16 hA hπ)

/-- Hypothesis A + BBP ⇒ `π` normal in every base `2^k`, `k ≥ 1`. -/
theorem hypA_pi_base_two_pow (hA : BaileyCrandallHypA) (hπ : PiBBP) (k : ℕ) (hk : 0 < k) :
    IsNormal (2 ^ k) Real.pi :=
  PowerBase.isNormal_pow (by norm_num) hk (hypA_pi_base2 hA hπ)

end NormalNumbers.MasterConjectures
