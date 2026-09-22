import NormalNumbers.PrimeModelBlockFamily
import NormalNumbers.PrimeModelBrunCountGraded

/-!
# Lemma B in arithmetic form: the graded Brun lower bound

Lap 4i of `KICKOFF-2026-09-22-multicutoff-lean.md`.  This file joins the two halves:

* the **arithmetic** half, `PrimeModelBrunCountGraded.graded_sifted_count_lower`, which turns any
  weight satisfying (minorisation, `|λ| ≤ 1`, support level `R`) into a lower bound for the
  sifted count with CRT error `R²`;
* the **combinatorial/model** half, `gradedBlock_model_lower` and `gradedBlock_level_le`, which
  supply exactly those three properties for the explicit graded weight `blockLam` on the block
  family `B_{j,l} = U^{(j)} ∩ (y_j^{2^{−(l+1)}}, y_j^{2^{−l}}]`.

The result, `graded_brun_lower`, is **Lemma B as the paper states it** (Fable §3, Astra §4):

    #{n < X : SiftedCondD} ≥ X/(Q ∏_A p) · (1 − 0.3 T) ∏_{p ∈ W} (1 − d_p/p) − R²,

with `T = ∑_j e^{−u_j}` and `log R = ∑_j (128 d_j + 4 u_j + 14) log y_j`.
-/

open Finset

open NormalNumbers.PrimeModel.BrunGraded

namespace NormalNumbers.PrimeModel.BlockSieve

variable {κ : Type*} [DecidableEq κ]

/-- The support level `R = ∏_j y_j^{128 d_j + 4 u_j + 14}`. -/
noncomputable def gradedLevel (t : Finset κ) (d u : κ → ℕ) (y : κ → ℝ) : ℝ :=
  Real.exp (∑ j ∈ t, (128 * (d j : ℝ) + 4 * u j + 14) * Real.log (y j))

theorem one_le_gradedLevel (t : Finset κ) (d u : κ → ℕ) (y : κ → ℝ) (hy : ∀ j, 1 ≤ y j) :
    1 ≤ gradedLevel t d u y := by
  rw [gradedLevel, Real.one_le_exp_iff]
  exact Finset.sum_nonneg fun j _ => by
    have := Real.log_nonneg (hy j)
    positivity

/-- **Lemma B, arithmetic form.** -/
theorem graded_brun_lower
    (t : Finset κ) (L : ℕ) (d u : κ → ℕ) (hd : ∀ j, 1 ≤ d j)
    (U : κ → Finset ℕ) (y : κ → ℝ) (hy : ∀ j, 1 ≤ y j)
    (hU : ∀ j j', j ≠ j' → Disjoint (U j) (U j'))
    (hprime : ∀ j, ∀ p ∈ U j, Nat.Prime p)
    (hcut : ∀ j ∈ t, ∀ l < L, 2 ≤ cut y j (l + 1))
    (hT1 : ∑ j ∈ t, Real.exp (-(u j : ℝ)) ≤ 1)
    (dp jp : ℕ → ℕ) (hdp : ∀ p, 2 * dp p ≤ p)
    (hdpj : ∀ j, ∀ p ∈ U j, dp p ≤ d j)
    (A : Finset ℕ) (Q rr X : ℕ)
    (hA : ∀ p ∈ A, Nat.Prime p) (hAj : ∀ p ∈ A, jp p < p)
    (hAU : Disjoint A ((t ×ˢ Finset.range L).biUnion (gradedBlock U y)))
    (hQ : 0 < Q) (hr : rr < Q)
    (hQcop : ∀ p ∈ A ∪ (t ×ˢ Finset.range L).biUnion (gradedBlock U y), Nat.Coprime Q p) :
    (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
        * ((1 - 0.3 * ∑ j ∈ t, Real.exp (-(u j : ℝ)))
            * ∏ p ∈ (t ×ˢ Finset.range L).biUnion (gradedBlock U y), (1 - (dp p : ℝ) / p))
        - (gradedLevel t d u y) ^ 2
      ≤ (((range X).filter (SiftedCondD A
            ((t ×ˢ Finset.range L).biUnion (gradedBlock U y)) dp jp Q rr)).card : ℝ) := by
  classical
  set s : Finset (κ × ℕ) := t ×ˢ Finset.range L with hs
  set W : Finset ℕ := s.biUnion (gradedBlock U y) with hW
  set g : ℕ → ℝ := fun p => (dp p : ℝ) / p with hg
  set lam : Finset ℕ → ℝ := fun E => ((blockLam s (gradedBlock U y) (gradedDeg d u) E : ℤ) : ℝ)
    with hlamdef
  set R : ℝ := gradedLevel t d u y with hRdef
  have hR1 : 1 ≤ R := one_le_gradedLevel t d u y hy
  have hg0 : ∀ p, 0 ≤ g p := fun p => by rw [hg]; positivity
  have hg1 : ∀ p, g p ≤ 1 / 2 := by
    intro p
    rw [hg]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp [hp]
    · rw [div_le_div_iff₀ (by exact_mod_cast hp) (by norm_num)]
      have := hdp p
      have h := hdp p
      have : (dp p : ℝ) * 2 ≤ 1 * p := by
        push_cast
        exact_mod_cast (by omega : dp p * 2 ≤ 1 * p)
      exact this
  -- primality and `d_p ≤ p` on the sieve range
  have hWmem : ∀ p ∈ W, ∃ j ∈ t, p ∈ U j := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 hp
    exact ⟨q.1, (Finset.mem_product.1 hq).1, gradedBlock_subset U y q hpq⟩
  have hUprop : ∀ p ∈ W, Nat.Prime p ∧ dp p ≤ p := by
    intro p hp
    obtain ⟨j, _, hpj⟩ := hWmem p hp
    exact ⟨hprime j p hpj, by have := hdp p; omega⟩
  -- the weight interface
  have hminor : ∀ B ⊆ W, ∑ E ∈ B.powerset, lam E ≤ if B = ∅ then 1 else 0 := by
    intro B hB
    have hZ := blockLam_minorant s (gradedBlock U y) (gradedDeg d u)
      (fun q _ q' _ hne => gradedBlock_disjoint U y hy hU q q' hne)
      (fun q _ => gradedDeg_even d u q) hB
    have hcast : ∑ E ∈ B.powerset, lam E
        = ((∑ E ∈ B.powerset, blockLam s (gradedBlock U y) (gradedDeg d u) E : ℤ) : ℝ) := by
      rw [hlamdef]; push_cast; rfl
    rw [hcast]
    by_cases hBe : B = ∅
    · rw [if_pos hBe]
      rw [if_pos hBe] at hZ
      exact_mod_cast hZ
    · rw [if_neg hBe]
      rw [if_neg hBe] at hZ
      exact_mod_cast hZ
  have hlam : ∀ E ⊆ W, |lam E| ≤ 1 ∧ (lam E ≠ 0 → ((∏ p ∈ E, p : ℕ) : ℝ) ≤ R) := by
    intro E hE
    constructor
    · have := blockLam_abs_le_one s (gradedBlock U y) (gradedDeg d u) E
      rw [hlamdef]
      rw [← Int.cast_abs]
      exact_mod_cast this
    · intro hne
      have hne' : blockLam s (gradedBlock U y) (gradedDeg d u) E ≠ 0 := by
        intro h
        apply hne
        simp only [hlamdef, h, Int.cast_zero]
      exact gradedBlock_level_le t L d u U y hy hU hE hne'
  -- the model lower bound for the signed sum
  have hmodel : (1 - 0.3 * ∑ j ∈ t, Real.exp (-(u j : ℝ))) * ∏ p ∈ W, (1 - g p)
      ≤ ∑ E ∈ W.powerset, lam E * ∏ p ∈ E, g p :=
    gradedBlock_model_lower t L d u hd U y hy hU hprime g hg0 hg1
      (fun j p hpj => by
        simp only [hg]
        rcases Nat.eq_zero_or_pos p with hp | hp
        · simp [hp]
        · have h1 : (dp p : ℝ) ≤ (d j : ℝ) := by exact_mod_cast hdpj j p hpj
          have h2 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
          gcongr)
      hcut hT1
  have hcount := BrunGraded.graded_sifted_count_lower lam A W dp jp Q rr X hR1 hA hAj hUprop hAU hQ hr
    hQcop hminor hlam
  have hXQ : (0:ℝ) ≤ (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) := by positivity
  refine le_trans ?_ hcount
  have := mul_le_mul_of_nonneg_left hmodel hXQ
  simpa [hg] using sub_le_sub_right this (R ^ 2)

end NormalNumbers.PrimeModel.BlockSieve
