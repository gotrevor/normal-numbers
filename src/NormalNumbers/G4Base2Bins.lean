/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTTThm31
import NormalNumbers.G4SubsetJunk

/-!
# Base-2 very-large primes: bin indicators (N3–N5 objects)

`binInd I n = 1` if no prime of the bin `I` divides `n`, else `0`.  It is completely
multiplicative-on-coprimes, real and bounded, so it is admissible in TT 3.1(i).
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- The bin indicator `g_I(n) = 1[no p ∈ I divides n]`. -/
noncomputable def binInd (I : Finset ℕ) (n : ℕ) : ℂ :=
  if ∃ p ∈ I, p ∣ n then 0 else 1

theorem binInd_mul (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (m n : ℕ) :
    binInd I (m * n) = binInd I m * binInd I n := by
  classical
  unfold binInd
  by_cases hm : ∃ p ∈ I, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := hm
    rw [if_pos ⟨p, hp, hpm.mul_right n⟩, if_pos ⟨p, hp, hpm⟩, zero_mul]
  · by_cases hn : ∃ p ∈ I, p ∣ n
    · obtain ⟨p, hp, hpn⟩ := hn
      rw [if_pos ⟨p, hp, hpn.mul_left m⟩, if_neg hm, if_pos ⟨p, hp, hpn⟩, mul_zero]
    · rw [if_neg, if_neg hm, if_neg hn, one_mul]
      rintro ⟨p, hp, hpmn⟩
      rcases (Nat.Prime.dvd_mul (hI p hp)).1 hpmn with h | h
      · exact hm ⟨p, hp, h⟩
      · exact hn ⟨p, hp, h⟩

theorem binInd_isCoprimeMultiplicative (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) :
    CastingOut.IsCoprimeMultiplicativeNat (binInd I) := by
  refine ⟨?_, fun m n _ _ _ => binInd_mul I hI m n⟩
  unfold binInd
  rw [if_neg]
  rintro ⟨p, hp, h1⟩
  exact (hI p hp).one_lt.ne' (Nat.dvd_one.1 h1)

theorem norm_binInd_le (I : Finset ℕ) (n : ℕ) : ‖binInd I n‖ ≤ 1 := by
  unfold binInd; split_ifs <;> simp

theorem binInd_im (I : Finset ℕ) (n : ℕ) : (binInd I n).im = 0 := by
  unfold binInd; split_ifs <;> simp

/-- The number of primes of `I` dividing `m`. -/
def binCount (I : Finset ℕ) (m : ℕ) : ℕ := (I.filter (· ∣ m)).card

variable (S : ℕ → Prop) [DecidablePred S]

/-- The very-large `S`-primes up to `M`. -/
def vlPrimes (Y P₀ M : ℕ) : Finset ℕ :=
  (range (M + 1)).filter (fun p => p.Prime ∧ S p ∧ ¬ p ∣ P₀ ∧ Y < p)

theorem omegaVLS_eq_card {Y P₀ M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    omegaVLS S Y P₀ m = binCount (vlPrimes S Y P₀ M) m := by
  unfold omegaVLS binCount vlPrimes
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primeFactors, mem_range]
  constructor
  · rintro ⟨⟨hp, hpm, -⟩, hS, hP, hY⟩
    exact ⟨⟨by have := Nat.le_of_dvd hm hpm; omega, hp, hS, hP, hY⟩, hpm⟩
  · rintro ⟨⟨-, hp, hS, hP, hY⟩, hpm⟩
    exact ⟨⟨hp, hpm, hm.ne'⟩, hS, hP, hY⟩

/-- **N4, pointwise.**  For a partition of the very-large primes into bins,
`ω_{S,>Y}(m) = Σ_ℓ binCount_ℓ(m)`. -/
theorem omegaVLS_eq_sum_bins {Y P₀ M m B : ℕ} (hm : 0 < m) (hmM : m ≤ M)
    (bins : Fin B → Finset ℕ) (hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ'))
    (hcover : univ.biUnion bins = vlPrimes S Y P₀ M) :
    omegaVLS S Y P₀ m = ∑ ℓ, binCount (bins ℓ) m := by
  rw [omegaVLS_eq_card S hm hmM, ← hcover]
  unfold binCount
  rw [filter_biUnion, card_biUnion]
  intro ℓ _ ℓ' _ h
  exact disjoint_filter_filter (hdisj ℓ ℓ' h)

/-- `1 − g_I(m)` as a real number: `1[some p ∈ I divides m]`. -/
theorem one_sub_binInd_re (I : Finset ℕ) (m : ℕ) :
    (1 - binInd I m).re = if binCount I m = 0 then 0 else 1 := by
  classical
  unfold binInd binCount
  by_cases h : ∃ p ∈ I, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := h
    rw [if_pos ⟨p, hp, hpm⟩, if_neg]
    · simp
    · rw [card_eq_zero, filter_eq_empty_iff]; exact fun hh => hh hp hpm
  · rw [if_neg h, if_pos]
    · simp
    · rw [card_eq_zero, filter_eq_empty_iff]; exact fun p hp hpm => h ⟨p, hp, hpm⟩

end NormalNumbers.G4.Base2
