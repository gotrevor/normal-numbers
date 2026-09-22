import Mathlib

/-!
# Lemma B, part 1: the block-Bonferroni pair and the telescoping minorant

Lap 1 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §3
(Astra §4).  This file is **pure combinatorics**: no primes, no arithmetic.

* `bonfPartial b r = ∑_{i ≤ r} (−1)^i C(b,i)`; the Bonferroni pair identity
  `bonfPartial (b+1) r = (−1)^r C(b, r)` (`bonfPartial_succ`), whence for even `r`
  - `bonfIndic b ≤ bonfPartial b r` (`U ≥ I`), and
  - `bonfPartial b r − C(b, r+1) ≤ bonfIndic b` (`U − D ≤ I`),
  where `bonfIndic b = [b = 0]`.
* `prod_sub_prod_le` — the telescoping minorant
  `∏ U − ∏ I ≤ ∑_i (U i − I i) ∏_{j ≠ i} U j`, valid for `0 ≤ I ≤ U`.  This is the step that
  replaces the (invalid) "product of lower sieves": multiplying two lower minorants can produce
  `(−1)(−1) = +1 > [B = ∅]`.
* `prod_le_prod_of_defect` — the packaged form `∏ U − ∑_i D i ∏_{j≠i} U j ≤ ∏ I`.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

/-! ### The Bonferroni pair -/

/-- `U_r(b) = ∑_{i ≤ r} (−1)^i C(b,i)`, the `r`-th Bonferroni partial sum. -/
def bonfPartial (b r : ℕ) : ℤ := ∑ i ∈ Finset.range (r + 1), (-1) ^ i * (b.choose i : ℤ)

/-- `I(b) = [b = 0]`, the exact indicator the sieve is minorising. -/
def bonfIndic (b : ℕ) : ℤ := if b = 0 then 1 else 0

@[simp] theorem bonfPartial_zero (r : ℕ) : bonfPartial 0 r = 1 := by
  unfold bonfPartial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hi)]
  · intro h; simp at h

/-- **Bonferroni pair identity**: `∑_{i ≤ r} (−1)^i C(b+1,i) = (−1)^r C(b,r)`. -/
theorem bonfPartial_succ (b r : ℕ) : bonfPartial (b + 1) r = (-1) ^ r * (b.choose r : ℤ) := by
  induction r with
  | zero => simp [bonfPartial]
  | succ r ih =>
      unfold bonfPartial at ih ⊢
      rw [Finset.sum_range_succ, ih]
      have hp : ((b + 1).choose (r + 1) : ℤ) = (b.choose r : ℤ) + (b.choose (r + 1) : ℤ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      rw [hp]
      ring

/-- `U ≥ I`: the even-order Bonferroni partial sum is an upper bound for the indicator. -/
theorem bonfIndic_le_bonfPartial (b : ℕ) {r : ℕ} (hr : Even r) :
    bonfIndic b ≤ bonfPartial b r := by
  cases b with
  | zero => simp [bonfIndic]
  | succ b =>
      rw [bonfPartial_succ, hr.neg_one_pow, one_mul, bonfIndic, if_neg (by omega)]
      positivity

/-- `0 ≤ I`. -/
@[simp] theorem bonfIndic_nonneg (b : ℕ) : 0 ≤ bonfIndic b := by
  unfold bonfIndic; split <;> norm_num

/-- `U − D ≤ I` with the defect `D = C(b, r+1)`. -/
theorem bonfPartial_sub_le (b : ℕ) {r : ℕ} (hr : Even r) :
    bonfPartial b r - (b.choose (r + 1) : ℤ) ≤ bonfIndic b := by
  cases b with
  | zero => simp [bonfIndic, Nat.choose_eq_zero_of_lt (Nat.succ_pos r)]
  | succ b =>
      rw [bonfPartial_succ, hr.neg_one_pow, one_mul, bonfIndic, if_neg (by omega)]
      have hp : ((b + 1).choose (r + 1) : ℤ) = (b.choose r : ℤ) + (b.choose (r + 1) : ℤ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      rw [hp]
      have : (0:ℤ) ≤ (b.choose (r + 1) : ℤ) := by positivity
      linarith

/-! ### The telescoping minorant -/

variable {ι : Type*} [DecidableEq ι]

/-- **Telescoping**: `∏ U − ∏ I ≤ ∑_i (U i − I i) ∏_{j ≠ i} U j` when `0 ≤ I i ≤ U i`.
This replaces the invalid "product of lower sieves". -/
theorem prod_sub_prod_le (s : Finset ι) (U I : ι → ℝ)
    (hI : ∀ i ∈ s, 0 ≤ I i) (hIU : ∀ i ∈ s, I i ≤ U i) :
    (∏ i ∈ s, U i) - (∏ i ∈ s, I i) ≤ ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hIa : 0 ≤ I a := hI a (mem_insert_self a s)
      have hIUa : I a ≤ U a := hIU a (mem_insert_self a s)
      have hI' : ∀ i ∈ s, 0 ≤ I i := fun i hi => hI i (mem_insert_of_mem hi)
      have hIU' : ∀ i ∈ s, I i ≤ U i := fun i hi => hIU i (mem_insert_of_mem hi)
      have hUnn : ∀ i ∈ s, 0 ≤ U i := fun i hi => (hI' i hi).trans (hIU' i hi)
      have hYnn : 0 ≤ ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j := by
        refine Finset.sum_nonneg fun i hi => ?_
        have h1 : 0 ≤ U i - I i := by linarith [hIU' i hi]
        have h2 : 0 ≤ ∏ j ∈ s.erase i, U j :=
          Finset.prod_nonneg fun j hj => hUnn j (Finset.mem_of_mem_erase hj)
        positivity
      have key := ih hI' hIU'
      -- rewrite both sides over `insert a s`
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have herase_a : (insert a s).erase a = s := Finset.erase_insert ha
      have hterms : ∀ i ∈ s, (U i - I i) * ∏ j ∈ (insert a s).erase i, U j
          = U a * ((U i - I i) * ∏ j ∈ s.erase i, U j) := by
        intro i hi
        have hne : i ≠ a := fun h => ha (h ▸ hi)
        have : (insert a s).erase i = insert a (s.erase i) := by
          ext x
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hx, hx2 | hx2⟩ <;> tauto
          · rintro (rfl | hx) <;> [exact ⟨hne.symm, Or.inl rfl⟩; exact ⟨hx.1, Or.inr hx.2⟩]
        rw [this, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum, herase_a]
      have hsplit : U a * ∏ i ∈ s, U i - I a * ∏ i ∈ s, I i
          = (U a - I a) * ∏ i ∈ s, U i + I a * ((∏ i ∈ s, U i) - ∏ i ∈ s, I i) := by ring
      rw [hsplit]
      have h1 : I a * ((∏ i ∈ s, U i) - ∏ i ∈ s, I i)
          ≤ U a * ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j := by
        calc I a * ((∏ i ∈ s, U i) - ∏ i ∈ s, I i)
            ≤ I a * ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j :=
              mul_le_mul_of_nonneg_left key hIa
          _ ≤ U a * ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j :=
              mul_le_mul_of_nonneg_right hIUa hYnn
      linarith

/-- The packaged minorant: with defects `D i ≥ U i − I i`, `∏ U − ∑ D_i ∏_{j≠i} U_j ≤ ∏ I`. -/
theorem prod_le_prod_of_defect (s : Finset ι) (U I D : ι → ℝ)
    (hI : ∀ i ∈ s, 0 ≤ I i) (hIU : ∀ i ∈ s, I i ≤ U i)
    (hD : ∀ i ∈ s, U i - I i ≤ D i) :
    (∏ i ∈ s, U i) - ∑ i ∈ s, D i * ∏ j ∈ s.erase i, U j ≤ ∏ i ∈ s, I i := by
  classical
  have hUnn : ∀ i ∈ s, 0 ≤ U i := fun i hi => (hI i hi).trans (hIU i hi)
  have hmono : ∑ i ∈ s, (U i - I i) * ∏ j ∈ s.erase i, U j
      ≤ ∑ i ∈ s, D i * ∏ j ∈ s.erase i, U j := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (hD i hi)
      (Finset.prod_nonneg fun j hj => hUnn j (Finset.mem_of_mem_erase hj))
  have := prod_sub_prod_le s U I hI hIU
  linarith

end NormalNumbers.PrimeModel.BlockSieve
