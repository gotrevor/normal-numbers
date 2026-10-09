/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SparseIdentity

/-!
# Carry/merge: short sums of powers of 3 are cyclically sparse

Leaf (iii) of the Baker-free shadow argument `CantorRepetition.repPairArith_of_sparse`: if
`2y ≡ Σ_{j<n} c_j 3^{e_j} (mod 3^A − 1)` with `|c_j| ≤ 2` (exponents arbitrary, repeats allowed),
then `y` is `CycSparse A (2n)`.  Proof: balanced cyclic ternary digits; adding `σ 3ⁱ`
(`σ = ±1`) raises the support by at most one (carry recursion, measure = number of `σ` digits).
-/

open Finset

namespace NormalNumbers.CycMerge

/-- Value of a digit function on `[0, A)`. -/
def val (A : ℕ) (d : ℕ → ℤ) : ℤ := ∑ j ∈ range A, d j * 3 ^ j

/-- Balanced digits. -/
def Bal (d : ℕ → ℤ) : Prop := ∀ j, d j = -1 ∨ d j = 0 ∨ d j = 1

/-- Support size on `[0, A)`. -/
def supp (A : ℕ) (d : ℕ → ℤ) : ℕ := ((range A).filter fun j => d j ≠ 0).card

theorem val_update (A : ℕ) (d : ℕ → ℤ) {i : ℕ} (hi : i < A) (v : ℤ) :
    val A (Function.update d i v) = val A d + (v - d i) * 3 ^ i := by
  unfold val
  rw [← Finset.add_sum_erase _ _ (mem_range.2 hi), ← Finset.add_sum_erase _ _ (mem_range.2 hi)]
  have : ∑ j ∈ (range A).erase i, Function.update d i v j * 3 ^ j =
      ∑ j ∈ (range A).erase i, d j * 3 ^ j :=
    sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this, Function.update_self]; ring

theorem supp_update_le (A : ℕ) (d : ℕ → ℤ) (i : ℕ) (v : ℤ) :
    supp A (Function.update d i v) ≤ supp A d + 1 := by
  unfold supp
  calc _ ≤ (insert i ((range A).filter fun j => d j ≠ 0)).card := by
        refine card_le_card fun j hj => ?_
        rw [mem_filter] at hj
        by_cases h : j = i
        · exact mem_insert.2 (Or.inl h)
        · refine mem_insert_of_mem (mem_filter.2 ⟨hj.1, ?_⟩)
          rw [Function.update_of_ne h] at hj; exact hj.2
    _ ≤ _ := card_insert_le _ _

theorem supp_update_eq (A : ℕ) (d : ℕ → ℤ) (i : ℕ) (v : ℤ) (hv : v ≠ 0) (hd : d i ≠ 0) :
    supp A (Function.update d i v) = supp A d := by
  unfold supp
  congr 1
  ext j
  simp only [mem_filter]
  by_cases h : j = i
  · subst h; simp [hv, hd]
  · rw [Function.update_of_ne h]

/-- **Carry step.**  Adding `σ 3ⁱ` (`σ = ±1`, `i < A`) to a balanced digit function costs at most
one more nonzero digit, modulo `3^A − 1`. -/
theorem carry (A : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) : ∀ m : ℕ, ∀ (d : ℕ → ℤ) (i : ℕ),
    Bal d → ((range A).filter fun j => d j = σ).card = m → i < A →
    ∃ d', Bal d' ∧ supp A d' ≤ supp A d + 1 ∧
      val A d' ≡ val A d + σ * 3 ^ i [ZMOD (3 ^ A - 1)] := by
  intro m
  induction m with
  | zero =>
    intro d i hd hm hi
    have hdi : d i ≠ σ := by
      intro h
      have : i ∈ (range A).filter fun j => d j = σ := mem_filter.2 ⟨mem_range.2 hi, h⟩
      rw [card_eq_zero.1 hm] at this; simp at this
    refine ⟨Function.update d i (d i + σ), ?_, supp_update_le _ _ _ _, ?_⟩
    · intro j
      by_cases h : j = i
      · subst h; rw [Function.update_self]; rcases hd j with h1 | h1 | h1 <;> omega
      · rw [Function.update_of_ne h]; exact hd j
    · rw [val_update A d hi, show d i + σ - d i = σ by ring]
  | succ m ih =>
    intro d i hd hm hi
    by_cases hdi : d i = σ
    · set d1 := Function.update d i (-σ)
      have hd1 : Bal d1 := by
        intro j
        by_cases h : j = i
        · subst h; simp only [d1, Function.update_self]; omega
        · simp only [d1]; rw [Function.update_of_ne h]; exact hd j
      have hm1 : ((range A).filter fun j => d1 j = σ).card = m := by
        have : (range A).filter (fun j => d1 j = σ) = ((range A).filter fun j => d j = σ).erase i := by
          ext j
          simp only [mem_filter, mem_erase, d1]
          by_cases h : j = i
          · subst h; simp only [Function.update_self]; constructor
            · rintro ⟨-, h⟩; omega
            · rintro ⟨h, -⟩; exact absurd rfl h
          · rw [Function.update_of_ne h]; tauto
        rw [this, card_erase_of_mem (mem_filter.2 ⟨mem_range.2 hi, hdi⟩), hm]; rfl
      set i' := if i + 1 < A then i + 1 else 0
      have hi' : i' < A := by simp only [i']; split_ifs <;> (try omega)
      obtain ⟨d', hd', hs, hv⟩ := ih d1 i' hd1 hm1 hi'
      refine ⟨d', hd', ?_, ?_⟩
      · have : supp A d1 = supp A d := supp_update_eq A d i (-σ) (by omega) (by omega)
        omega
      · have h3 : (3 : ℤ) ^ i' ≡ 3 ^ (i + 1) [ZMOD (3 ^ A - 1)] := by
          simp only [i']; split_ifs with h
          · rfl
          · have : i + 1 = A := by omega
            rw [this, pow_zero, Int.modEq_iff_dvd]
        have hval1 : val A d1 = val A d + (-σ - σ) * 3 ^ i := by
          rw [val_update A d hi, hdi]
        refine hv.trans ?_
        rw [hval1]
        calc val A d + (-σ - σ) * 3 ^ i + σ * 3 ^ i'
            ≡ val A d + (-σ - σ) * 3 ^ i + σ * 3 ^ (i + 1) [ZMOD (3 ^ A - 1)] :=
              Int.ModEq.add_left _ (Int.ModEq.mul_left _ h3)
          _ = val A d + σ * 3 ^ i := by ring
    · refine ⟨Function.update d i (d i + σ), ?_, supp_update_le _ _ _ _, ?_⟩
      · intro j
        by_cases h : j = i
        · subst h; rw [Function.update_self]; rcases hd j with h1 | h1 | h1 <;> omega
        · rw [Function.update_of_ne h]; exact hd j
      · rw [val_update A d hi, show d i + σ - d i = σ by ring]

/-- Adding `σ 3ᵉ` for arbitrary `e` (reduced mod `A`). -/
theorem add_pow (A : ℕ) (hA : 1 ≤ A) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (d : ℕ → ℤ) (e : ℕ)
    (hd : Bal d) : ∃ d', Bal d' ∧ supp A d' ≤ supp A d + 1 ∧
      val A d' ≡ val A d + σ * 3 ^ e [ZMOD (3 ^ A - 1)] := by
  obtain ⟨d', h1, h2, h3⟩ := carry A σ hσ _ d (e % A) hd rfl (Nat.mod_lt _ (by omega))
  refine ⟨d', h1, h2, h3.trans (Int.ModEq.add_left _ (Int.ModEq.mul_left _ ?_))⟩
  have h : (3 : ℤ) ^ A ≡ 1 [ZMOD (3 ^ A - 1)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  conv_rhs => rw [← Nat.mod_add_div e A, pow_add, pow_mul]
  calc (3 : ℤ) ^ (e % A) = 3 ^ (e % A) * 1 ^ (e / A) := by simp
    _ ≡ 3 ^ (e % A) * (3 ^ A) ^ (e / A) [ZMOD (3 ^ A - 1)] :=
      Int.ModEq.mul_left _ (Int.ModEq.pow _ h.symm)

/-- Adding `c 3ᵉ`, `|c| ≤ 2`, costs at most two digits. -/
theorem add_term (A : ℕ) (hA : 1 ≤ A) (c : ℤ) (hc : |c| ≤ 2) (d : ℕ → ℤ) (e : ℕ)
    (hd : Bal d) : ∃ d', Bal d' ∧ supp A d' ≤ supp A d + 2 ∧
      val A d' ≡ val A d + c * 3 ^ e [ZMOD (3 ^ A - 1)] := by
  rw [abs_le] at hc
  have hcases : c = 0 ∨ c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨d, hd, by omega, by simp⟩
  · obtain ⟨d', h1, h2, h3⟩ := add_pow A hA 1 (Or.inl rfl) d e hd
    exact ⟨d', h1, by omega, h3⟩
  · obtain ⟨d', h1, h2, h3⟩ := add_pow A hA (-1) (Or.inr rfl) d e hd
    exact ⟨d', h1, by omega, h3⟩
  · obtain ⟨d1, h1, h2, h3⟩ := add_pow A hA 1 (Or.inl rfl) d e hd
    obtain ⟨d2, h4, h5, h6⟩ := add_pow A hA 1 (Or.inl rfl) d1 e h1
    refine ⟨d2, h4, by omega, h6.trans ?_⟩
    calc val A d1 + 1 * 3 ^ e ≡ val A d + 1 * 3 ^ e + 1 * 3 ^ e [ZMOD (3 ^ A - 1)] :=
          Int.ModEq.add_right _ h3
      _ = val A d + 2 * 3 ^ e := by ring
  · obtain ⟨d1, h1, h2, h3⟩ := add_pow A hA (-1) (Or.inr rfl) d e hd
    obtain ⟨d2, h4, h5, h6⟩ := add_pow A hA (-1) (Or.inr rfl) d1 e h1
    refine ⟨d2, h4, by omega, h6.trans ?_⟩
    calc val A d1 + -1 * 3 ^ e ≡ val A d + -1 * 3 ^ e + -1 * 3 ^ e [ZMOD (3 ^ A - 1)] :=
          Int.ModEq.add_right _ h3
      _ = val A d + -2 * 3 ^ e := by ring

/-- **Carry/merge lemma (proved).**  If `2y ≡ Σ_{j<n} c_j 3^{e_j} (mod 3^A − 1)` with
`|c_j| ≤ 2` (arbitrary exponents, repeats allowed), then `y` is cyclically `2n`-sparse. -/
theorem cycSparse_of_sum (A : ℕ) (hA : 1 ≤ A) (n : ℕ) (c : ℕ → ℤ) (e : ℕ → ℕ)
    (hc : ∀ j < n, |c j| ≤ 2) (y : ℤ)
    (hy : 2 * y ≡ ∑ j ∈ range n, c j * 3 ^ e j [ZMOD (3 ^ A - 1)]) :
    SparseIdentity.CycSparse A (2 * n) y := by
  have key : ∀ n' ≤ n, ∃ d, Bal d ∧ supp A d ≤ 2 * n' ∧
      val A d ≡ ∑ j ∈ range n', c j * 3 ^ e j [ZMOD (3 ^ A - 1)] := by
    intro n'
    induction n' with
    | zero =>
      intro _
      exact ⟨fun _ => 0, fun _ => Or.inr (Or.inl rfl), by simp [supp], by simp [val]⟩
    | succ k ih =>
      intro hk
      obtain ⟨d, hd, hs, hv⟩ := ih (by omega)
      obtain ⟨d', hd', hs', hv'⟩ := add_term A hA (c k) (hc k (by omega)) d (e k) hd
      refine ⟨d', hd', by omega, hv'.trans ?_⟩
      rw [sum_range_succ]; exact Int.ModEq.add_right _ hv
  obtain ⟨d, hd, hs, hv⟩ := key n le_rfl
  refine ⟨(range A).filter fun j => d j ≠ 0, d, filter_subset _ _, hs, ?_, ?_⟩
  · intro j hj
    have := (mem_filter.1 hj).2
    refine ⟨this, ?_⟩
    rcases hd j with h | h | h <;> rw [h] <;> norm_num
  · refine hy.trans (hv.symm.trans ?_)
    unfold val
    rw [sum_filter]
    have : ∑ j ∈ range A, (if d j ≠ 0 then d j * 3 ^ j else 0) = ∑ j ∈ range A, d j * 3 ^ j := by
      refine sum_congr rfl fun j _ => ?_
      split_ifs with h
      · rfl
      · push Not at h; rw [h, zero_mul]
    rw [this]

/-- A balanced digit function gives a cyclic sparse representation. -/
theorem cycSparse_of_bal (A K : ℕ) (d : ℕ → ℤ) (hd : Bal d) (hs : supp A d ≤ K) (y : ℤ)
    (hy : 2 * y ≡ val A d [ZMOD (3 ^ A - 1)]) : SparseIdentity.CycSparse A K y := by
  refine ⟨(range A).filter fun j => d j ≠ 0, d, filter_subset _ _, hs, ?_, ?_⟩
  · intro j hj
    refine ⟨(mem_filter.1 hj).2, ?_⟩
    rcases hd j with h | h | h <;> rw [h] <;> norm_num
  · refine hy.trans ?_
    unfold val
    rw [sum_filter]
    have : ∑ j ∈ range A, (if d j ≠ 0 then d j * 3 ^ j else 0) = ∑ j ∈ range A, d j * 3 ^ j := by
      refine sum_congr rfl fun j _ => ?_
      split_ifs with h
      · rfl
      · push Not at h; rw [h, zero_mul]
    rw [this]

/-- Finset-indexed sums of `≤ 2`-coefficient terms have a balanced representation. -/
theorem exists_bal_finsum {ι : Type*} [DecidableEq ι] (A : ℕ) (hA : 1 ≤ A) (T : Finset ι)
    (c : ι → ℤ) (e : ι → ℕ) (hc : ∀ j ∈ T, |c j| ≤ 2) :
    ∃ d, Bal d ∧ supp A d ≤ 2 * T.card ∧
      val A d ≡ ∑ j ∈ T, c j * 3 ^ e j [ZMOD (3 ^ A - 1)] := by
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ => Or.inr (Or.inl rfl), by simp [supp], by simp [val]⟩
  | insert a T ha ih =>
    obtain ⟨d, hd, hs, hv⟩ := ih fun j hj => hc j (mem_insert_of_mem hj)
    obtain ⟨d', hd', hs', hv'⟩ := add_term A hA (c a) (hc a (mem_insert_self _ _)) d (e a) hd
    refine ⟨d', hd', by rw [card_insert_of_notMem ha]; omega, hv'.trans ?_⟩
    rw [sum_insert ha, add_comm]; exact Int.ModEq.add_left _ hv

/-- **Sum of a cyclic-sparse and a sparse number (proved).**  `CycSparse A K₁ y₁` and
`IsSparse3 K₂ (2y₂)` give `CycSparse A (2(K₁ + K₂)) (3ʲ y₁ + 3ⁱ y₂)` for any shifts `i, j`. -/
theorem cycSparse_add (A : ℕ) (hA : 1 ≤ A) {K₁ K₂ : ℕ} {y₁ y₂ : ℤ} (i j : ℕ)
    (h₁ : SparseIdentity.CycSparse A K₁ y₁) (h₂ : SparseIdentity.IsSparse3 K₂ (2 * y₂)) :
    SparseIdentity.CycSparse A (2 * (K₁ + K₂)) (3 ^ j * y₁ + 3 ^ i * y₂) := by
  obtain ⟨S₁, c₁, -, hS₁, hc₁, hy₁⟩ := h₁
  obtain ⟨S₂, c₂, hS₂, hc₂, hy₂⟩ := h₂
  obtain ⟨d, hd, hs, hv⟩ := exists_bal_finsum A hA (S₁.disjSum S₂)
    (Sum.elim c₁ c₂) (Sum.elim (· + j) (· + i)) (by
      intro x hx
      rcases x with x | x
      · exact (hc₁ x (mem_disjSum.1 hx |>.elim (fun ⟨a, ha, h⟩ => by
          cases h; exact ha) (fun ⟨_, _, h⟩ => by cases h))).2
      · exact (hc₂ x (mem_disjSum.1 hx |>.elim (fun ⟨_, _, h⟩ => by cases h)
          (fun ⟨a, ha, h⟩ => by cases h; exact ha))).2)
  refine cycSparse_of_bal A _ d hd (hs.trans (by rw [card_disjSum]; omega)) _ ?_
  refine Int.ModEq.symm (hv.trans ?_)
  rw [sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, pow_add]
  have e1 : ∑ x ∈ S₁, c₁ x * (3 ^ x * 3 ^ j) = 3 ^ j * ∑ x ∈ S₁, c₁ x * 3 ^ x := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x ∈ S₂, c₂ x * (3 ^ x * 3 ^ i) = 3 ^ i * ∑ x ∈ S₂, c₂ x * 3 ^ x := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [e1, e2, ← hy₂, mul_add]
  have : 2 * (3 ^ j * y₁) = 3 ^ j * (2 * y₁) := by ring
  rw [this, show 2 * (3 ^ i * y₂) = 3 ^ i * (2 * y₂) by ring]
  exact Int.ModEq.add_right _ (Int.ModEq.mul_left _ hy₁.symm)

end NormalNumbers.CycMerge
