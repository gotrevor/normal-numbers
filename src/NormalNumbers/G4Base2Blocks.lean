/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleGrid

/-!
# Sample averages over `[0, 2^x)` from dyadic block bounds

`apSample (2^x) P₀ b₀` splits into the head `n ≤ 2^{x−J₀}` and the blocks `(2^j, 2^{j+1}]`,
`x − J₀ ≤ j < x` (minus the endpoint `2^x`).  If each block, normalized by `P₀/2^j`, is `≤ ε'`,
the sample average is `≤ 2ε' + 2F·2^{−J₀} + 4F·P₀/2^x` for `|f| ≤ F`.
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- Partial sums over `[0, 2^k]` in the progression. -/
def headSum (f : ℕ → ℝ) (P₀ b₀ k : ℕ) : ℝ :=
  ∑ n ∈ (range (2 ^ k + 1)).filter (fun n => n % P₀ = b₀), f n

/-- A dyadic block sum. -/
def blockSum2 (f : ℕ → ℝ) (P₀ b₀ j : ℕ) : ℝ :=
  ∑ n ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter (fun n => n % P₀ = b₀), f n

lemma headSum_succ (f : ℕ → ℝ) (P₀ b₀ k : ℕ) :
    headSum f P₀ b₀ (k + 1) = headSum f P₀ b₀ k + blockSum2 f P₀ b₀ k := by
  unfold headSum blockSum2
  rw [← sum_union]
  · congr 1
    ext n
    simp only [mem_filter, mem_range, mem_union, mem_Ioc]
    have : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : n < 2 ^ k + 1
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h1'⟩, h2⟩) <;> exact ⟨by omega, h2⟩
  · rw [disjoint_left]
    intro n h1 h2
    simp only [mem_filter, mem_range, mem_Ioc] at h1 h2
    omega

lemma headSum_add (f : ℕ → ℝ) (P₀ b₀ k J : ℕ) :
    headSum f P₀ b₀ (k + J) = headSum f P₀ b₀ k + ∑ j ∈ range J, blockSum2 f P₀ b₀ (k + j) := by
  induction J with
  | zero => simp
  | succ J ih => rw [← add_assoc, headSum_succ, ih, sum_range_succ, add_assoc]

lemma sum_apSample_eq (f : ℕ → ℝ) (P₀ b₀ x : ℕ) :
    ∑ n ∈ apSample (2 ^ x) P₀ b₀, f n
      = headSum f P₀ b₀ x - (if 2 ^ x % P₀ = b₀ then f (2 ^ x) else 0) := by
  unfold headSum apSample
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp)]; ring
  · ring

/-- **Sample average from block bounds.** -/
theorem abs_avg_le_blocks (f : ℕ → ℝ) {F ε' : ℝ} (hF : ∀ n, |f n| ≤ F) {P₀ b₀ x J₀ : ℕ}
    (hP₀ : 0 < P₀) (hb : b₀ < P₀) (hJ : J₀ ≤ x) (hPx : 2 * P₀ ≤ 2 ^ x) (hε' : 0 ≤ ε')
    (hblk : ∀ j, x - J₀ ≤ j → j < x → |(P₀ : ℝ) / 2 ^ j * blockSum2 f P₀ b₀ j| ≤ ε') :
    |((apSample (2 ^ x) P₀ b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample (2 ^ x) P₀ b₀, f n|
      ≤ 2 * ε' + 2 * F * (1 / 2) ^ J₀ + 6 * F * P₀ / 2 ^ x := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have hP : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hX : (0 : ℝ) < 2 ^ x := by positivity
  have hPx' : (2 : ℝ) * P₀ ≤ 2 ^ x := by exact_mod_cast hPx
  -- the sum
  have hsplit := sum_apSample_eq f P₀ b₀ x
  have hxk : x = (x - J₀) + J₀ := by omega
  have hhead : |headSum f P₀ b₀ (x - J₀)| ≤ F * ((2 ^ (x - J₀) + 1) / P₀ + 1) := by
    unfold headSum
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun n _ => hF n).trans ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
    have := card_apSample_le (2 ^ (x - J₀) + 1) P₀ b₀ hP₀ hb
    unfold apSample at this
    push_cast at this
    exact mul_le_mul_of_nonneg_left this hF0
  have hblocks : |∑ j ∈ range J₀, blockSum2 f P₀ b₀ (x - J₀ + j)| ≤ ε' * 2 ^ x / P₀ := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j ∈ range J₀, |blockSum2 f P₀ b₀ (x - J₀ + j)| ≤ ε' * 2 ^ (x - J₀ + j) / P₀ := by
      intro j hj
      rw [mem_range] at hj
      have h := hblk (x - J₀ + j) (by omega) (by omega)
      rw [abs_mul, abs_of_pos (by positivity)] at h
      rw [le_div_iff₀ hP]
      have h2 : (0 : ℝ) < 2 ^ (x - J₀ + j) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ h2] at h
      linarith
    refine (sum_le_sum hj).trans ?_
    rw [← sum_div, ← mul_sum]
    gcongr
    have : ∑ j ∈ range J₀, (2 : ℝ) ^ (x - J₀ + j) = 2 ^ (x - J₀) * (2 ^ J₀ - 1) := by
      simp_rw [pow_add, ← mul_sum]
      congr 1
      have := geom_sum_mul (2 : ℝ) J₀
      linarith
    rw [this]
    have h3 : (2 : ℝ) ^ (x - J₀) * 2 ^ J₀ = 2 ^ x := by rw [← pow_add]; congr 1; omega
    have h4 : (0 : ℝ) ≤ 2 ^ (x - J₀) := by positivity
    nlinarith
  have hA : |∑ n ∈ apSample (2 ^ x) P₀ b₀, f n|
      ≤ F * ((2 ^ (x - J₀) + 1) / P₀ + 1) + ε' * 2 ^ x / P₀ + F := by
    rw [hsplit]
    conv_lhs => rw [show headSum f P₀ b₀ x = headSum f P₀ b₀ (x - J₀ + J₀) by rw [← hxk]]
    rw [headSum_add]
    have hend : |(if 2 ^ x % P₀ = b₀ then f (2 ^ x) else 0)| ≤ F := by
      split_ifs
      · exact hF _
      · simpa using hF0
    calc _ ≤ |headSum f P₀ b₀ (x - J₀) + ∑ j ∈ range J₀, blockSum2 f P₀ b₀ (x - J₀ + j)|
          + |(if 2 ^ x % P₀ = b₀ then f (2 ^ x) else 0)| := abs_sub _ _
      _ ≤ |headSum f P₀ b₀ (x - J₀)| + |∑ j ∈ range J₀, blockSum2 f P₀ b₀ (x - J₀ + j)| + F := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by gcongr
  -- the sample size
  have hcard : (2 : ℝ) ^ x / (2 * P₀) ≤ (apSample (2 ^ x) P₀ b₀).card := by
    have h := card_apSample_ge (2 ^ x) P₀ b₀ hP₀ hb
    push_cast at h
    have : (2 : ℝ) ^ x / (2 * P₀) ≤ 2 ^ x / P₀ - 1 := by
      rw [div_le_iff₀ (by positivity)]
      rw [sub_mul, div_mul_eq_mul_div, mul_div_assoc]
      field_simp
      nlinarith
    linarith
  have hc0 : (0 : ℝ) < 2 ^ x / (2 * P₀) := by positivity
  rw [abs_mul, abs_inv, Nat.abs_cast]
  calc ((apSample (2 ^ x) P₀ b₀).card : ℝ)⁻¹ * |∑ n ∈ apSample (2 ^ x) P₀ b₀, f n|
      ≤ ((2 : ℝ) ^ x / (2 * (P₀ : ℝ)))⁻¹ * (F * ((2 ^ (x - J₀) + 1) / P₀ + 1) + ε' * 2 ^ x / P₀ + F) := by
        gcongr
    _ = 2 * ε' + 2 * F * (2 ^ (x - J₀) / 2 ^ x) + 2 * F / 2 ^ x + 4 * F * P₀ / 2 ^ x := by
        field_simp; ring
    _ ≤ 2 * ε' + 2 * F * (1 / 2) ^ J₀ + 6 * F * P₀ / 2 ^ x := by
        have h1 : (2 : ℝ) ^ (x - J₀) / 2 ^ x = (1 / 2) ^ J₀ := by
          rw [show (2 : ℝ) ^ x = 2 ^ (x - J₀) * 2 ^ J₀ by rw [← pow_add]; congr 1]
          rw [one_div_pow]
          field_simp
        have h2 : 2 * F / 2 ^ x ≤ 2 * F * P₀ / 2 ^ x := by
          have : (1 : ℝ) ≤ P₀ := by exact_mod_cast hP₀
          exact div_le_div_of_nonneg_right (by nlinarith) hX.le
        have h3 : 2 * F * P₀ / 2 ^ x + 4 * F * P₀ / 2 ^ x = 6 * F * P₀ / 2 ^ x := by ring
        rw [h1]; linarith

/-- **Pigeonhole for the scale.**  If `J₀·|E| < L`, some `x ∈ [a, a+L)` has no bad scale among
its top `J₀` scales `[x − J₀, x)`. -/
theorem exists_good_x (E : Finset ℕ) (a L J₀ : ℕ) (h : J₀ * E.card < L) :
    ∃ x, a ≤ x ∧ x < a + L ∧ ∀ j, x - J₀ ≤ j → j < x → j ∉ E := by
  classical
  set bad := E.biUnion (fun j => Ioc j (j + J₀)) with hbad
  have hcard : bad.card ≤ J₀ * E.card := by
    refine (card_biUnion_le).trans ?_
    calc ∑ j ∈ E, (Ioc j (j + J₀)).card = ∑ _j ∈ E, J₀ := by
          refine sum_congr rfl fun j _ => ?_
          simp
      _ = J₀ * E.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ J₀ * E.card := le_rfl
  have hlt : bad.card < (Ico a (a + L)).card := by simp; omega
  obtain ⟨x, hx, hxb⟩ := exists_mem_notMem_of_card_lt_card hlt
  rw [mem_Ico] at hx
  refine ⟨x, hx.1, hx.2, fun j hj1 hj2 hjE => hxb ?_⟩
  rw [hbad, mem_biUnion]
  exact ⟨j, hjE, mem_Ioc.2 ⟨hj2, by omega⟩⟩

end NormalNumbers.G4.Base2
