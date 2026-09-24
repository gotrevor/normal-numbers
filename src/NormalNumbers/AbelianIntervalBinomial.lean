/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianBlockDensity

/-!
# Windows over a block substitution whose in-block intervals are Binomial

Fix a digit substitution `g : ℕ → ℕ` on hex digits, read four bits per digit.  Suppose that for
every contiguous interval inside a single block the one-count of `g d`, as `d` runs over the 16
hex digits, is `2^(4-m) · choose m i` — i.e. Binomial(`m`, 1/2).  Then the one-count of *every*
window, at every offset, over a uniformly random hex word, is Binomial: the blocks are
independent, and Binomials convolve (Vandermonde).

This is the combinatorial core of `AbelianBinaryExample`.
-/

open Finset

namespace NormalNumbers.Abelian

open NormalNumbers NormalNumbers.PowerBase

variable (g : ℕ → ℕ)

/-- Bit `i` of the window at offset `r` in the hex word `v`, read through `g`. -/
def bitW (v : List ℕ) (r i : ℕ) : ℕ := g (v.getD ((r + i) / 4) 0) / 2 ^ (3 - (r + i) % 4) % 2

/-- One-count of the bits `r, …, r+m-1` of the single block `g d`. -/
def ivOnes (d r m : ℕ) : ℕ := ((range m).filter (fun q => g d / 2 ^ (3 - (r + q)) % 2 = 1)).card

/-- One-count of the length-`L` window at offset `r` in the hex word `v`. -/
def onesW (L r : ℕ) (v : List ℕ) : ℕ := ((range L).filter (fun i => bitW g v r i = 1)).card

/-- Number of hex digits whose block contributes `i` ones on the interval `[r, r+m)`. -/
def hexCnt (r m i : ℕ) : ℕ := ((range 16).filter (fun t => ivOnes g t r m = i)).card

lemma ivOnes_le (d r m : ℕ) : ivOnes g d r m ≤ m := by
  simpa [ivOnes] using Finset.card_filter_le (range m) _

/-! ### Splitting the sum over hex words by the leading digit -/

lemma sum_split (S : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (16 ^ (S + 1)), f k
      = ∑ t ∈ range 16, ∑ k ∈ range (16 ^ S), f (t * 16 ^ S + k) := by
  classical
  set M := 16 ^ S with hM
  have hM0 : 0 < M := by positivity
  have hstep : ∑ k ∈ range (16 ^ (S + 1)), f k
      = ∑ p ∈ (range 16) ×ˢ (range M), f (p.1 * M + p.2) := by
    refine Finset.sum_nbij' (fun k => (k / M, k % M)) (fun p => p.1 * M + p.2) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_range, pow_succ] at hk
      have hk16 : k < M * 16 := by rw [hM]; exact hk
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨Nat.div_lt_of_lt_mul hk16, Nat.mod_lt _ hM0⟩
    · intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      have hlt : p.1 * M + p.2 < 16 * M :=
        calc p.1 * M + p.2 < p.1 * M + M := by omega
          _ = (p.1 + 1) * M := by ring
          _ ≤ 16 * M := Nat.mul_le_mul_right M (by omega)
      rw [Finset.mem_range, pow_succ]
      have : (16 : ℕ) * M = 16 ^ S * 16 := by rw [hM]; ring
      omega
    · intro k _
      simpa using Nat.div_add_mod' k M
    · intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      have h1 : (p.1 * M + p.2) / M = p.1 := by
        rw [mul_comm, Nat.mul_add_div hM0, Nat.div_eq_of_lt hp.2, Nat.add_zero]
      have h2 : (p.1 * M + p.2) % M = p.2 := by
        rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2]
      rw [h1, h2]
    · intro k _
      congr 1
      exact (Nat.div_add_mod' k M).symm
  rw [hstep, Finset.sum_product]


/-! ### Peeling the first block off a window -/

lemma bitW_cons_lt (t : ℕ) (v : List ℕ) (r i : ℕ) (h : r + i < 4) :
    bitW g (t :: v) r i = g t / 2 ^ (3 - (r + i)) % 2 := by
  unfold bitW
  rw [show (r + i) / 4 = 0 by omega, show (r + i) % 4 = r + i by omega]
  rfl

lemma bitW_cons_ge (t : ℕ) (v : List ℕ) (r i : ℕ) (h : 4 ≤ r + i) :
    bitW g (t :: v) r i = bitW g v 0 (r + i - 4) := by
  unfold bitW
  have hq : (r + i) / 4 = (0 + (r + i - 4)) / 4 + 1 := by omega
  have hm : (r + i) % 4 = (0 + (r + i - 4)) % 4 := by omega
  rw [hq, hm, List.getD_cons_succ]

lemma onesW_small (L r : ℕ) (hL : r + L ≤ 4) (t : ℕ) (v : List ℕ) :
    onesW g L r (t :: v) = ivOnes g t r L := by
  classical
  unfold onesW ivOnes
  congr 1
  refine Finset.filter_congr (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [bitW_cons_lt g t v r i (by omega)]

lemma onesW_peel (L r : ℕ) (hr : r < 4) (hL : 4 - r ≤ L) (t : ℕ) (v : List ℕ) :
    onesW g L r (t :: v) = ivOnes g t r (4 - r) + onesW g (L - (4 - r)) 0 v := by
  classical
  set m := 4 - r with hm
  have hm1 : 1 ≤ m := by omega
  unfold onesW
  rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le m) hL, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      (Finset.Ico_disjoint_Ico_consecutive 0 m L))]
  congr 1
  · rw [← Finset.range_eq_Ico]
    unfold ivOnes
    congr 1
    refine Finset.filter_congr (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [bitW_cons_lt g t v r i (by omega)]
  · refine Finset.card_nbij' (fun i => i - m) (fun k => k + m) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hi
      obtain ⟨⟨h1, h2⟩, h3⟩ := hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [← h3, bitW_cons_ge g t v r i (by omega)]
      congr 1
      omega
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hk
      obtain ⟨h1, h2⟩ := hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [bitW_cons_ge g t v r (k + m) (by omega), ← h2]
      congr 1
      omega
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hi
      show i - m + m = i
      omega
    · intro k _
      show k + m - m = k
      omega


/-! ### Vandermonde bookkeeping -/

lemma vander (m L' j : ℕ) (hm : m ≤ 4) :
    ∑ i ∈ range 5, (if i ≤ j then m.choose i * L'.choose (j - i) else 0) = (m + L').choose j := by
  classical
  have hT2 : (m + L').choose j = ∑ i ∈ range (j + 1), m.choose i * L'.choose (j - i) := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [hT2]
  rcases Nat.lt_or_ge 5 (j + 1) with h | h
  · have e1 : ∑ i ∈ range 5, (if i ≤ j then m.choose i * L'.choose (j - i) else 0)
        = ∑ i ∈ range 5, m.choose i * L'.choose (j - i) :=
      Finset.sum_congr rfl (fun x hx => if_pos (by simp only [Finset.mem_range] at hx; omega))
    rw [e1]
    refine Finset.sum_subset ((fun x hx => Finset.mem_range.mpr (by simp only [Finset.mem_range] at hx; omega)))
      (fun x hx hnx => ?_)
    simp only [Finset.mem_range] at hx hnx
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  · refine Eq.symm ?_
    have e1 : ∑ i ∈ range (j + 1), m.choose i * L'.choose (j - i)
        = ∑ i ∈ range (j + 1), (if i ≤ j then m.choose i * L'.choose (j - i) else 0) :=
      Finset.sum_congr rfl (fun x hx => (if_pos (by simp only [Finset.mem_range] at hx; omega)).symm)
    rw [e1]
    refine Finset.sum_subset ((fun x hx => Finset.mem_range.mpr (by simp only [Finset.mem_range] at hx; omega)))
      (fun x hx hnx => ?_)
    simp only [Finset.mem_range] at hx hnx
    exact if_neg (by omega)

/-! ### The interval hypothesis -/

/-- Every contiguous interval inside a block has a Binomial one-count under the `g`-block law. -/
def HBinom : Prop :=
  ∀ r m i, r < 4 → 1 ≤ m → r + m ≤ 4 → i ≤ 4 → hexCnt g r m i = 2 ^ (4 - m) * m.choose i

lemma hexCnt_eq (hyp : HBinom g) (r m i : ℕ) (hr : r < 4) (hm : 1 ≤ m) (hrm : r + m ≤ 4) :
    hexCnt g r m i = 2 ^ (4 - m) * m.choose i := by
  classical
  rcases Nat.lt_or_ge 4 i with h | h
  · have h1 : hexCnt g r m i = 0 := by
      rw [hexCnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _
      have := ivOnes_le g t r m
      omega
    rw [h1, Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  · exact hyp r m i hr hm hrm h

/-! ### The window count over all hex words -/

/-- Number of length-`S` hex words whose length-`L` window at offset `r` carries `j` ones. -/
def wordCount (L r S j : ℕ) : ℕ :=
  ∑ k ∈ range (16 ^ S), if onesW g L r (wordOf 16 S k) = j then 1 else 0

lemma wordCount_zero (r S j : ℕ) : wordCount g 0 r S j = 16 ^ S * (0 : ℕ).choose j := by
  classical
  unfold wordCount
  have h0 : ∀ v : List ℕ, onesW g 0 r v = 0 := by intro v; simp [onesW]
  simp only [h0]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [Finset.sum_congr rfl (fun k _ => if_neg (by omega)), Finset.sum_const_zero,
      Nat.choose_eq_zero_of_lt hj, mul_zero]

/-- The leading-digit recursion for `wordCount`. -/
lemma wordCount_succ (L r S j : ℕ) :
    wordCount g L r (S + 1) j
      = ∑ t ∈ range 16, ∑ k ∈ range (16 ^ S),
          (if onesW g L r (t :: wordOf 16 S k) = j then 1 else 0) := by
  classical
  unfold wordCount
  rw [sum_split S (fun k => if onesW g L r (wordOf 16 (S + 1) k) = j then 1 else 0)]
  refine Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun k hk => ?_))
  rw [wordOf_cons 16 S k t (by norm_num) (Finset.mem_range.mp hk) (Finset.mem_range.mp ht)]


/-! ### The main count -/

/-- **Binomial windows.**  If every in-block interval is Binomial under the `g`-block law, then
for every offset `r < 4` and every window length `L`, the number of length-`S` hex words whose
window carries `j` ones is `16^S · choose L j / 2^L`. -/
theorem two_pow_mul_wordCount (hyp : HBinom g) :
    ∀ L r S j, r < 4 → r + L ≤ 4 * S → 2 ^ L * wordCount g L r S j = 16 ^ S * L.choose j := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro r S j hr hS
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · rw [pow_zero, one_mul, wordCount_zero]
    obtain ⟨S', rfl⟩ : ∃ S', S = S' + 1 := ⟨S - 1, by omega⟩
    rw [wordCount_succ]
    by_cases hsmall : r + L ≤ 4
    · have hin : ∀ t ∈ range 16, (∑ k ∈ range (16 ^ S'),
          (if onesW g L r (t :: wordOf 16 S' k) = j then 1 else 0))
          = 16 ^ S' * (if ivOnes g t r L = j then 1 else 0) := by
        intro t _
        rw [Finset.sum_congr rfl (fun k _ => by
          rw [onesW_small g L r (by omega) t (wordOf 16 S' k)]),
          Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [Finset.sum_congr rfl hin, ← Finset.mul_sum]
      have hcnt : (∑ t ∈ range 16, (if ivOnes g t r L = j then 1 else 0)) = hexCnt g r L j := by
        rw [hexCnt, Finset.card_filter]
      rw [hcnt, hexCnt_eq g hyp r L j hr hL (by omega)]
      have hpow : (2 : ℕ) ^ L * 2 ^ (4 - L) = 16 := by
        rw [← pow_add, show L + (4 - L) = 4 from by omega]; norm_num
      calc 2 ^ L * (16 ^ S' * (2 ^ (4 - L) * L.choose j))
          = (2 ^ L * 2 ^ (4 - L)) * (16 ^ S' * L.choose j) := by ring
        _ = 16 ^ (S' + 1) * L.choose j := by rw [hpow, pow_succ]; ring
    · set m := 4 - r with hmdef
      set L' := L - m with hL'def
      have hm1 : 1 ≤ m := by omega
      have hm4 : m ≤ 4 := by omega
      have hLm : m + L' = L := by omega
      have hL'lt : L' < L := by omega
      have hL'S : 0 + L' ≤ 4 * S' := by omega
      set F : ℕ → ℕ := fun i => if i ≤ j then wordCount g L' 0 S' (j - i) else 0 with hF
      have hinner : ∀ i : ℕ, (∑ k ∈ range (16 ^ S'),
          (if i + onesW g L' 0 (wordOf 16 S' k) = j then 1 else 0)) = F i := by
        intro i
        rw [hF]
        by_cases hij : i ≤ j
        · simp only [if_pos hij]
          rw [wordCount]
          exact Finset.sum_congr rfl (fun k _ => if_congr (by omega) rfl rfl)
        · simp only [if_neg hij]
          exact Finset.sum_eq_zero (fun k _ => if_neg (by omega))
      have hpeel : ∀ t ∈ range 16, (∑ k ∈ range (16 ^ S'),
          (if onesW g L r (t :: wordOf 16 S' k) = j then 1 else 0)) = F (ivOnes g t r m) := by
        intro t _
        rw [Finset.sum_congr rfl (fun k _ => by
          rw [onesW_peel g L r hr (by omega) t (wordOf 16 S' k)])]
        exact hinner (ivOnes g t r m)
      rw [Finset.sum_congr rfl hpeel]
      have hmaps : ∀ t ∈ range 16, ivOnes g t r m ∈ range 5 := fun t _ =>
        Finset.mem_range.mpr (by have := ivOnes_le g t r m; omega)
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => F (ivOnes g t r m))]
      have hfib : ∀ i ∈ range 5, (∑ t ∈ (range 16).filter (fun t => ivOnes g t r m = i),
          F (ivOnes g t r m)) = hexCnt g r m i * F i := by
        intro i _
        rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]),
          Finset.sum_const, hexCnt, smul_eq_mul]
      rw [Finset.sum_congr rfl hfib, Finset.mul_sum]
      have hterm : ∀ i ∈ range 5, 2 ^ L * (hexCnt g r m i * F i)
          = 16 ^ (S' + 1) * (if i ≤ j then m.choose i * L'.choose (j - i) else 0) := by
        intro i _
        rw [hexCnt_eq g hyp r m i hr hm1 (by omega), hF]
        by_cases hij : i ≤ j
        · simp only [if_pos hij]
          have hIH : 2 ^ L' * wordCount g L' 0 S' (j - i) = 16 ^ S' * L'.choose (j - i) :=
            ih L' hL'lt 0 S' (j - i) (by norm_num) hL'S
          have h2 : (2 : ℕ) ^ L = 2 ^ m * 2 ^ L' := by rw [← pow_add, hLm]
          have h3 : (2 : ℕ) ^ m * 2 ^ (4 - m) = 16 := by
            rw [← pow_add, show m + (4 - m) = 4 from by omega]; norm_num
          calc 2 ^ L * (2 ^ (4 - m) * m.choose i * wordCount g L' 0 S' (j - i))
              = (2 ^ m * 2 ^ (4 - m)) * m.choose i * (2 ^ L' * wordCount g L' 0 S' (j - i)) := by
                rw [h2]; ring
            _ = 16 * m.choose i * (16 ^ S' * L'.choose (j - i)) := by rw [h3, hIH]
            _ = 16 ^ (S' + 1) * (m.choose i * L'.choose (j - i)) := by rw [pow_succ]; ring
        · simp only [if_neg hij, mul_zero]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, vander m L' j hm4, hLm]

end NormalNumbers.Abelian
