import NormalNumbers.AbelianNormal
import NormalNumbers.AbelianBlockDensity
import NormalNumbers.PowerBaseReal

/-!
# A binary sequence that is abelian-normal but not normal

Campbell (arXiv:2603.04396) separates abelian normality from normality in base 10 with a cyclic
swap on digit pairs, which needs three digits.  In base 2 the separation first appears at block
length 4 (`rigid_three`, `separation_four`).  This file realizes it by an infinite sequence.

Take a base-16 normal digit sequence `c`, apply `hexSwap` (2 → 3, 5 → 4, B → A, C → D), and read
each hex digit as four bits.  Every contiguous interval inside a block has a Binomial one-count
under the induced block law, so every window's one-count is Binomial (suffix + whole blocks +
prefix, independent in the limit by base-16 normality of `c`).  But `0011` has limiting frequency
`5/64`.  Design note: `DESIGN-2026-09-23-binary-abelian-nonnormal.md`; exact probe:
`probes/abelian_hex_construction.py`.
-/

open Finset Filter Topology

namespace NormalNumbers.Abelian

open NormalNumbers NormalNumbers.PowerBase

/-- The hex substitution `2 → 3, 5 → 4, B → A, C → D`. -/
def hexSwap (d : ℕ) : ℕ :=
  if d = 2 then 3 else if d = 5 then 4 else if d = 11 then 10 else if d = 12 then 13 else d

/-- Binary reading of the swapped hex digits of `c`: bit `n` is bit `3 - n % 4` (most significant
first) of `hexSwap (c (n / 4))`. -/
def xiBits (c : ℕ → ℕ) (n : ℕ) : ℕ := hexSwap (c (n / 4)) / 2 ^ (3 - n % 4) % 2


/-- Bit `i` of the window at offset `r` inside a hex word `v`, read through `hexSwap`. -/
def bitOfWord (v : List ℕ) (r i : ℕ) : ℕ :=
  hexSwap (v.getD ((r + i) / 4) 0) / 2 ^ (3 - (r + i) % 4) % 2

lemma xiBits_eq_bitOfWord (c : ℕ → ℕ) (S n i : ℕ) (h : (n % 4 + i) / 4 < S) :
    xiBits c (n + i) = bitOfWord (blk c S (n / 4)) (n % 4) i := by
  unfold xiBits bitOfWord
  rw [blk_getD c S (n / 4) _ h]
  have h1 : (n + i) / 4 = n / 4 + (n % 4 + i) / 4 := by omega
  have h2 : (n + i) % 4 = (n % 4 + i) % 4 := by omega
  rw [h1, h2]

/-! ### The nibble law

`hexSwap` is not injective, so the *whole* nibble is not uniform — that is exactly what breaks
normality.  What survives is the statistic that abelian normality reads: for **every**
contiguous interval of bit positions inside a nibble (the full nibble included), the one-count
of `hexSwap d` over that interval, as `d` ranges uniformly over `{0,…,15}`, is
Binomial(`len`, 1/2).  For a proper interval this holds because the four swaps
`2↔3, 5↔4, 11↔10, 12↔13` move each digit only within its own 2-bit quadrant *and* within its
own 2-bit residue class; for the full nibble it holds because the swaps pair up popcounts
`{1,2} ↦ {2,2}`, `{1,2} ↦ {1,1}`, `{2,3} ↦ {2,2}`, `{2,3} ↦ {3,3}`, which preserves the
multiset `{1,1,2,2,2,2,3,3}`. -/

/-- Bit `p` (most significant first) of `hexSwap d`. -/
def swapBit (d p : ℕ) : ℕ := hexSwap d / 2 ^ (3 - p) % 2

lemma bitOfWord_eq_swapBit (v : List ℕ) (r i : ℕ) :
    bitOfWord v r i = swapBit (v.getD ((r + i) / 4) 0) ((r + i) % 4) := rfl

lemma swapBit_le_one (d p : ℕ) : swapBit d p ≤ 1 :=
  Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))

/-- One-count of `hexSwap d` over the bit positions `[lo, hi)`. -/
def nibPc (d lo hi : ℕ) : ℕ := ∑ p ∈ Finset.Ico lo hi, swapBit d p

/-- How many hex digits have one-count `t` over the bit window `[lo, hi)`. -/
def nibCount (lo hi t : ℕ) : ℕ :=
  ((Finset.range 16).filter fun d => nibPc d lo hi = t).card

lemma nibPc_le (d lo hi : ℕ) : nibPc d lo hi ≤ hi - lo := by
  calc nibPc d lo hi ≤ ∑ _p ∈ Finset.Ico lo hi, 1 :=
        Finset.sum_le_sum fun p _ => swapBit_le_one d p
    _ = hi - lo := by simp

/-- **The nibble law.**  Over every contiguous bit window of a nibble, the swapped one-count is
Binomial(`hi - lo`, 1/2).  Checked by `decide` on the 125 relevant `(lo, hi, t)` triples. -/
theorem nibCount_binomial (lo hi t : ℕ) (hlo : lo ≤ 4) (hhi : hi ≤ 4) :
    nibCount lo hi t * 2 ^ (hi - lo) = 16 * (hi - lo).choose t := by
  by_cases ht : t ≤ 4
  · have key : ∀ a < 5, ∀ b < 5, ∀ c < 5,
        nibCount a b c * 2 ^ (b - a) = 16 * (b - a).choose c := by decide
    exact key lo (by omega) hi (by omega) t (by omega)
  · have h0 : nibCount lo hi t = 0 := by
      rw [nibCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro d _
      have := nibPc_le d lo hi
      omega
    have h1 : (hi - lo).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, h1]
    simp

/-! ### The window law over a block of hex digits

A length-`L` bit window starting at bit `r` of a hex word splits into: a contiguous bit
interval of the first nibble, then whole nibbles, then a contiguous prefix of the last.  Each
piece is Binomial by `nibCount_binomial`, the nibbles are independent, and Vandermonde
convolves them into Binomial(`L`, 1/2). -/

/-- One-count of the length-`L` bit window at offset `r` of the hex word `v`. -/
def winPc (r L : ℕ) (v : List ℕ) : ℕ := ∑ i ∈ Finset.range L, bitOfWord v r i

/-- How many `S`-digit hex words give window one-count `j`. -/
def winCountK (r L S j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (16 ^ S), if winPc r L (wordOf 16 S k) = j then 1 else 0

/-- Splitting an indicator of a sum over the antidiagonal. -/
lemma indicator_add_eq (a b j : ℕ) :
    (if a + b = j then (1 : ℕ) else 0)
      = ∑ p ∈ antidiagonal j,
          (if a = p.1 then (1 : ℕ) else 0) * (if b = p.2 then 1 else 0) := by
  have hpt : ∀ p : ℕ × ℕ,
      (if a = p.1 then (1 : ℕ) else 0) * (if b = p.2 then 1 else 0)
        = if (a, b) = p then 1 else 0 := by
    intro p
    by_cases h1 : a = p.1 <;> by_cases h2 : b = p.2 <;>
      simp [Prod.ext_iff, h1, h2]
  rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_ite_eq]
  by_cases h : a + b = j
  · rw [if_pos h, if_pos (mem_antidiagonal.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (mem_antidiagonal.mp hc))]

/-- Reindexing `range (b ^ (S+1))` by leading digit and tail. -/
lemma sum_range_pow_succ_split (b S : ℕ) (hb : 0 < b) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.range (b ^ (S + 1)), f k
      = ∑ t ∈ Finset.range b, ∑ k ∈ Finset.range (b ^ S), f (t * b ^ S + k) := by
  have hbS : 0 < b ^ S := pow_pos hb S
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun k => (k / b ^ S, k % b ^ S))
    (fun p : ℕ × ℕ => p.1 * b ^ S + p.2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range, pow_succ] at hk
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul (by omega), Nat.mod_lt _ hbS⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range, pow_succ]
    calc p.1 * b ^ S + p.2 < p.1 * b ^ S + b ^ S := by omega
      _ = (p.1 + 1) * b ^ S := by ring
      _ ≤ b * b ^ S := Nat.mul_le_mul_right _ hp.1
      _ = b ^ S * b := by ring
  · intro k _
    exact Nat.div_add_mod' k (b ^ S)
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have h1 : (p.1 * b ^ S + p.2) / b ^ S = p.1 := by
      rw [Nat.mul_comm p.1, Nat.mul_add_div hbS, Nat.div_eq_of_lt hp.2, Nat.add_zero]
    have h2 : (p.1 * b ^ S + p.2) % b ^ S = p.2 := by
      rw [Nat.mul_comm p.1, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2]
    rw [Prod.ext_iff]
    exact ⟨h1, h2⟩
  · intro k _
    rw [Nat.div_add_mod' k (b ^ S)]

/-- The cons decomposition of a window one-count. -/
lemma winPc_cons (r L t : ℕ) (w : List ℕ) (hr : r < 4) :
    winPc r L (t :: w) = nibPc t r (r + min L (4 - r)) + winPc 0 (L - min L (4 - r)) w := by
  set m := min L (4 - r) with hm
  have hmL : m ≤ L := min_le_left _ _
  have hm4 : r + m ≤ 4 := by omega
  have hsplit : ∑ i ∈ Finset.range L, bitOfWord (t :: w) r i
      = (∑ i ∈ Finset.range m, bitOfWord (t :: w) r i)
        + ∑ i ∈ Finset.range (L - m), bitOfWord (t :: w) r (m + i) := by
    have := Finset.sum_range_add (f := fun i => bitOfWord (t :: w) r i) m (L - m)
    rw [show m + (L - m) = L from by omega] at this
    exact this
  have hhead : ∑ i ∈ Finset.range m, bitOfWord (t :: w) r i = nibPc t r (r + m) := by
    rw [nibPc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    rw [bitOfWord_eq_swapBit]
    have h1 : (r + i) / 4 = 0 := Nat.div_eq_of_lt (by omega)
    have h2 : (r + i) % 4 = r + i := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    rfl
  have htail : ∑ i ∈ Finset.range (L - m), bitOfWord (t :: w) r (m + i)
      = winPc 0 (L - m) w := by
    rcases Nat.eq_zero_or_pos (L - m) with h0 | h0
    · rw [h0]; simp [winPc]
    have hmeq : m = 4 - r := by omega
    rw [winPc]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [bitOfWord_eq_swapBit, bitOfWord_eq_swapBit]
    have h1 : (r + (m + i)) / 4 = (0 + i) / 4 + 1 := by omega
    have h2 : (r + (m + i)) % 4 = (0 + i) % 4 := by omega
    rw [h1, h2, List.getD_cons_succ]
  rw [winPc, hsplit, hhead, htail]

/-- The convolution step: a sum of an indicator of a sum of two independent statistics. -/
lemma sum_sum_indicator_add (A B : Finset ℕ) (f g : ℕ → ℕ) (j : ℕ) :
    ∑ t ∈ A, ∑ k ∈ B, (if f t + g k = j then (1 : ℕ) else 0)
      = ∑ p ∈ antidiagonal j,
          (∑ t ∈ A, if f t = p.1 then (1 : ℕ) else 0) *
            (∑ k ∈ B, if g k = p.2 then (1 : ℕ) else 0) := by
  have step : ∀ t ∈ A, ∑ k ∈ B, (if f t + g k = j then (1 : ℕ) else 0)
      = ∑ p ∈ antidiagonal j,
          (if f t = p.1 then (1 : ℕ) else 0) * ∑ k ∈ B, (if g k = p.2 then (1 : ℕ) else 0) := by
    intro t _
    rw [Finset.sum_congr rfl fun k (_ : k ∈ B) => indicator_add_eq (f t) (g k) j,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]

/-- **The window law.**  Among the `16^S` hex words of length `S`, the number whose length-`L`
bit window at offset `r` carries `j` ones is `16^S · C(L, j) / 2^L`. -/
theorem winCountK_binomial (S : ℕ) : ∀ r L j : ℕ, r < 4 → r + L ≤ 4 * S →
    winCountK r L S j * 2 ^ L = 16 ^ S * L.choose j := by
  induction S with
  | zero =>
      intro r L j hr hrL
      obtain rfl : L = 0 := by omega
      simp only [winCountK, pow_zero, Finset.sum_range_one, winPc, Finset.range_zero,
        Finset.sum_empty, one_mul]
      cases j with
      | zero => simp
      | succ j => simp
  | succ S ih =>
      intro r L j hr hrL
      set m := min L (4 - r) with hm
      have hmL : m ≤ L := min_le_left _ _
      have hm4 : r + m ≤ 4 := by omega
      have htail : 0 + (L - m) ≤ 4 * S := by
        rcases le_or_gt L (4 - r) with h | h
        · have : m = L := by omega
          omega
        · have : m = 4 - r := by omega
          omega
      -- split off the leading hex digit
      have hsplit : winCountK r L (S + 1) j
          = ∑ t ∈ Finset.range 16, ∑ k ∈ Finset.range (16 ^ S),
              if nibPc t r (r + m) + winPc 0 (L - m) (wordOf 16 S k) = j then 1 else 0 := by
        rw [winCountK, sum_range_pow_succ_split 16 S (by norm_num)]
        refine Finset.sum_congr rfl fun t ht => ?_
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [wordOf_cons 16 S k t (by norm_num) (Finset.mem_range.mp hk) (Finset.mem_range.mp ht),
          winPc_cons r L t _ hr]
      rw [hsplit, sum_sum_indicator_add]
      -- identify the two factors
      have hfac1 : ∀ a : ℕ, (∑ t ∈ Finset.range 16, if nibPc t r (r + m) = a then (1 : ℕ) else 0)
          = nibCount r (r + m) a := by
        intro a; rw [nibCount, Finset.card_filter]
      have hfac2 : ∀ b : ℕ,
          (∑ k ∈ Finset.range (16 ^ S), if winPc 0 (L - m) (wordOf 16 S k) = b then (1 : ℕ) else 0)
            = winCountK 0 (L - m) S b := fun b => rfl
      rw [Finset.sum_congr rfl fun p (_ : p ∈ antidiagonal j) => by
        rw [hfac1 p.1, hfac2 p.2]]
      -- multiply by 2^L and apply the nibble law, the induction hypothesis and Vandermonde
      have hLm : m + (L - m) = L := by omega
      have hpow : (2 : ℕ) ^ L = 2 ^ m * 2 ^ (L - m) := by rw [← pow_add, hLm]
      have hkey : ∀ p ∈ antidiagonal j,
          nibCount r (r + m) p.1 * winCountK 0 (L - m) S p.2 * 2 ^ L
            = 16 ^ (S + 1) * (m.choose p.1 * (L - m).choose p.2) := by
        intro p _
        have h1 : nibCount r (r + m) p.1 * 2 ^ m = 16 * m.choose p.1 := by
          have := nibCount_binomial r (r + m) p.1 (by omega) hm4
          rwa [Nat.add_sub_cancel_left] at this
        have h2 : winCountK 0 (L - m) S p.2 * 2 ^ (L - m) = 16 ^ S * (L - m).choose p.2 :=
          ih 0 (L - m) p.2 (by norm_num) htail
        calc nibCount r (r + m) p.1 * winCountK 0 (L - m) S p.2 * 2 ^ L
            = (nibCount r (r + m) p.1 * 2 ^ m) * (winCountK 0 (L - m) S p.2 * 2 ^ (L - m)) := by
              rw [hpow]; ring
          _ = (16 * m.choose p.1) * (16 ^ S * (L - m).choose p.2) := by rw [h1, h2]
          _ = 16 ^ (S + 1) * (m.choose p.1 * (L - m).choose p.2) := by ring
      rw [Finset.sum_mul, Finset.sum_congr rfl hkey, ← Finset.mul_sum, ← Nat.add_choose_eq, hLm]

/-- The four-bit window predicate for `[0,0,1,1]`, as a function of the offset and the hex pair. -/
def isZZOO (r : ℕ) (v : List ℕ) : Prop :=
  ∀ j < 4, bitOfWord v r j = (wordOf 2 4 3).getD j 0

instance (r : ℕ) (v : List ℕ) : Decidable (isZZOO r v) := Nat.decidableBallLT _ _

/-- The construction is abelian-normal in base two. -/
theorem isAbelianNormalTwo_xiBits (c : ℕ → ℕ) (hc16 : ∀ m, c m < 16)
    (hc : IsNormalSequence 16 c) : IsAbelianNormalTwo (xiBits c) := by
  sorry

/-- The construction is not normal in base two: `0011` has limiting frequency `5/64`. -/
theorem not_isNormalSequence_xiBits (c : ℕ → ℕ) (hc16 : ∀ m, c m < 16)
    (hc : IsNormalSequence 16 c) : ¬ IsNormalSequence 2 (xiBits c) := by
  classical
  intro hnorm
  have hfilter : ∀ N : ℕ,
      (range N).filter (MatchesAt (xiBits c) (wordOf 2 4 3))
        = (range N).filter (fun n => isZZOO (n % 4) (blk c 2 (n / 4))) := by
    intro N
    refine Finset.filter_congr (fun n _ => ?_)
    have hlen : (wordOf 2 4 3).length = 4 := length_wordOf 2 4 3
    constructor
    · intro h j hj
      rw [← xiBits_eq_bitOfWord c 2 n j (by omega)]
      exact h j (by rw [hlen]; exact hj)
    · intro h j hj
      rw [hlen] at hj
      rw [xiBits_eq_bitOfWord c 2 n j (by omega)]
      exact h j hj
  have h1 := tendsto_blockEvent c 2 isZZOO hc16 hc
  have hsum : (∑ r ∈ range 4, ∑ k ∈ range (16 ^ 2),
      if isZZOO r (wordOf 16 2 k) then (1 : ℝ) else 0) = 80 := by
    have hcf : ∀ r : ℕ, (∑ k ∈ range (16 ^ 2), if isZZOO r (wordOf 16 2 k) then (1 : ℝ) else 0)
        = (((range (16 ^ 2)).filter (fun k => isZZOO r (wordOf 16 2 k))).card : ℝ) := by
      intro r; rw [Finset.card_filter]; push_cast; rfl
    have e0 : ((range (16 ^ 2)).filter (fun k => isZZOO 0 (wordOf 16 2 k))).card = 32 := by decide
    have e1 : ((range (16 ^ 2)).filter (fun k => isZZOO 1 (wordOf 16 2 k))).card = 16 := by decide
    have e2 : ((range (16 ^ 2)).filter (fun k => isZZOO 2 (wordOf 16 2 k))).card = 16 := by decide
    have e3 : ((range (16 ^ 2)).filter (fun k => isZZOO 3 (wordOf 16 2 k))).card = 16 := by decide
    rw [Finset.sum_congr rfl (fun r _ => hcf r)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3]
    norm_num
  rw [hsum] at h1
  have h2 := tendsto_winCount_wordOf (b := 2) (s := xiBits c) (by norm_num) hnorm 4 3
  have h2' : Tendsto (fun N => (((range N).filter
      (fun n => isZZOO (n % 4) (blk c 2 (n / 4)))).card : ℝ) / N) atTop (𝓝 (((2 : ℝ) ^ 4)⁻¹)) := by
    refine h2.congr (fun N => ?_)
    rw [winCount, hfilter N]
  have := tendsto_nhds_unique h2' h1
  norm_num at this

/-- **Separation.**  Some binary sequence is abelian-normal but not normal. -/
theorem exists_abelianNormal_not_normal :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ IsAbelianNormalTwo s ∧ ¬ IsNormalSequence 2 s := by
  set c := digitOf 16 (Int.fract NormalNumbers.G4.Sched.fullRealW) with hcdef
  have hc16 : ∀ m, c m < 16 := fun m => digitOf_lt 16 (by norm_num) _ m
  have hc : IsNormalSequence 16 c := by
    have h := NormalNumbers.G4.Sched.isNormal_two_pow_fullRealW 4 (by norm_num)
    norm_num [IsNormal] at h
    exact h
  refine ⟨xiBits c, fun m => ?_, isAbelianNormalTwo_xiBits c hc16 hc,
    not_isNormalSequence_xiBits c hc16 hc⟩
  exact Nat.mod_lt _ (by norm_num)

end NormalNumbers.Abelian
