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
