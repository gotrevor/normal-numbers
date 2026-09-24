import NormalNumbers.AbelianNormal
import NormalNumbers.AbelianBlockDensity
import NormalNumbers.AbelianIntervalBinomial
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
def bitOfWord (v : List ℕ) (r i : ℕ) : ℕ := bitW hexSwap v r i

lemma xiBits_eq_bitOfWord (c : ℕ → ℕ) (S n i : ℕ) (h : (n % 4 + i) / 4 < S) :
    xiBits c (n + i) = bitOfWord (blk c S (n / 4)) (n % 4) i := by
  unfold xiBits bitOfWord bitW
  rw [blk_getD c S (n / 4) _ h]
  have h1 : (n + i) / 4 = n / 4 + (n % 4 + i) / 4 := by omega
  have h2 : (n + i) % 4 = (n % 4 + i) % 4 := by omega
  rw [h1, h2]

/-- The four-bit window predicate for `[0,0,1,1]`, as a function of the offset and the hex pair. -/
def isZZOO (r : ℕ) (v : List ℕ) : Prop :=
  ∀ j < 4, bitOfWord v r j = (wordOf 2 4 3).getD j 0

instance (r : ℕ) (v : List ℕ) : Decidable (isZZOO r v) := Nat.decidableBallLT _ _

/-- The construction is abelian-normal in base two. -/
theorem isAbelianNormalTwo_xiBits (c : ℕ → ℕ) (hc16 : ∀ m, c m < 16)
    (hc : IsNormalSequence 16 c) : IsAbelianNormalTwo (xiBits c) := by
  classical
  have hbin : HBinom hexSwap := by
    intro r m i hr hm hrm hi
    have hm4 : m ≤ 4 := by omega
    interval_cases r <;> interval_cases m <;> interval_cases i <;> first | rfl | decide | omega
  intro L j hj
  -- the window one-count is a function of the offset and the next `L+1` hex digits
  have hones : ∀ n : ℕ, onesCount (xiBits c) L n = onesW hexSwap L (n % 4) (blk c (L + 1) (n / 4)) := by
    intro n
    unfold onesCount onesW NormalNumbers.Walsh.windowSet
    congr 1
    refine Finset.filter_congr (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show bitW hexSwap (blk c (L + 1) (n / 4)) (n % 4) i
        = xiBits c (n + i) from (xiBits_eq_bitOfWord c (L + 1) n i (by omega)).symm]
  have hfreq : ∀ N : ℕ, onesFreq (xiBits c) L j N
      = (((range N).filter
          (fun n => onesW hexSwap L (n % 4) (blk c (L + 1) (n / 4)) = j)).card : ℝ) / N := by
    intro N
    rw [onesFreq]
    have hset : (range N).filter (fun n => onesCount (xiBits c) L n = j)
        = (range N).filter (fun n => onesW hexSwap L (n % 4) (blk c (L + 1) (n / 4)) = j) :=
      Finset.filter_congr (fun n _ => by rw [hones n])
    rw [hset]
  have hmain := tendsto_blockEvent c (L + 1) (fun r v => onesW hexSwap L r v = j) hc16 hc
  have hinner : ∀ r : ℕ, (∑ k ∈ range (16 ^ (L + 1)),
      if onesW hexSwap L r (wordOf 16 (L + 1) k) = j then (1 : ℝ) else 0)
      = (wordCount hexSwap L r (L + 1) j : ℝ) := by
    intro r
    rw [wordCount, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun k _ => by split <;> simp)
  have hwc : ∀ r ∈ range 4, (wordCount hexSwap L r (L + 1) j : ℝ)
      = 16 ^ (L + 1) * (L.choose j : ℝ) / 2 ^ L := by
    intro r hr
    have h := two_pow_mul_wordCount hexSwap hbin L r (L + 1) j (Finset.mem_range.mp hr)
      (by have := Finset.mem_range.mp hr; omega)
    have hR : ((2 : ℝ) ^ L) * (wordCount hexSwap L r (L + 1) j : ℝ)
        = 16 ^ (L + 1) * (L.choose j : ℝ) := by exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    field_simp at hR ⊢
    linarith [hR]
  have hval : (∑ r ∈ range 4, ∑ k ∈ range (16 ^ (L + 1)),
      if onesW hexSwap L r (wordOf 16 (L + 1) k) = j then (1 : ℝ) else 0) / (4 * 16 ^ (L + 1))
      = (L.choose j : ℝ) / 2 ^ L := by
    rw [Finset.sum_congr rfl (fun r hr => by rw [hinner r, hwc r hr]), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have h16 : ((16 : ℝ) ^ (L + 1)) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) ^ L) ≠ 0 := by positivity
    field_simp
    ring
  rw [hval] at hmain
  exact hmain.congr (fun N => (hfreq N).symm)

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
