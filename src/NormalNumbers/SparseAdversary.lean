/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Literature
import NormalNumbers.Bridge
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Sparse adversaries defeat per-block hitting sets

Node N1 of the hitting-set graph (`docs/hitting-set-invariant-2026-09-13.md`).

Fix a base `g ≥ 2`, a block length `k ≥ 1` and a finite candidate set `S` of
multipliers.  The adversary picks one integer `B ≥ 1` and plays the
**block-sparse** irrational

  `α = B · ∑ᵢ g^{-(i+i₀)!}`,

whose base-`g` expansion consists of copies of the digit string of `B`, each
placed just before the position `(i+i₀)!` and separated by long runs of zeros.
Multiplying by `m ∈ S` does not disturb this shape: `m·α` is the same
block-sparse number built from `m·B` instead of `B` (blocks are so far apart
that no carries interact), so every length-`k` window of `m·α` that contains
a nonzero digit is a window of the digit string of `m·B` padded with `k-1`
zeros on both sides.  Hence a block `w ≠ 0^k` absent from all those padded
strings occurs nowhere in any `m·α`, and `S` is not a hitting set.

The digit computation goes through the sequence ↔ real bridge
(`digitOf_realOfDigits`): the digit sequence `blockSeq` is written down
explicitly, its digit series is shown to sum to `m·α` by comparing partial
sums along the block boundaries `e i = (i + i₀)!`, and the bridge recovers
`blockSeq` as the digit map of `m·α`.
-/

namespace NormalNumbers

open Finset Filter Topology

/-- The base-`g` digit string of `n`, most significant digit first, with `k-1`
zeros on each side: every length-`k` window of `m·α` that meets a block of a
block-sparse `α` is a window of this. -/
def paddedDigits (g k n : ℕ) : List ℕ :=
  List.replicate (k - 1) 0 ++ (Nat.digits g n).reverse ++ List.replicate (k - 1) 0

/-! ## The block-sparse digit sequence -/

open Classical in
/-- The block-sparse digit sequence: at positions `e i - L ≤ n < e i` (block `i`)
the digit `c / g^(e i - 1 - n) % g` of `c`, most significant first, ending at
position `e i - 1`; zero everywhere else. -/
noncomputable def blockSeq (g L c : ℕ) (e : ℕ → ℕ) (n : ℕ) : ℕ :=
  if h : ∃ i, e i - L ≤ n ∧ n < e i then c / g ^ (e (Nat.find h) - 1 - n) % g else 0

/-- Blocks are pairwise disjoint when consecutive boundaries are `≥ L` apart. -/
theorem block_unique {L : ℕ} {e : ℕ → ℕ} (hmono : Monotone e)
    (hL : ∀ i, e i + L ≤ e (i + 1)) {i j n : ℕ}
    (hi1 : e i - L ≤ n) (hi2 : n < e i) (hj1 : e j - L ≤ n) (hj2 : n < e j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exfalso; have := hL i; have := hmono (show i + 1 ≤ j by omega); omega
  · exact hij
  · exfalso; have := hL j; have := hmono (show j + 1 ≤ i by omega); omega

theorem blockSeq_of_inBlock (g L c : ℕ) (e : ℕ → ℕ) (hmono : Monotone e)
    (hL : ∀ i, e i + L ≤ e (i + 1)) {i n : ℕ} (h1 : e i - L ≤ n) (h2 : n < e i) :
    blockSeq g L c e n = c / g ^ (e i - 1 - n) % g := by
  unfold blockSeq
  split_ifs with h
  · have hspec := Nat.find_spec h
    rw [block_unique hmono hL hspec.1 hspec.2 h1 h2]
  · exact absurd ⟨i, h1, h2⟩ h

theorem blockSeq_of_not (g L c : ℕ) (e : ℕ → ℕ) {n : ℕ}
    (hn : ∀ i, ¬ (e i - L ≤ n ∧ n < e i)) : blockSeq g L c e n = 0 := by
  unfold blockSeq
  rw [dif_neg (not_exists.mpr hn)]

theorem blockSeq_lt (g L c : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g) (n : ℕ) :
    blockSeq g L c e n < g := by
  unfold blockSeq
  split_ifs
  · exact Nat.mod_lt _ (by omega)
  · omega

/-- A position strictly between the previous block and the next one meets no
block other than block `i`. -/
theorem not_inBlock_of_ne {L k : ℕ} {e : ℕ → ℕ} (hmono : Monotone e)
    (hk : ∀ i, e i + L + k ≤ e (i + 1)) {i j p : ℕ} (hji : j ≠ i)
    (h1 : e i - L - k < p) (h2 : p < e i + k) : ¬ (e j - L ≤ p ∧ p < e j) := by
  rintro ⟨hj1, hj2⟩
  rcases Nat.lt_or_gt_of_ne hji with h | h
  · have := hk j; have := hmono (show j + 1 ≤ i by omega); omega
  · have := hk i; have := hmono (show i + 1 ≤ j by omega); omega

/-! ## The digit series of `blockSeq` sums to `∑ c / g^(e i)` -/

/-- `∑_{j<L} (c / g^j % g) g^j = c % g^L`: the base-`g` expansion. -/
theorem sum_digit_mul_pow (g c L : ℕ) :
    ∑ j ∈ range L, c / g ^ j % g * g ^ j = c % g ^ L := by
  induction L with
  | zero => simp [Nat.mod_one]
  | succ L ih => rw [sum_range_succ, ih, Nat.mod_pow_succ]; ring

/-- The digit series is summable (comparison with the geometric series). -/
theorem summable_digit_series (g : ℕ) (hg : 2 ≤ g) (s : ℕ → ℕ) (hs : ∀ i, s i < g) :
    Summable (fun i : ℕ => (s i : ℝ) / (g : ℝ) ^ (i + 1)) := by
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < (g : ℝ) := lt_trans zero_lt_one hg1
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geometric_of_lt_one (r := (g : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hg1))
  rw [inv_pow, div_le_iff₀ (pow_pos hg0 (i + 1)), pow_succ,
    inv_mul_cancel_left₀ (pow_pos hg0 i).ne']
  exact_mod_cast (hs i).le

/-- The block `i` contributes exactly `c / g^(e i)`. -/
theorem sum_block (g L c : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g) (hc : c < g ^ L)
    (hmono : Monotone e) (hL : ∀ i, e i + L ≤ e (i + 1)) (i : ℕ) (hLe : L ≤ e i) :
    ∑ n ∈ Ico (e i - L) (e i), (blockSeq g L c e n : ℝ) / (g : ℝ) ^ (n + 1)
      = (c : ℝ) / (g : ℝ) ^ (e i) := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  rw [sum_Ico_eq_sum_range, (by omega : e i - (e i - L) = L)]
  have h1 : ∀ q ∈ range L,
      (blockSeq g L c e (e i - L + q) : ℝ) / (g : ℝ) ^ (e i - L + q + 1)
        = ((c / g ^ (L - 1 - q) % g * g ^ (L - 1 - q) : ℕ) : ℝ) / (g : ℝ) ^ (e i) := by
    intro q hq
    rw [mem_range] at hq
    rw [blockSeq_of_inBlock g L c e hmono hL (i := i) (n := e i - L + q) (by omega) (by omega),
      (by omega : e i - 1 - (e i - L + q) = L - 1 - q),
      (by omega : e i - L + q + 1 = e i - (L - 1 - q))]
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
      (by omega : L - 1 - q + (e i - (L - 1 - q)) = e i)]
  rw [sum_congr rfl h1,
    sum_range_reflect (fun j => ((c / g ^ j % g * g ^ j : ℕ) : ℝ) / (g : ℝ) ^ (e i)) L,
    ← sum_div, ← Nat.cast_sum, sum_digit_mul_pow, Nat.mod_eq_of_lt hc]

/-- Positions meeting no block contribute nothing. -/
theorem sum_blockSeq_eq_zero (g L c : ℕ) (e : ℕ → ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, ∀ i, ¬ (e i - L ≤ n ∧ n < e i)) :
    ∑ n ∈ s, (blockSeq g L c e n : ℝ) / (g : ℝ) ^ (n + 1) = 0 :=
  sum_eq_zero fun n hn => by rw [blockSeq_of_not g L c e (hs n hn)]; simp

/-- Partial sums along block boundaries. -/
theorem sum_range_blockSeq (g L c : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g) (hc : c < g ^ L)
    (hmono : Monotone e) (hL : ∀ i, e i + L ≤ e (i + 1)) (he0 : L ≤ e 0) (i : ℕ) :
    ∑ n ∈ range (e i), (blockSeq g L c e n : ℝ) / (g : ℝ) ^ (n + 1)
      = ∑ j ∈ range (i + 1), (c : ℝ) / (g : ℝ) ^ (e j) := by
  induction i with
  | zero =>
    rw [← sum_range_add_sum_Ico _ (Nat.sub_le (e 0) L), sum_blockSeq_eq_zero, zero_add,
      sum_block g L c e hg hc hmono hL 0 he0, sum_range_one]
    intro n hn j ⟨hj1, hj2⟩
    rw [mem_range] at hn
    have := hmono (Nat.zero_le j)
    omega
  | succ i ih =>
    rw [← sum_range_add_sum_Ico _ (hmono (Nat.le_succ i)), ih,
      ← sum_Ico_consecutive _ (m := e i) (n := e (i + 1) - L) (k := e (i + 1))
        (by have := hL i; omega) (Nat.sub_le _ _),
      sum_blockSeq_eq_zero, zero_add,
      sum_block g L c e hg hc hmono hL (i + 1) (by have := hL i; omega), sum_range_succ _ (i + 1)]
    intro n hn j ⟨hj1, hj2⟩
    rw [mem_Ico] at hn
    rcases le_or_gt j i with h | h
    · have := hmono h; omega
    · have := hmono (show i + 1 ≤ j by omega); omega

/-- **The crux**: the digit series of `blockSeq` sums to the sparse series. -/
theorem realOfDigits_blockSeq (g L c : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g) (hc : c < g ^ L)
    (hL : ∀ i, e i + L < e (i + 1)) (he0 : L ≤ e 0)
    (hsum : Summable fun i : ℕ => (c : ℝ) / (g : ℝ) ^ (e i)) :
    realOfDigits g (blockSeq g L c e) = ∑' i, (c : ℝ) / (g : ℝ) ^ (e i) := by
  have hstrict : StrictMono e := strictMono_nat_of_lt_succ fun i => by have := hL i; omega
  have hmono := hstrict.monotone
  have hL' : ∀ i, e i + L ≤ e (i + 1) := fun i => (hL i).le
  have hs := summable_digit_series g hg (blockSeq g L c e) (blockSeq_lt g L c e hg)
  have h1 : Tendsto (fun N => ∑ n ∈ range N, (blockSeq g L c e n : ℝ) / (g : ℝ) ^ (n + 1))
      atTop (𝓝 (realOfDigits g (blockSeq g L c e))) := hs.hasSum.tendsto_sum_nat
  have h2 := h1.comp hstrict.tendsto_atTop
  have h3 : Tendsto (fun i => ∑ j ∈ range (i + 1), (c : ℝ) / (g : ℝ) ^ (e j)) atTop
      (𝓝 (∑' i, (c : ℝ) / (g : ℝ) ^ (e i))) :=
    hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2' : ((fun N => ∑ n ∈ range N, (blockSeq g L c e n : ℝ) / (g : ℝ) ^ (n + 1)) ∘ e)
      = fun i => ∑ j ∈ range (i + 1), (c : ℝ) / (g : ℝ) ^ (e j) :=
    funext fun i => sum_range_blockSeq g L c e hg hc hmono hL' he0 i
  rw [h2'] at h2
  exact tendsto_nhds_unique h2 h3

/-- The zeros between blocks make `blockSeq` a proper digit sequence. -/
theorem properDigits_blockSeq (g L c : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g)
    (hL : ∀ i, e i + L < e (i + 1)) : ProperDigits g (blockSeq g L c e) := by
  have hstrict : StrictMono e := strictMono_nat_of_lt_succ fun i => by have := hL i; omega
  intro N
  refine ⟨e N, hstrict.le_apply, ?_⟩
  rw [blockSeq_of_not]
  · omega
  · rintro j ⟨hj1, hj2⟩
    rcases le_or_gt j N with h | h
    · have := hstrict.monotone h; omega
    · have := hstrict.monotone (show N + 1 ≤ j by omega); have := hL N; omega

/-! ## Windows of `blockSeq` are windows of the padded digit string -/

theorem paddedDigits_length (g k c : ℕ) :
    (paddedDigits g k c).length = (k - 1) + (Nat.digits g c).length + (k - 1) := by
  simp only [paddedDigits, List.length_append, List.length_replicate, List.length_reverse]

/-- The padded digit string, read by index: `k-1` zeros, then the digits of `c`
from the most significant, then zeros — uniformly `(digits g c).getD (…) 0`. -/
theorem paddedDigits_getElem (g k c q : ℕ) (hq : q < (paddedDigits g k c).length) :
    (paddedDigits g k c)[q]
      = if q < k - 1 + (Nat.digits g c).length
        then (Nat.digits g c).getD (k - 1 + (Nat.digits g c).length - 1 - q) 0 else 0 := by
  have hlen := paddedDigits_length g k c
  simp only [paddedDigits, List.getElem_append, List.length_append, List.length_replicate,
    List.length_reverse, List.getElem_replicate, List.getElem_reverse]
  split_ifs with h1 h2 <;> try omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    omega

/-- Near block `i`, `blockSeq` reads the digits of `c` (as `getD`, so that the
leading-zero positions of the block are covered too), then zeros. -/
theorem blockSeq_near (g L c k : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g) (hc : c < g ^ L)
    (hmono : Monotone e) (hk : ∀ i, e i + L + k ≤ e (i + 1)) (i p : ℕ)
    (h1 : e i - L - k < p) (h2 : p < e i + k) :
    blockSeq g L c e p
      = if p < e i then (Nat.digits g c).getD (e i - 1 - p) 0 else 0 := by
  have hL : ∀ i, e i + L ≤ e (i + 1) := fun i => by have := hk i; omega
  rw [Nat.getD_digits _ _ hg]
  split_ifs with hp
  · by_cases hin : e i - L ≤ p
    · exact blockSeq_of_inBlock g L c e hmono hL hin hp
    · rw [blockSeq_of_not, Nat.div_eq_of_lt, Nat.zero_mod]
      · exact lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega))
      · intro j
        by_cases hji : j = i
        · subst hji; omega
        · exact not_inBlock_of_ne hmono hk hji h1 h2
  · apply blockSeq_of_not
    intro j
    by_cases hji : j = i
    · subst hji; omega
    · exact not_inBlock_of_ne hmono hk hji h1 h2

/-- A length-`k` window of `blockSeq` containing a nonzero digit is a window of
the padded digit string of `c`. -/
theorem infix_paddedDigits_of_window (g L c k : ℕ) (e : ℕ → ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (hc : c < g ^ L) (hL : ∀ i, e i + L < e (i + 1)) (hkL : ∀ i, e i + L + k ≤ e (i + 1))
    (he0 : L + k ≤ e 0) (w : List ℕ) (hw : w.length = k) (hw0 : ∃ d ∈ w, d ≠ 0) (n : ℕ)
    (hocc : ∀ j (hj : j < w.length), blockSeq g L c e (n + j) = w[j]) :
    w <:+: paddedDigits g k c := by
  have hmono : Monotone e := monotone_nat_of_le_succ fun i => by have := hL i; omega
  have hL'L : (Nat.digits g c).length ≤ L := (Nat.digits_length_le_iff (by omega) c).2 hc
  obtain ⟨d, hd, hd0⟩ := hw0
  obtain ⟨j₀, hj₀, rfl⟩ := List.mem_iff_getElem.1 hd
  have hne : blockSeq g L c e (n + j₀) ≠ 0 := by rw [hocc j₀ hj₀]; exact hd0
  have hex : ∃ i, e i - L ≤ n + j₀ ∧ n + j₀ < e i := by
    by_contra h
    push Not at h
    refine hne (blockSeq_of_not g L c e fun i hi => ?_)
    have := h i hi.1
    omega
  obtain ⟨i, hi1, hi2⟩ := hex
  have he0i : e 0 ≤ e i := hmono (Nat.zero_le i)
  have hval := blockSeq_near g L c k e hg hc hmono hkL i (n + j₀) (by omega) (by omega)
  rw [if_pos hi2] at hval
  have hidx : e i - 1 - (n + j₀) < (Nat.digits g c).length := by
    by_contra h
    push Not at h
    rw [hval, List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hne
    exact hne rfl
  have hbase : (Nat.digits g c).length + (k - 1) ≤ e i := by
    have := hmono (Nat.zero_le i); omega
  have hlen := paddedDigits_length g k c
  have hpt : ∀ q (hq : q < (paddedDigits g k c).length),
      blockSeq g L c e (e i - (Nat.digits g c).length - (k - 1) + q) = (paddedDigits g k c)[q] := by
    intro q hq
    rw [paddedDigits_getElem, blockSeq_near g L c k e hg hc hmono hkL i
      (e i - (Nat.digits g c).length - (k - 1) + q) (by omega) (by omega)]
    split_ifs with h1 h2 <;> first | omega | rfl | (congr 1; omega)
  have hbn : e i - (Nat.digits g c).length - (k - 1) ≤ n := by omega
  have hw' : w = ((paddedDigits g k c).drop (n - (e i - (Nat.digits g c).length - (k - 1)))).take k := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, hw]; omega
    · intro j hj1 hj2
      rw [List.getElem_take, List.getElem_drop, ← hocc j hj1, ← hpt _ (by omega)]
      congr 1
      omega
  rw [hw']
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-! ## The wiring theorem -/

/-- **Sparse adversaries defeat hitting sets.**  If one integer `B ≥ 1` has the block
`w ≠ 0^k` absent from the padded digit string of every `m·B`, `m ∈ S`, then `S` is not a
per-block hitting set for `(g, k)`.  Berend–Boshernitzan 1994 §3 is the case `B = 1`. -/
theorem not_isHittingSet_of_avoider (g k : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (S : Finset ℕ) (w : List ℕ) (hw : w.length = k) (hwd : ∀ d ∈ w, d < g)
    (hw0 : ∃ d ∈ w, d ≠ 0) (B : ℕ) (hB : 1 ≤ B)
    (havoid : ∀ m ∈ S, 1 ≤ m → ¬ (w <:+: paddedDigits g k (m * B))) :
    ¬ Literature.IsHittingSet g k S := by
  intro hS
  -- a length bound for every `m * B`
  obtain ⟨L, hLdef⟩ : ∃ L, L = S.sup (fun m => m * B) + 1 := ⟨_, rfl⟩
  have hL : ∀ m ∈ S, m * B < g ^ L := fun m hm =>
    calc m * B ≤ S.sup (fun m => m * B) := Finset.le_sup (f := fun m => m * B) hm
      _ < L := by omega
      _ < g ^ L := Nat.lt_pow_self (by omega)
  -- the block boundaries `e i = (i + k₀ + 1)!`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = L + k + 1 := ⟨_, rfl⟩
  obtain ⟨e, he_def⟩ : ∃ e : ℕ → ℕ, e = fun i => (i + (k₀ + 1)).factorial := ⟨_, rfl⟩
  have he : ∀ i, e i + L + k + 2 ≤ e (i + 1) := by
    intro i
    rw [he_def]
    show (i + (k₀ + 1)).factorial + L + k + 2 ≤ (i + 1 + (k₀ + 1)).factorial
    rw [show i + 1 + (k₀ + 1) = (i + (k₀ + 1)) + 1 by ring, Nat.factorial_succ, Nat.succ_mul]
    have h1 := Nat.factorial_pos (i + (k₀ + 1))
    have h2 : i + (k₀ + 1) ≤ (i + (k₀ + 1)) * (i + (k₀ + 1)).factorial :=
      Nat.le_mul_of_pos_right _ h1
    omega
  have he0 : L + k ≤ e 0 := by
    rw [he_def]
    show L + k ≤ (0 + (k₀ + 1)).factorial
    have := Nat.self_le_factorial (0 + (k₀ + 1))
    omega
  have hLe : ∀ i, e i + L < e (i + 1) := fun i => by have := he i; omega
  have hLk : ∀ i, e i + L + k ≤ e (i + 1) := fun i => by have := he i; omega
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 1 < g)
  -- the adversary
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (B : ℝ) * LiouvilleNumber.remainder g k₀ := ⟨_, rfl⟩
  have hα_irr : Irrational α := by
    have h1 : Irrational (liouvilleNumber g) := (liouville_liouvilleNumber hg).irrational
    obtain ⟨p, hp⟩ := LiouvilleNumber.partialSum_eq_rat (m := g) (by omega) k₀
    have h2 : LiouvilleNumber.remainder g k₀
        = liouvilleNumber g - ((p / (g ^ k₀.factorial : ℕ) : ℚ) : ℝ) := by
      rw [← LiouvilleNumber.partialSum_add_remainder hg1 k₀, hp]
      push_cast
      ring
    rw [hα, h2]
    exact Irrational.natCast_mul (h1.sub_ratCast (q := p / (g ^ k₀.factorial : ℕ))) (by omega)
  obtain ⟨m, hmS, hm1, hocc⟩ := hS α hα_irr w hw hwd
  obtain ⟨n, -, hn⟩ := hocc 0
  have hc : m * B < g ^ L := hL m hmS
  -- `m * α` is the sparse series with numerator `m * B`
  have hsum1 : Summable (fun i : ℕ => (1 : ℝ) / (g : ℝ) ^ (i + (k₀ + 1)).factorial) :=
    LiouvilleNumber.remainder_summable hg1 k₀
  have hsum : Summable (fun i => ((m * B : ℕ) : ℝ) / (g : ℝ) ^ (e i)) :=
    (hsum1.mul_left ((m * B : ℕ) : ℝ)).congr fun i => by rw [he_def, mul_one_div]
  have hmα : (m : ℝ) * α = ∑' i, ((m * B : ℕ) : ℝ) / (g : ℝ) ^ (e i) := by
    rw [hα, ← mul_assoc, LiouvilleNumber.remainder, ← tsum_mul_left]
    congr 1
    funext i
    rw [he_def, mul_one_div]
    push_cast
    rfl
  have hreal : realOfDigits g (blockSeq g L (m * B) e) = (m : ℝ) * α := by
    rw [hmα]
    exact realOfDigits_blockSeq g L (m * B) e hg hc hLe (by omega) hsum
  have hmem := realOfDigits_mem_Ico g hg _ (blockSeq_lt g L (m * B) e hg)
    (properDigits_blockSeq g L (m * B) e hg hLe)
  have hfract : Int.fract ((m : ℝ) * α) = realOfDigits g (blockSeq g L (m * B) e) := by
    rw [← hreal, Int.fract_eq_self.mpr hmem]
  have hdig : digitOf g (Int.fract ((m : ℝ) * α)) = blockSeq g L (m * B) e := by
    rw [hfract]
    exact digitOf_realOfDigits g hg _ (blockSeq_lt g L (m * B) e hg)
      (properDigits_blockSeq g L (m * B) e hg hLe)
  apply havoid m hmS hm1
  refine infix_paddedDigits_of_window g L (m * B) k e hg hk hc hLe hLk he0 w hw hw0 n ?_
  intro j hj
  rw [← hdig]
  exact hn j hj

/-! ## Two concrete corollaries -/

/-- `{1, 11}` is not a hitting set for `(4, 1)`: with `B = 62` and `w = [1]`,
`digits₄ 62 = 3,3,2` and `digits₄ 682 = 2,2,2,2,2` contain no `1`. -/
theorem pair_one_eleven_not_hitting : ¬ Literature.IsHittingSet 4 1 {1, 11} :=
  not_isHittingSet_of_avoider 4 1 (by norm_num) le_rfl {1, 11} [1] rfl (by decide)
    ⟨1, by simp, by decide⟩ 62 (by norm_num) (by decide)

/-- `{1, 3, 5}` is not a hitting set for `(2, 3)`: with `B = 1` and `w = [1,1,1]`,
`1`, `11`, `101` in binary contain no `111`. -/
theorem triple_one_three_five_not_hitting : ¬ Literature.IsHittingSet 2 3 {1, 3, 5} :=
  not_isHittingSet_of_avoider 2 3 (by norm_num) (by norm_num) {1, 3, 5} [1, 1, 1] rfl (by decide)
    ⟨1, by simp, by decide⟩ 1 le_rfl (by decide)

end NormalNumbers
