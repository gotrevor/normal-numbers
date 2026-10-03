/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.DecayAeNormal
import NormalNumbers.CantorSelfSimilar
import Mathlib.Topology.Instances.CantorSet
import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-!
# Bugeaud 10.37: a Liouville number in the middle-third Cantor set, normal to base 2

**Source.**  Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge
Tracts in Math. 193 (2012), p. 219, verbatim: "There exist Liouville numbers in the middle third
Cantor set K and there are Liouville numbers which are normal to base 2.  Furthermore, K contains
numbers normal to base 2.  But we do not know whether there are real numbers with all these three
properties.  **Problem 10.37.** Prove that the middle third Cantor set contains Liouville numbers
which are normal to base 2."

The headline `exists_liouville_mem_cantorSet_isNormal_two` uses Mathlib's `cantorSet` (the
intersection of the pre-Cantor sets), Mathlib's `Liouville`, and this repo's `IsNormal 2`.
`exists_computable_liouville_mem_cantorSet_isNormal_two` is the computable strengthening.

**Freshness.**  Open as far as found (2026-10-03 audit, about 75%): forward citations of Bluhm
2000, Bugeaud 2002 (C. R. Acad. Sci. 335), Becher–Heiber–Slaman 2015, Bugeaud 2008 (Math. Ann.),
Levesley–Salp–Velani math/0505074, Bugeaud–Durand 1305.6501, Allen–Chow–Yu 2005.09300; full text
of Becher–Lew Deveali 2607.06773 (closest: sparse Cantor sets, but its window condition forbids
the gaps `[n, w n]` a Liouville point needs), Pramanik–Zhang 2408.03473 (`K` carries no Rajchman
measure, so the Bluhm/Bugeaud Fourier route is closed).  Record:
`docs/CANTOR-LIOUVILLE-AUDIT-2026-10-03.md`.

## Mechanism (a Cassels 1959 measure with forced zero-runs)

Fair coins `ω`.  Ternary digit `i` (weight `3^{-(i+1)}`) is `2·ω i` at *free* positions and `0`
on the runs `[a k, (k+2)·a k)`, `a 0 = 4`, `a (k+1) = 2(k+2)·a k` (`runStart`, `isForced`).

1. Every point lies in `K` (`pt_mem_cantorSet`, proved).
2. Truncating at `a k` gives `|x − p/3^{a k}| < 3^{-(k+2) a k}`: Liouville as soon as infinitely
   many free digits are `2` (`liouville_cantorLiouvilleReal`), which holds a.s.
3. **Cassels lemma** (`secondMoment_le`, the content): with `F(N)` free positions below
   `M = ⌊log₃ N⌋/2`, `𝔼‖Σ_{k<N} e(h 2ᵏ x)‖² ≤ C N² (exp(−c F(N)) + N^{-1/2})`.  The pair
   `(j, j+m)` has frequency `ξ = h(2ᵐ−1)·2ʲ`; `|μ̂(ξ)| ≤ Π_{p free, p<M} |cos(2πξ/3^{p+1})|`
   (`charFun_norm_le`), a factor is `≤ cos(π/9)` at a ternary digit change of `ξ`
   (`abs_cos_le_of_tdig_ne`), and over a full period of `2` mod `3^M` (2 is a primitive root,
   `orderOf_two_zmod_three_pow`) the digit changes are i.i.d. with probability `2/3`
   (`sum_pow_changes`, an exact identity).  The period is `≤ √N`, so partial periods cost
   `N^{3/2}`; pairs with `v₃(2ᵐ−1)` large are rare.
4. The runs leave `F ≥ M/(2(log₂ M + 2))` (`le_freeCount`), so the bound is summable along
   `sched j = ⌊exp √j⌋ + j` (`summable_sched_bound`), whose ratio tends to `1`; a
   Davenport–Erdős–LeVeque step along that schedule (`ae_isNormal_two_of_secondMoment`) gives
   a.s. base-2 normality.

## Difficulty check (known-false siblings, in the kernel)

* **Base 3** must fail, and does: every point misses digit `1`
  (`not_isNormal_three_cantorLiouvilleReal`, proved).  The mechanism's base-2 input is that `2` is
  a unit generating `(ℤ/3ᴹ)ˣ`; for `3` the low digits of `c·3ʲ` vanish (`tdig_mul_three_pow`,
  proved), so the change count, and with it the saving, is `0`.
* **All positions forced** (`free ≡ false`): `F ≡ 0` and the bound in `secondMoment_le` is the
  trivial `C N²`; no normality is claimed.  **All positions free** recovers Cassels 1959.
* **Too few free digits** (`F(N) = o(log log N)`): `summable_sched_bound` is where the run
  schedule enters; the general `secondMoment_le` is stated for every `free`.

No literature input is assumed: the file has no hypothesis `Prop`.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorLiouville

open DecayAeNormal ExplicitSquare CantorSelfSimilar

/-! ## The forced zero-runs -/

/-- Start of the `k`-th forced run: `a 0 = 4`, `a (k+1) = 2 (k+2) a k`. -/
def runStart : ℕ → ℕ
  | 0 => 4
  | k + 1 => 2 * (k + 2) * runStart k

/-- Ternary position `i` is **forced** to `0` iff it lies in a run `[a k, (k+2) a k)`.  (A run
containing `i` has `k < a k ≤ i`, so `k ≤ i` loses nothing; see `isForced_of_mem_run`.) -/
def isForced (i : ℕ) : Bool :=
  (List.range (i + 1)).any fun k => decide (runStart k ≤ i) && decide (i < (k + 2) * runStart k)

/-- Free positions carry a fair `{0, 2}` digit. -/
def isFree (i : ℕ) : Bool := !isForced i

/-- Non-vacuity anchors: run `0` is `[4, 8)`, run `1` is `[16, 48)`. -/
theorem isForced_anchor :
    isForced 3 = false ∧ isForced 4 = true ∧ isForced 7 = true ∧ isForced 8 = false ∧
      isForced 15 = false ∧ isForced 16 = true ∧ isForced 47 = true ∧ isForced 48 = false := by
  decide

theorem lt_runStart (k : ℕ) : k < runStart k := by
  induction k with
  | zero => simp [runStart]
  | succ k ih =>
    simp only [runStart]
    nlinarith

theorem isForced_of_mem_run {k i : ℕ} (h1 : runStart k ≤ i) (h2 : i < (k + 2) * runStart k) :
    isForced i = true := by
  unfold isForced
  rw [List.any_eq_true]
  refine ⟨k, List.mem_range.2 (by have := lt_runStart k; omega), ?_⟩
  simp [h1, h2]

/-! ## The points -/

/-- Ternary digits of the point coded by coins `ω`, for a free-position predicate `free`. -/
def ptDigit (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ℕ :=
  if free i && ω i then 2 else 0

/-- The point `Σ ptDigit i · 3^{-(i+1)}`. -/
noncomputable def pt (free : ℕ → Bool) (ω : ℕ → Bool) : ℝ := realOfDigits 3 (ptDigit free ω)

/-- The Cantor–Liouville point coded by `ω`. -/
noncomputable def cantorLiouvilleReal (ω : ℕ → Bool) : ℝ := pt isFree ω

/-- Number of free positions below `M`. -/
def freeCount (free : ℕ → Bool) (M : ℕ) : ℕ :=
  ((Finset.range M).filter fun i => free i = true).card

theorem ptDigit_lt (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ptDigit free ω i < 3 := by
  unfold ptDigit; split_ifs <;> norm_num

theorem ptDigit_ne_one (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ptDigit free ω i ≠ 1 := by
  unfold ptDigit; split_ifs <;> norm_num

theorem pt_eq_ofDigits (free : ℕ → Bool) (ω : ℕ → Bool) :
    pt free ω = Real.ofDigits (fun i => (⟨ptDigit free ω i, ptDigit_lt free ω i⟩ : Fin 3)) := by
  unfold pt realOfDigits Real.ofDigits Real.ofDigitsTerm
  congr 1

/-- **Every point lies in the middle-third Cantor set.**  (Mathlib:
`ofDigits_zero_two_sequence_mem_cantorSet`.) -/
theorem pt_mem_cantorSet (free : ℕ → Bool) (ω : ℕ → Bool) : pt free ω ∈ cantorSet := by
  rw [pt_eq_ofDigits]
  refine ofDigits_zero_two_sequence_mem_cantorSet fun n h => ptDigit_ne_one free ω n ?_
  have := congrArg Fin.val h
  simpa using this

theorem measurable_pt (free : ℕ → Bool) : Measurable (pt free) := by
  unfold pt realOfDigits
  refine Measurable.tsum fun i => Measurable.div_const ?_ _
  refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
  exact (measurable_of_countable (fun b : Bool => if free i && b then 2 else 0)).comp
    (measurable_pi_apply i)

/-! ## Known-false sibling: base 3 -/

theorem ptDigit_proper (free : ℕ → Bool) (ω : ℕ → Bool)
    (hforced : ∀ N, ∃ i, N ≤ i ∧ free i = false) : ProperDigits 3 (ptDigit free ω) := by
  intro N
  obtain ⟨i, hi, hf⟩ := hforced N
  exact ⟨i, hi, by simp [ptDigit, hf]⟩

/-- **The base-3 sibling fails, as it must.**  Whenever forced positions recur, the point's
ternary expansion is `ptDigit`, which never shows the digit `1`. -/
theorem not_isNormal_three_pt (free : ℕ → Bool) (ω : ℕ → Bool)
    (hforced : ∀ N, ∃ i, N ≤ i ∧ free i = false) : ¬ IsNormal 3 (pt free ω) := by
  intro h
  have hp := ptDigit_proper free ω hforced
  have hmem := realOfDigits_mem_Ico 3 (by norm_num) _ (ptDigit_lt free ω) hp
  rw [Set.mem_Ico] at hmem
  unfold IsNormal at h
  rw [pt, Int.fract_eq_self.mpr hmem,
    digitOf_realOfDigits 3 (by norm_num) _ (ptDigit_lt free ω) hp] at h
  have ht := h [1] (by simp) (by intro d hd; simp at hd; omega)
  have h0 : ∀ n, countOccurrences [1] ((List.range n).map (ptDigit free ω)) = 0 := by
    intro n
    rw [countOccurrences_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i - ⟨-, hi⟩
    simp at hi
    exact ptDigit_ne_one free ω i hi.symm
  simp only [h0, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

theorem isFree_runStart (k : ℕ) : isFree (runStart k) = false := by
  have h : isForced (runStart k) = true :=
    isForced_of_mem_run le_rfl (by have := lt_runStart k; nlinarith)
  simp [isFree, h]

/-- Every Cantor–Liouville point is non-normal in base 3. -/
theorem not_isNormal_three_cantorLiouvilleReal (ω : ℕ → Bool) :
    ¬ IsNormal 3 (cantorLiouvilleReal ω) :=
  not_isNormal_three_pt isFree ω fun N =>
    ⟨runStart N, (lt_runStart N).le, isFree_runStart N⟩

/-! ## Free gaps between the runs -/

theorem isFree_of_not_mem_run {i : ℕ} (h : ∀ k, ¬ (runStart k ≤ i ∧ i < (k + 2) * runStart k)) :
    isFree i = true := by
  unfold isFree isForced
  simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  intro k _ hk
  exact h k hk

theorem runStart_succ_eq (k : ℕ) : runStart (k + 1) = 2 * (k + 2) * runStart k := rfl

theorem runStart_mono : Monotone runStart := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [runStart_succ_eq]; nlinarith

theorem runEnd_mono : Monotone fun k => (k + 2) * runStart k := by
  refine monotone_nat_of_le_succ fun k => ?_
  show (k + 2) * runStart k ≤ (k + 1 + 2) * runStart (k + 1)
  rw [runStart_succ_eq]
  have : (k + 2) * runStart k ≤ (k + 2) * runStart k * (2 * (k + 3)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  calc _ ≤ (k + 2) * runStart k * (2 * (k + 3)) := this
    _ = _ := by ring

/-- Lower end of the free gap before run `k`. -/
def gapStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => (k + 2) * runStart k

theorem isFree_gap {k i : ℕ} (h1 : gapStart k ≤ i) (h2 : i < runStart k) : isFree i = true := by
  refine isFree_of_not_mem_run fun j ⟨hj1, hj2⟩ => ?_
  rcases Nat.lt_or_ge j k with hjk | hjk
  · cases k with
    | zero => omega
    | succ k =>
      have := runEnd_mono (show j ≤ k by omega)
      simp only [gapStart] at h1
      simp only at this; omega
  · have := runStart_mono hjk; omega

theorem isFree_after {k i : ℕ} (h1 : (k + 2) * runStart k ≤ i) (h2 : i < runStart (k + 1)) :
    isFree i = true := isFree_gap (k := k + 1) h1 h2

theorem gap_size (k : ℕ) : runStart k ≤ 2 * (runStart k - gapStart k) := by
  cases k with
  | zero => simp [gapStart]; omega
  | succ k =>
    simp only [gapStart, runStart_succ_eq]
    have : 2 * (k + 2) * runStart k = 2 * ((k + 2) * runStart k) := by ring
    rw [this]; omega

theorem two_pow_le_runStart (k : ℕ) : 2 ^ k ≤ runStart k := by
  induction k with
  | zero => simp [runStart]
  | succ k ih => rw [runStart_succ_eq, pow_succ]; nlinarith

theorem card_le_freeCount {s e M : ℕ} (he : e ≤ M) (hf : ∀ i, s ≤ i → i < e → isFree i = true) :
    e - s ≤ freeCount isFree M := by
  unfold freeCount
  rw [← Nat.card_Ico]
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hf i hi.1 hi.2⟩

theorem card_le_freeCount₂ {s e s' M : ℕ} (hes : e ≤ s') (heM : e ≤ M)
    (hf : ∀ i, s ≤ i → i < e → isFree i = true) (hf' : ∀ i, s' ≤ i → i < M → isFree i = true) :
    (e - s) + (M - s') ≤ freeCount isFree M := by
  unfold freeCount
  rcases Nat.lt_or_ge M s' with hM | hM
  · have := card_le_freeCount heM hf
    unfold freeCount at this
    omega
  rw [← Nat.card_Ico, ← Nat.card_Ico, ← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun i hi => ?_
    simp only [Finset.mem_union, Finset.mem_Ico] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hi with hi | hi
    · exact ⟨by omega, hf i hi.1 hi.2⟩
    · exact ⟨by omega, hf' i hi.1 hi.2⟩
  · rw [Finset.disjoint_left]; intro i h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega

theorem isFree_runEnd (k : ℕ) : isFree ((k + 2) * runStart k) = true :=
  isFree_after le_rfl (by rw [runStart_succ_eq]; have := lt_runStart k; nlinarith)

theorem summable_ptDigit (free : ℕ → Bool) (ω : ℕ → Bool) :
    Summable fun i => (ptDigit free ω i : ℝ) / (3 : ℝ) ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)))
  have : (ptDigit free ω i : ℝ) ≤ 3 := by exact_mod_cast (ptDigit_lt free ω i).le
  rw [inv_pow, div_le_iff₀ (by positivity), pow_succ, inv_mul_cancel_left₀ (by positivity)]
  exact this

/-! ## Liouville -/

/-- **Liouville property.**  Confidence 93%.

English proof.  Fix `n`, pick `k ≥ n` such that some free position `i ≥ (k+2)·a k` has
`ω i = true` (the hypothesis).  Put `b = 3^{a k}` and `a = Σ_{i < a k} ptDigit i · 3^{a k − 1 − i}`.
Digits in `[a k, (k+2) a k)` are forced zeros, so `0 ≤ x − a/b = Σ_{i ≥ (k+2) a k} d_i 3^{-(i+1)}`.
This is `> 0` (a digit `2` there) and `< 3^{-(k+2) a k}` (all digits `≤ 2`, and run `k+1`
forces zeros, so the geometric bound `Σ_{i ≥ L} 2·3^{-(i+1)} = 3^{-L}` is strict).  Hence
`|x − a/b| < b^{-(k+2)} ≤ b^{-n}` with `b = 3^{a k} ≥ 3^4 > 1`. -/
theorem liouville_cantorLiouvilleReal (ω : ℕ → Bool)
    (hω : ∀ n, ∃ i, n ≤ i ∧ isFree i = true ∧ ω i = true) :
    Liouville (cantorLiouvilleReal ω) := by
  intro n
  set A := runStart n
  set T := (n + 2) * A
  set d := ptDigit isFree ω
  set f : ℕ → ℝ := fun i => (d i : ℝ) / 3 ^ (i + 1)
  have hf : Summable f := summable_ptDigit isFree ω
  have hd2 : ∀ i, (d i : ℝ) ≤ 2 := fun i => by
    have : d i ≤ 2 := by simp only [d, ptDigit]; split_ifs <;> norm_num
    exact_mod_cast this
  have hf0 : ∀ i, 0 ≤ f i := fun i => by positivity
  have hrun : ∀ i, A ≤ i → i < T → d i = 0 := by
    intro i h1 h2
    have := isForced_of_mem_run (k := n) h1 h2
    simp [d, ptDigit, isFree, this]
  obtain ⟨i0, hi0, hfree, hωi⟩ := hω T
  have hA1 : 1 ≤ A := by have := lt_runStart n; omega
  set a : ℤ := ∑ i ∈ Finset.range A, ((d i * 3 ^ (A - 1 - i) : ℕ) : ℤ)
  set b : ℤ := 3 ^ A
  have hb : (b : ℝ) = 3 ^ A := by simp [b]
  have hb1 : 1 < b := one_lt_pow₀ (by norm_num) (by omega)
  have hx : cantorLiouvilleReal ω = ∑ i ∈ Finset.range T, f i + ∑' i, f (i + T) := by
    unfold cantorLiouvilleReal pt realOfDigits
    simp only [Nat.cast_ofNat]
    exact (hf.sum_add_tsum_nat_add T).symm
  have hpart : ∑ i ∈ Finset.range T, f i = a / b := by
    have hT : T = A + (T - A) := by have : A ≤ T := by simp only [T]; nlinarith
                                    omega
    rw [hT, Finset.sum_range_add]
    have hz : ∑ x ∈ Finset.range (T - A), f (A + x) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        simp only [Finset.mem_range] at hx
        simp [f, hrun (A + x) (by omega) (by omega)]
    rw [hz, add_zero, hb]
    simp only [a]; push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp only [f]
    have : (3 : ℝ) ^ A = 3 ^ (A - 1 - i) * 3 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  set t := ∑' i, f (i + T)
  have hft : Summable fun i => f (i + T) := (summable_nat_add_iff T).2 hf
  have htpos : 0 < t := by
    refine hft.tsum_pos (fun i => hf0 _) (i0 - T) ?_
    simp only [f, d, ptDigit, Nat.sub_add_cancel hi0, hfree, hωi]; norm_num
  have hg : Summable fun i : ℕ => (2 : ℝ) / 3 ^ (i + T + 1) := by
    have := (summable_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (2 / 3 ^ (T + 1))
    refine this.congr fun i => ?_
    rw [one_div_pow]; field_simp; ring
  have hgsum : ∑' i : ℕ, (2 : ℝ) / 3 ^ (i + T + 1) = 1 / 3 ^ T := by
    have : (fun i : ℕ => (2 : ℝ) / 3 ^ (i + T + 1)) = fun i => 2 / 3 ^ (T + 1) * (1 / 3) ^ i := by
      funext i; rw [one_div_pow, show i + T + 1 = i + (T + 1) by ring, pow_add, pow_succ]; field_simp
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
    field_simp; norm_num
  have hnext : T ≤ runStart (n + 1) := by
    simp only [T, A, runStart_succ_eq]; nlinarith
  have hzero : d (runStart (n + 1)) = 0 := by
    simp [d, ptDigit, isFree_runStart]
  have htlt : t < 1 / 3 ^ T := by
    rw [← hgsum]
    refine Summable.tsum_lt_tsum_of_nonneg (i := runStart (n + 1) - T) (fun i => hf0 _)
      (fun i => ?_) ?_ hg
    · simp only [f]; gcongr; exact hd2 _
    · simp only [f, Nat.sub_add_cancel hnext, hzero, Nat.cast_zero, zero_div]; positivity
  refine ⟨a, b, hb1, ?_, ?_⟩
  · rw [hx, hpart]; intro h; linarith
  · rw [hx, hpart, add_sub_cancel_left, abs_of_pos htpos, hb]
    calc t < 1 / 3 ^ T := htlt
      _ ≤ 1 / ((3 : ℝ) ^ A) ^ n := by
        rw [← pow_mul]
        apply one_div_le_one_div_of_le (by positivity)
        apply pow_le_pow_right₀ (by norm_num)
        simp only [T]; nlinarith

/-- **Almost every coin sequence has infinitely many free `2`s.**  Confidence 98%.

English proof.  Free positions are infinite (`[(k+2) a k, a (k+1))` is free and nonempty).  For
`n` and `L`, take `L` free positions `≥ n`; the coins there are independent fair, so
`P(all false) = 2^{-L}`.  Letting `L → ∞` the event "no free `true` past `n`" is null; take the
countable union over `n`. -/
theorem ae_frequently_free :
    ∀ᵐ ω ∂coinMeasure, ∀ n, ∃ i, n ≤ i ∧ isFree i = true ∧ ω i = true := by
  rw [ae_all_iff]
  intro n
  set p : ℕ → ℕ := fun k => (k + 2) * runStart k
  have hp : StrictMono p := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    show (k + 2) * runStart k < (k + 1 + 2) * runStart (k + 1)
    rw [runStart_succ_eq]
    have ha : 0 < runStart k := by have := lt_runStart k; omega
    calc (k + 2) * runStart k < (k + 2) * runStart k * (2 * (k + 3)) :=
          lt_mul_of_one_lt_right (by positivity) (by omega)
      _ = _ := by ring
  have hpn : ∀ k, k ≤ p k := fun k => by
    have := lt_runStart k; show k ≤ (k + 2) * runStart k; nlinarith
  rw [ae_iff]
  set E := {ω : ℕ → Bool | ¬∃ i, n ≤ i ∧ isFree i = true ∧ ω i = true}
  have hle : ∀ L : ℕ, coinMeasure E ≤ (2⁻¹ : ENNReal) ^ L := by
    intro L
    set S := (Finset.Ico n (n + L)).image p
    have hsub : E ⊆ Set.pi (S : Set ℕ) (fun _ => {false}) := by
      intro ω hω i hi
      simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Ico] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      simp only [E, Set.mem_setOf_eq, not_exists, not_and] at hω
      simp only [Set.mem_singleton_iff]
      have := hω (p k) ((hpn k).trans' hk.1 |>.trans (le_refl _)) (isFree_runEnd k)
      simpa using this
    refine (measure_mono hsub).trans (le_of_eq ?_)
    unfold coinMeasure
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    rw [Finset.prod_congr rfl (fun i _ => by rw [uniform_apply])]
    rw [Finset.prod_const, Finset.card_image_of_injective _ hp.injective, Nat.card_Ico]
    simp
  have ht : Tendsto (fun L : ℕ => (2⁻¹ : ENNReal) ^ L) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

/-! ## The Cassels lemma -/

/-- Ternary digit `i` of an integer `c` (digit `i` of `c mod 3^{i+1}`; Euclidean division). -/
def tdig (c : ℤ) (i : ℕ) : ℤ := c / 3 ^ i % 3

/-- Number of ternary digit changes of `c` at the pairs `(i, i+1)`, `i ∈ P`. -/
def changes (c : ℤ) (P : Finset ℕ) : ℕ :=
  (P.filter fun i => tdig c (i + 1) ≠ tdig c i).card

/-- **Base-3 frequencies have no low digit changes** (the sibling's failure point):
`c · 3ʲ` has digit `0` below `j`. -/
theorem tdig_mul_three_pow (c : ℤ) {i j : ℕ} (hij : i < j) : tdig (c * 3 ^ j) i = 0 := by
  unfold tdig
  have : (3 : ℤ) ^ j = 3 ^ i * 3 ^ (j - i) := by rw [← pow_add]; congr 1; omega
  rw [this, ← mul_assoc, mul_comm c, mul_assoc,
    Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num))]
  obtain ⟨t, ht⟩ : ∃ t, j - i = t + 1 := ⟨j - i - 1, by omega⟩
  rw [ht, pow_succ]
  simp [Int.mul_emod_left, ← mul_assoc]

theorem padicValNat_four_pow_sub_one (n : ℕ) (hn : n ≠ 0) :
    padicValNat 3 (4 ^ n - 1) = 1 + padicValNat 3 n := by
  have := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hn
  simpa using this

theorem three_pow_dvd_iff (j n : ℕ) (hn : n ≠ 0) :
    3 ^ j ∣ 4 ^ n - 1 ↔ j ≤ 1 + padicValNat 3 n := by
  have : (4 ^ n - 1) ≠ 0 := by
    have : 4 ≤ 4 ^ n := Nat.le_self_pow hn 4
    omega
  rw [padicValNat_dvd_iff_le this, padicValNat_four_pow_sub_one n hn]

theorem two_pow_eq_one_iff {n e : ℕ} :
    (2 : ZMod n) ^ e = 1 ↔ n ∣ 2 ^ e - 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), sub_eq_zero]
  push_cast; rfl

/-- **Content locator: `2` generates `(ℤ/3^{M+1})ˣ`.**  Confidence 99%.

English proof.  `2 ≡ −1 (mod 3)` has order `2` mod `3`; by lifting the exponent,
`v₃(2^{2t} − 1) = v₃(4ᵗ − 1) = 1 + v₃(t)`, so the order of `4` mod `3^{M+1}` is `3^M`, and the
order of `2` is `2·3^M = φ(3^{M+1})`.  This is exactly what fails for `3` (`3` is not a unit). -/
theorem orderOf_two_zmod_three_pow (M : ℕ) :
    orderOf (2 : ZMod (3 ^ (M + 1))) = 2 * 3 ^ M := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · rw [two_pow_eq_one_iff, pow_mul, show (2:ℕ)^2 = 4 by norm_num,
      three_pow_dvd_iff _ _ (by positivity), padicValNat.prime_pow]
    omega
  · intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h2 | h3
    · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      subst this
      rw [show 2 * 3 ^ M / 2 = 3 ^ M by omega]
      intro h
      have h' := congrArg (ZMod.castHom (dvd_pow_self 3 (Nat.succ_ne_zero M)) (ZMod 3)) h
      rw [map_pow, map_one, map_ofNat] at h'
      have hodd : Odd (3 ^ M) := Odd.pow (by decide)
      rw [show (2 : ZMod 3) = -1 by decide, hodd.neg_one_pow] at h'
      exact absurd h' (by decide)
    · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (Nat.Prime.dvd_of_dvd_pow hp h3)
      subst this
      rcases M with _ | M
      · simp at h3
      · rw [show 2 * 3 ^ (M + 1) / 3 = 2 * 3 ^ M by rw [pow_succ]; omega,
          Ne, two_pow_eq_one_iff, pow_mul, show (2:ℕ)^2 = 4 by norm_num,
          three_pow_dvd_iff _ _ (by positivity), padicValNat.prime_pow]
        omega

theorem abs_cos_le_mid {θ : ℝ} (h1 : 2 * Real.pi / 9 ≤ θ) (h2 : θ ≤ 8 * Real.pi / 9) :
    |Real.cos θ| ≤ Real.cos (Real.pi / 9) := by
  have hp := Real.pi_pos
  rw [abs_le]; constructor
  · have : Real.cos (8 * Real.pi / 9) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h2
    have e : Real.cos (8 * Real.pi / 9) = -Real.cos (Real.pi / 9) := by
      rw [show 8 * Real.pi / 9 = Real.pi - Real.pi / 9 by ring, Real.cos_pi_sub]
    linarith
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

theorem abs_cos_le_of_mem {w : ℝ} (h : (1 / 9 ≤ w ∧ w ≤ 4 / 9) ∨ (5 / 9 ≤ w ∧ w ≤ 8 / 9)) :
    |Real.cos (2 * Real.pi * w)| ≤ Real.cos (Real.pi / 9) := by
  have hp := Real.pi_pos
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_cos_le_mid (by nlinarith) (by nlinarith)
  · rw [← Real.cos_two_pi_sub]
    exact abs_cos_le_mid (by nlinarith) (by nlinarith)

/-- **A digit change forces a Riesz factor below `cos(π/9)`.**  Confidence 97%.

English proof.  `t = ξ/3^{i+2} mod 1` has leading ternary digits `(tdig ξ (i+1), tdig ξ i)`, so
`t ∈ [a/3 + b/9, a/3 + (b+1)/9)`.  When `a ≠ b` this interval lies in `[1/9, 4/9] ∪ [5/9, 8/9]`,
at distance `≥ 1/18` from `{0, 1/2, 1}`, so `|cos(2πt)| ≤ cos(π/9)`.  Probe: maximum over
`|ξ| < 3000`, `i < 6` is `0.93969262078603 ≈ cos(π/9)` (attained). -/
theorem abs_cos_le_of_tdig_ne (ξ : ℤ) (i : ℕ) (h : tdig ξ (i + 1) ≠ tdig ξ i) :
    |Real.cos (2 * Real.pi * ξ / 3 ^ (i + 2))| ≤ Real.cos (Real.pi / 9) := by
  unfold tdig at h
  set a := ξ / 3 ^ (i + 1) % 3
  set b := ξ / 3 ^ i % 3
  set q := ξ / 3 ^ (i + 2)
  set s := ξ % 3 ^ i
  have h3 : (0 : ℤ) < 3 ^ i := by positivity
  have e1 : ξ = 3 ^ i * (ξ / 3 ^ i) + s := (Int.mul_ediv_add_emod ξ _).symm
  have e2 : ξ / 3 ^ i = 3 * (ξ / 3 ^ (i + 1)) + b := by
    have := (Int.mul_ediv_add_emod (ξ / 3 ^ i) 3).symm
    rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_succ] at this; exact this
  have e3 : ξ / 3 ^ (i + 1) = 3 * q + a := by
    have := (Int.mul_ediv_add_emod (ξ / 3 ^ (i + 1)) 3).symm
    rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_succ] at this; exact this
  have hs0 : 0 ≤ s := Int.emod_nonneg _ h3.ne'
  have hs1 : s < 3 ^ i := Int.emod_lt_of_pos _ h3
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (by norm_num)
  have ha1 : a < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (by norm_num)
  have hb1 : b < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hξ : (ξ : ℝ) = 3 ^ (i + 2) * q + 3 ^ (i + 1) * a + 3 ^ i * b + s := by
    have : ξ = 3 ^ (i + 2) * q + 3 ^ (i + 1) * a + 3 ^ i * b + s := by
      rw [e1, e2, e3]; ring
    exact_mod_cast this
  set u : ℝ := s / 3 ^ (i + 2)
  have hP : (0 : ℝ) < 3 ^ i := by positivity
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 / 9 := by
    have : (s : ℝ) < 3 ^ i := by exact_mod_cast hs1
    simp only [u]; rw [div_lt_iff₀ (by positivity), pow_add]; nlinarith
  have harg : 2 * Real.pi * ξ / 3 ^ (i + 2) =
      2 * Real.pi * ((a : ℝ) / 3 + b / 9 + u) + (q : ℤ) * (2 * Real.pi) := by
    rw [hξ]; simp only [u]; field_simp; ring
  rw [harg, Real.cos_add_int_mul_two_pi]
  apply abs_cos_le_of_mem
  have hA : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hB : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;> rw [hA, hB] at h ⊢ <;>
    simp at h <;> norm_num <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

theorem pt_consB (free : ℕ → Bool) (c : Bool) (ω : ℕ → Bool) :
    pt free (consB c ω) = (if free 0 && c then 2 else 0) / 3 +
      pt (fun i => free (i + 1)) ω / 3 := by
  unfold pt realOfDigits
  simp only [Nat.cast_ofNat]
  rw [(summable_ptDigit free (consB c ω)).tsum_eq_zero_add, ← tsum_div_const]
  congr 1
  · simp [ptDigit, consB]
  · refine tsum_congr fun i => ?_
    simp only [ptDigit, consB]
    rw [pow_succ _ (i + 1)]; field_simp; split_ifs with hh <;> simp_all

theorem norm_one_add_ee_div_two (t : ℝ) : ‖(1 + ee t) / 2‖ = |Real.cos (Real.pi * t)| := by
  have : (1 + ee t) / 2 = ee (t / 2) * (Real.cos (Real.pi * t) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    unfold ee
    have e1 : Complex.exp (2 * Real.pi * Complex.I * ((t / 2 : ℝ) : ℂ)) *
        Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I) =
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (2 * Real.pi * Complex.I * ((t / 2 : ℝ) : ℂ)) *
        Complex.exp (-(((Real.pi * t : ℝ) : ℂ)) * Complex.I) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; ring
    rw [mul_div_assoc', mul_add, e1, e2]; ring
  rw [this, norm_mul, norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem charFun_real (M : ℕ) : ∀ (free : ℕ → Bool) (ξ : ℝ),
    ‖∫ ω, ee (ξ * pt free ω) ∂coinMeasure‖ ≤
      ∏ p ∈ (Finset.range M).filter (fun p => free p = true),
        |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| := by
  induction M with
  | zero =>
    intro free ξ
    simp only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    refine (norm_integral_le_of_norm_le_const (C := 1)
      (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
    simp
  | succ M ih =>
    intro free ξ
    set free' : ℕ → Bool := fun i => free (i + 1)
    set g : (ℕ → Bool) → ℂ := fun ω => ee (ξ * pt free ω)
    have hgm : Measurable g := measurable_ee.comp ((measurable_pt free).const_mul ξ)
    have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
      Integrable.of_bound hgm.aestronglyMeasurable 1
        (Eventually.of_forall fun ω => (norm_ee _).le)
    set I' := ∫ ω, ee (ξ / 3 * pt free' ω) ∂coinMeasure
    have hc : ∀ c, ∫ ω, g (consB c ω) ∂coinMeasure =
        ee (ξ * ((if free 0 && c then 2 else 0) / 3)) * I' := by
      intro c
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [g, pt_consB, ← ee_add]
      congr 1; ring
    have hsplit : ∫ ω, g ω ∂coinMeasure =
        2⁻¹ * ∫ ω, g (consB true ω) ∂coinMeasure + 2⁻¹ * ∫ ω, g (consB false ω) ∂coinMeasure := by
      conv_lhs => rw [coinMeasure_eq]
      rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
          ((hgi _ inferInstance).smul_measure (by simp)),
        integral_smul_measure, integral_smul_measure,
        integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
        integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
      simp [ENNReal.toReal_inv]
    have hI' := ih free' (ξ / 3)
    change ‖∫ ω, g ω ∂coinMeasure‖ ≤ _
    rw [hsplit, hc, hc, Finset.prod_filter, Finset.prod_range_succ', ← Finset.prod_filter]
    have hre : ∏ p ∈ (Finset.range M).filter (fun p => free (p + 1) = true),
        |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1 + 1))| =
        ∏ p ∈ (Finset.range M).filter (fun p => free' p = true),
        |Real.cos (2 * Real.pi * (ξ / 3) / 3 ^ (p + 1))| := by
      refine Finset.prod_congr rfl fun p _ => ?_
      congr 2; rw [pow_succ]; ring
    rw [hre]
    by_cases h0 : free 0 = true
    · simp only [h0, Bool.true_and, if_true, Bool.false_eq_true, if_false]
      have : 2⁻¹ * (ee (ξ * (2 / 3)) * I') + 2⁻¹ * (ee (ξ * (0 / 3)) * I') =
          ((1 + ee (2 * ξ / 3)) / 2) * I' := by
        rw [show ξ * (0 / 3) = 0 by ring, show ξ * (2 / 3) = 2 * ξ / 3 by ring]
        simp [ee]; ring
      rw [this, norm_mul, norm_one_add_ee_div_two, mul_comm,
        show Real.pi * (2 * ξ / 3) = 2 * Real.pi * ξ / 3 ^ (0 + 1) by ring]
      exact mul_le_mul_of_nonneg_right hI' (abs_nonneg _)
    · simp only [Bool.not_eq_true] at h0
      simp only [h0, Bool.false_and, Bool.false_eq_true, if_false]
      have : 2⁻¹ * (ee (ξ * (0 / 3)) * I') + 2⁻¹ * (ee (ξ * (0 / 3)) * I') = I' := by
        rw [show ξ * (0 / 3) = 0 by ring]; simp [ee]; ring
      rw [this, mul_one]
      exact hI'

/-- **Riesz-product bound for the characteristic function.**  Confidence 94%.

English proof.  `pt free ω = Σ_{p<M} d_p 3^{-(p+1)} + 3^{-M}·(tail)`, the two parts independent
under `coinMeasure` (disjoint coordinates).  So `𝔼 e(ξx)` factors; each free `p < M` contributes
`𝔼 e(2ξ ω_p/3^{p+1}) = (1 + e(2ξ/3^{p+1}))/2`, of modulus `|cos(2πξ/3^{p+1})|`; forced `p`
contribute `1`; the tail factor has modulus `≤ 1`. -/
theorem charFun_norm_le (free : ℕ → Bool) (ξ : ℤ) (M : ℕ) :
    ‖∫ ω, ee (ξ * pt free ω) ∂coinMeasure‖ ≤
      ∏ p ∈ (Finset.range M).filter (fun p => free p = true),
        |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| :=
  charFun_real M free ξ

/-! ### Cassels' three-point route to `secondMoment_le` -/

theorem cos_three_sum (x : ℝ) :
    Real.cos x + Real.cos (x + 2 * Real.pi / 3) + Real.cos (x + 2 * (2 * Real.pi / 3)) = 0 := by
  have h1 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    ring
  have h2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  have h3 : Real.cos (2 * (2 * Real.pi / 3)) = -1 / 2 := by
    rw [Real.cos_two_mul, h1]; ring
  have h4 : Real.sin (2 * (2 * Real.pi / 3)) = -(Real.sqrt 3 / 2) := by
    rw [Real.sin_two_mul, h1, h2]; ring
  rw [Real.cos_add, Real.cos_add, h1, h2, h3, h4]; ring

/-- **Cassels' three-point bound.** -/
theorem three_point (x : ℝ) :
    ∑ t ∈ Finset.range 3, |Real.cos (x + t * (2 * Real.pi / 3))| ≤ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, zero_mul, add_zero, one_mul, zero_add]
  have hs := cos_three_sum x
  have a1 := Real.cos_le_one x
  have a2 := Real.cos_le_one (x + 2 * Real.pi / 3)
  have a3 := Real.cos_le_one (x + 2 * (2 * Real.pi / 3))
  have b1 := Real.neg_one_le_cos x
  have b2 := Real.neg_one_le_cos (x + 2 * Real.pi / 3)
  have b3 := Real.neg_one_le_cos (x + 2 * (2 * Real.pi / 3))
  rcases abs_cases (Real.cos x) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
  rcases abs_cases (Real.cos (x + 2 * Real.pi / 3)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
  rcases abs_cases (Real.cos (x + 2 * (2 * Real.pi / 3))) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
  rw [e1, e2, e3] <;> linarith

/-- Positions `p ∈ [v+1, v+k)` that are free. -/
def posSet (free : ℕ → Bool) (v k : ℕ) : Finset ℕ :=
  (Finset.range (v + k)).filter fun p => v + 1 ≤ p ∧ free p = true

/-- The Riesz majorant at offset `v`. -/
noncomputable def Hf (free : ℕ → Bool) (v k : ℕ) (u : ℝ) : ℝ :=
  ∏ p ∈ posSet free v k, |Real.cos (2 * Real.pi * (3 ^ v * u) / 3 ^ (p + 1))|

theorem Hf_nonneg (free : ℕ → Bool) (v k : ℕ) (u : ℝ) : 0 ≤ Hf free v k u :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem Hf_le_one (free : ℕ → Bool) (v k : ℕ) (u : ℝ) : Hf free v k u ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _

theorem Hf_periodic (free : ℕ → Bool) (v k : ℕ) (u : ℝ) (s : ℤ) :
    Hf free v k (u + 3 ^ k * s) = Hf free v k u := by
  unfold Hf
  refine Finset.prod_congr rfl fun p hp => ?_
  simp only [posSet, Finset.mem_filter, Finset.mem_range] at hp
  have he : (3 : ℝ) ^ v * 3 ^ k = 3 ^ (p + 1) * 3 ^ (v + k - (p + 1)) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have : 2 * Real.pi * (3 ^ v * (u + 3 ^ k * s)) / 3 ^ (p + 1) =
      2 * Real.pi * (3 ^ v * u) / 3 ^ (p + 1) + ((s * 3 ^ (v + k - (p + 1)) : ℤ) : ℝ) * (2 * Real.pi) := by
    have h3 : (3 : ℝ) ^ (p + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    linear_combination (s : ℝ) * he
  rw [this, Real.cos_add_int_mul_two_pi]

theorem Hf_succ (free : ℕ → Bool) (v k : ℕ) (hk : 1 ≤ k) (u : ℝ) :
    Hf free v (k + 1) u = Hf free v k u *
      (if free (v + k) = true then |Real.cos (2 * Real.pi * (3 ^ v * u) / 3 ^ (v + k + 1))| else 1) := by
  unfold Hf posSet
  rw [show v + (k + 1) = (v + k) + 1 by ring, Finset.range_add_one, Finset.filter_insert]
  by_cases hf : free (v + k) = true
  · rw [if_pos ⟨by omega, hf⟩, Finset.prod_insert (by simp), if_pos hf, mul_comm]
  · rw [if_neg (fun h => hf h.2), if_neg hf, mul_one]

theorem sum_range_mul_eq (f : ℕ → ℝ) (L q : ℕ) :
    ∑ w ∈ Finset.range (L * q), f w = ∑ t ∈ Finset.range q, ∑ u ∈ Finset.range L, f (L * t + u) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem three_dvd_add_iff (k t u : ℕ) (hk : 1 ≤ k) : 3 ∣ 3 ^ k * t + u ↔ 3 ∣ u := by
  have : 3 ∣ 3 ^ k * t := Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) t
  exact (Nat.dvd_add_right this)

/-- **Cassels' residue bound.**  Over units `u mod 3^{j+1}`, the majorant averages to
`(2/3)^{#free positions}`. -/
theorem residue_sum_le (free : ℕ → Bool) (v : ℕ) : ∀ j : ℕ,
    ∑ u ∈ Finset.range (3 ^ (j + 1)), (if 3 ∣ u then 0 else Hf free v (j + 1) u) ≤
      2 * 3 ^ j * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card := by
  intro j
  induction j with
  | zero =>
    have : posSet free v (0 + 1) = ∅ := by
      ext p; simp [posSet]; omega
    simp only [this, Finset.card_empty, pow_zero, Hf, Finset.prod_empty]
    simp [Finset.sum_range_succ]
    norm_num
  | succ j ih =>
    set k := j + 1
    have hk : 1 ≤ k := by omega
    rw [show 3 ^ (k + 1) = 3 ^ k * 3 by ring, sum_range_mul_eq, Finset.sum_comm]
    have hstep : ∀ u ∈ Finset.range (3 ^ k),
        ∑ t ∈ Finset.range 3, (if 3 ∣ 3 ^ k * t + u then (0:ℝ) else
          Hf free v (k + 1) ((3 ^ k * t + u : ℕ) : ℝ)) ≤
        (if free (v + k) = true then 2 else 3) * (if 3 ∣ u then 0 else Hf free v k u) := by
      intro u _
      by_cases hu : 3 ∣ u
      · simp [three_dvd_add_iff k _ u hk, hu]
      · simp only [three_dvd_add_iff k _ u hk, hu, if_false]
        have hper : ∀ t : ℕ, Hf free v k ((3 ^ k * t + u : ℕ) : ℝ) = Hf free v k u := by
          intro t
          have := Hf_periodic free v k u t
          rw [← this]; congr 1; push_cast; ring
        simp_rw [Hf_succ free v k hk, hper, ← Finset.mul_sum]
        rw [mul_comm]
        gcongr
        · exact Hf_nonneg _ _ _ _
        by_cases hf : free (v + k) = true
        · simp only [hf, if_true]
          have := three_point (2 * Real.pi * (3 ^ v * u) / 3 ^ (v + k + 1))
          refine le_of_eq_of_le (Finset.sum_congr rfl fun t _ => ?_) this
          congr 2
          push_cast
          field_simp
          ring
        · simp [hf]
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    have hcard : (posSet free v (k + 1)).card =
        (posSet free v k).card + (if free (v + k) = true then 1 else 0) := by
      unfold posSet
      rw [show v + (k + 1) = (v + k) + 1 by ring, Finset.range_add_one, Finset.filter_insert]
      by_cases hf : free (v + k) = true
      · rw [if_pos ⟨by omega, hf⟩, Finset.card_insert_of_notMem (by simp), if_pos hf]
      · rw [if_neg (fun h => hf h.2), if_neg hf, add_zero]
    rw [hcard]
    by_cases hf : free (v + k) = true
    · simp only [hf, if_true]
      calc (2 : ℝ) * _ ≤ 2 * (2 * 3 ^ j * (2 / 3 : ℝ) ^ (posSet free v k).card) := by gcongr
        _ = _ := by rw [pow_succ, pow_succ]; ring
    · simp only [hf, if_false, Bool.false_eq_true, add_zero]
      calc (3 : ℝ) * _ ≤ 3 * (2 * 3 ^ j * (2 / 3 : ℝ) ^ (posSet free v k).card) := by gcongr
        _ = _ := by rw [pow_succ]; ring

theorem Hf_mod (free : ℕ → Bool) (v k n : ℕ) :
    Hf free v k ((n % 3 ^ k : ℕ) : ℝ) = Hf free v k n := by
  have := Hf_periodic free v k ((n % 3 ^ k : ℕ) : ℝ) ((n / 3 ^ k : ℕ) : ℤ)
  rw [← this]; congr 1
  have h := Nat.mod_add_div n (3 ^ k)
  have h' : ((n % 3 ^ k : ℕ) : ℝ) + ((3 ^ k * (n / 3 ^ k) : ℕ) : ℝ) = n := by
    rw [← Nat.cast_add, h]
  push_cast at h'
  rw [Int.cast_natCast]; linarith

theorem card_units_range (j : ℕ) :
    ((Finset.range (3 ^ (j + 1))).filter fun u => ¬ 3 ∣ u).card = 2 * 3 ^ j := by
  have h := Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos j)
  rw [Nat.totient_eq_card_coprime] at h
  rw [show 2 * 3 ^ j = 3 ^ (j + 1 - 1) * (3 - 1) by simp; ring, ← h]
  congr 1
  refine Finset.filter_congr fun u _ => ?_
  rw [Nat.coprime_pow_left_iff (Nat.succ_pos j), Nat.Prime.coprime_iff_not_dvd Nat.prime_three]

/-- **One period of the doubling orbit covers the units once.** -/
theorem block_sum (free : ℕ → Bool) (v j c : ℕ) (hc : ¬ 3 ∣ c) :
    ∑ b ∈ Finset.range (2 * 3 ^ j), Hf free v (j + 1) ((c * 2 ^ b : ℕ) : ℝ) =
      ∑ u ∈ Finset.range (3 ^ (j + 1)), (if 3 ∣ u then 0 else Hf free v (j + 1) u) := by
  have hfl : ∑ u ∈ Finset.range (3 ^ (j + 1)), (if 3 ∣ u then 0 else Hf free v (j + 1) u) =
      ∑ u ∈ (Finset.range (3 ^ (j + 1))).filter (fun u => ¬ 3 ∣ u), Hf free v (j + 1) u := by
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun u _ => ?_; split_ifs <;> simp_all
  rw [hfl]
  simp_rw [← Hf_mod free v (j + 1) (c * 2 ^ _)]
  set n := 3 ^ (j + 1)
  have hcop : Nat.Coprime c n :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hc).symm
  have hord := orderOf_two_zmod_three_pow j
  have hfin : IsOfFinOrder (2 : ZMod n) := orderOf_pos_iff.1 (by rw [hord]; positivity)
  have hinj : Set.InjOn (fun b => c * 2 ^ b % n) (Finset.range (2 * 3 ^ j) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : ((c * 2 ^ a : ℕ) : ZMod n) = ((c * 2 ^ b : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).2 hab
    push_cast at h1
    have hu : IsUnit (c : ZMod n) := (ZMod.unitOfCoprime c hcop).isUnit
    have h2 := hu.mul_left_cancel h1
    rw [hfin.pow_inj_mod, hord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
    exact h2
  have hmaps : Set.MapsTo (fun b => c * 2 ^ b % n) (Finset.range (2 * 3 ^ j) : Set ℕ)
      ((Finset.range n).filter fun u => ¬ 3 ∣ u : Finset ℕ) := by
    intro b _
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨Nat.mod_lt _ (by positivity), fun h3 => ?_⟩
    have h3n : 3 ∣ n := dvd_pow_self 3 (Nat.succ_ne_zero j)
    have : 3 ∣ c * 2 ^ b := by
      rw [← Nat.mod_add_div (c * 2 ^ b) n]
      exact dvd_add h3 (Dvd.dvd.mul_right h3n _)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h | h
    · exact hc h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by decide)
  refine Finset.sum_nbij (fun b => c * 2 ^ b % n) (fun b hb => hmaps hb) hinj ?_ (fun _ _ => rfl)
  exact Finset.surjOn_of_injOn_of_card_le _ hmaps hinj
    (by rw [card_units_range, Finset.card_range])

/-- **Partial periods.** -/
theorem sum_Hf_le (free : ℕ → Bool) (v j c : ℕ) (hc : ¬ 3 ∣ c) (N : ℕ) :
    ∑ b ∈ Finset.range N, Hf free v (j + 1) ((c * 2 ^ b : ℕ) : ℝ) ≤
      (N + 2 * 3 ^ j) * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card := by
  set L := 2 * 3 ^ j
  set f : ℕ → ℝ := fun b => Hf free v (j + 1) ((c * 2 ^ b : ℕ) : ℝ)
  have hL : 0 < L := by positivity
  have hper1 : (3 ^ (j + 1)) ∣ 2 ^ L - 1 := by
    rw [← two_pow_eq_one_iff]
    have := pow_orderOf_eq_one (2 : ZMod (3 ^ (j + 1)))
    rwa [orderOf_two_zmod_three_pow] at this
  have hper : ∀ t b, f (L * t + b) = f b := by
    intro t b
    induction t with
    | zero => simp
    | succ t ih =>
      rw [← ih]
      obtain ⟨s, hs⟩ := hper1
      simp only [f]
      have h2 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have : c * 2 ^ (L * (t + 1) + b) = c * 2 ^ (L * t + b) + 3 ^ (j + 1) * (c * 2 ^ (L * t + b) * s) := by
        rw [show L * (t + 1) + b = (L * t + b) + L by ring, pow_add]
        have : 2 ^ L = 3 ^ (j + 1) * s + 1 := by omega
        rw [this]; ring
      rw [this]
      have := Hf_periodic free v (j + 1) ((c * 2 ^ (L * t + b) : ℕ) : ℝ) ((c * 2 ^ (L * t + b) * s : ℕ) : ℤ)
      rw [← this]; congr 1; push_cast; ring
  set q := N / L + 1
  have hNq : N ≤ L * q := by
    have := Nat.lt_div_mul_add (a := N) hL
    simp only [q]; nlinarith [Nat.div_add_mod N L, Nat.mod_lt N hL]
  have hf0 : ∀ b, 0 ≤ f b := fun b => Hf_nonneg _ _ _ _
  calc ∑ b ∈ Finset.range N, f b ≤ ∑ b ∈ Finset.range (L * q), f b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNq) (fun b _ _ => hf0 b)
    _ = q * ∑ b ∈ Finset.range L, f b := by
        rw [sum_range_mul_eq]; simp_rw [hper]; simp
    _ ≤ q * (L * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card) := by
        gcongr
        rw [block_sum free v j c hc]
        refine (residue_sum_le free v j).trans (le_of_eq ?_)
        simp [L]
    _ ≤ _ := by
        rw [← mul_assoc]
        gcongr
        have : (q : ℝ) * L ≤ N + L := by
          have h1 : (N / L) * L ≤ N := Nat.div_mul_le_self N L
          have : ((N / L : ℕ) : ℝ) * L ≤ N := by exact_mod_cast h1
          simp only [q]; push_cast; linarith
        simpa [L] using this

/-- The Riesz majorant of `|μ̂(ξ)|` (`charFun_norm_le`). -/
noncomputable def Bf (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range M).filter (fun p => free p = true), |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))|

theorem Bf_nonneg (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : 0 ≤ Bf free M ξ :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem Bf_le_one (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : Bf free M ξ ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _

theorem Bf_neg (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : Bf free M (-ξ) = Bf free M ξ := by
  unfold Bf
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [mul_neg, neg_div, Real.cos_neg]

theorem Bf_le_Hf (free : ℕ → Bool) (v k : ℕ) (u : ℝ) :
    Bf free (v + k) (3 ^ v * u) ≤ Hf free v k u := by
  unfold Bf Hf
  have hsub : posSet free v k ⊆ (Finset.range (v + k)).filter (fun p => free p = true) := by
    intro p hp; simp only [posSet, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ p ∈ (Finset.range (v + k)).filter (fun p => free p = true) \ posSet free v k,
      |Real.cos (2 * Real.pi * (3 ^ v * u) / 3 ^ (p + 1))| ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _
  have h2 : 0 ≤ ∏ p ∈ posSet free v k, |Real.cos (2 * Real.pi * (3 ^ v * u) / 3 ^ (p + 1))| :=
    Finset.prod_nonneg fun _ _ => abs_nonneg _
  nlinarith

theorem freeCount_le (free : ℕ → Bool) (v k : ℕ) :
    freeCount free (v + k) ≤ v + 1 + (posSet free v k).card := by
  unfold freeCount posSet
  have : (Finset.range (v + k)).filter (fun i => free i = true) ⊆
      Finset.range (v + 1) ∪ (Finset.range (v + k)).filter fun p => v + 1 ≤ p ∧ free p = true := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hp ⊢
    by_cases h : p < v + 1
    · exact Or.inl h
    · exact Or.inr ⟨hp.1, by omega, hp.2⟩
  refine (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans ?_)
  simp

/-- **Good shifts.**  If `v₃(c)` is small compared with the free count, the orbit sum of the
majorant saves `(2/3)^{F/2}`. -/
theorem good_shift (free : ℕ → Bool) (M N : ℕ) (hMN : 3 ^ M ≤ N) (c : ℕ) (hc : c ≠ 0)
    (hv : padicValNat 3 c + 1 ≤ freeCount free M / 2) :
    ∑ b ∈ Finset.range N, Bf free M ((c * 2 ^ b : ℕ) : ℝ) ≤
      2 * N * (2 / 3 : ℝ) ^ (freeCount free M / 2) := by
  obtain ⟨v, c', hc', hcc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc 3 (by norm_num)
  have hvv : padicValNat 3 c = v := by
    rw [hcc, padicValNat.mul (by positivity) (by rintro rfl; simp at hc'),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hc', add_zero]
  rw [hvv] at hv
  have hFM : freeCount free M ≤ M := by
    unfold freeCount; exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨j, hj⟩ : ∃ j, M = v + (j + 1) := ⟨M - v - 1, by omega⟩
  have hterm : ∀ b, Bf free M ((c * 2 ^ b : ℕ) : ℝ) ≤ Hf free v (j + 1) ((c' * 2 ^ b : ℕ) : ℝ) := by
    intro b
    have := Bf_le_Hf free v (j + 1) ((c' * 2 ^ b : ℕ) : ℝ)
    rw [← hj] at this
    refine le_of_eq_of_le ?_ this
    congr 1; rw [hcc]; push_cast; ring
  have hcard := freeCount_le free v (j + 1)
  rw [← hj] at hcard
  have hL : (2 * 3 ^ j : ℝ) ≤ N := by
    have : 2 * 3 ^ j ≤ 3 ^ M := by
      rw [hj, pow_add, pow_succ]; nlinarith [Nat.one_le_pow v 3 (by norm_num), Nat.one_le_pow j 3 (by norm_num)]
    exact_mod_cast this.trans hMN
  calc _ ≤ ∑ b ∈ Finset.range N, Hf free v (j + 1) ((c' * 2 ^ b : ℕ) : ℝ) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ ≤ (N + 2 * 3 ^ j) * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card := sum_Hf_le free v j c' hc' N
    _ ≤ (2 * N) * (2 / 3 : ℝ) ^ (freeCount free M / 2) := by
        gcongr ?_ * ?_
        · linarith
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem tri_sum_le (G : ℕ → ℕ → ℝ) (hG : ∀ d b, 0 ≤ G d b) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if m < n then G (n - m) m else 0) ≤
      ∑ d ∈ Finset.Ico 1 N, ∑ b ∈ Finset.range N, G d b := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.Ico 1 N)]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image (f := fun d => G d m) (g := fun n => n - m)]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _ _
    intro d hd
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨n, ⟨hn, hmn⟩, rfl⟩ := hd
    simp only [Finset.mem_Ico]; omega
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    simp only at hab; omega

theorem pair_sum_le (Φ : ℕ → ℕ → ℝ) (G : ℕ → ℕ → ℝ) (hG : ∀ d b, 0 ≤ G d b)
    (hd : ∀ n, Φ n n ≤ 1) (hlt : ∀ n m, m < n → Φ n m ≤ G (n - m) m)
    (hgt : ∀ n m, n < m → Φ n m ≤ G (m - n) n) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, Φ n m ≤
      N + 2 * ∑ d ∈ Finset.Ico 1 N, ∑ b ∈ Finset.range N, G d b := by
  have hsplit : ∀ n m, Φ n m ≤ (if m < n then G (n - m) m else 0) + (if n = m then 1 else 0) +
      (if n < m then G (m - n) n else 0) := by
    intro n m
    rcases lt_trichotomy m n with h | h | h
    · simp [h, h.ne', not_lt.2 h.le, hlt n m h]
    · subst h; simp [hd]
    · simp [h, h.ne, not_lt.2 h.le, hgt n m h]
  calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((if m < n then G (n - m) m else 0) + (if n = m then 1 else 0) +
          (if n < m then G (m - n) n else 0)) :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hsplit n m
    _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if m < n then G (n - m) m else 0) + N +
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (if n < m then G (m - n) n else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun n m => if n < m then G (m - n) n else 0)]
        congr 1
        congr 1
        simp
        rw [Finset.filter_true_of_mem fun x hx => Finset.mem_range.1 hx, Finset.card_range]
    _ ≤ _ := by
        have := tri_sum_le G hG N
        linarith

theorem bad_count (e W N : ℕ) :
    ((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 3 (2 ^ m - 1))).card ≤
      N / 3 ^ (W - e - 1) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card ?_
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hm ⊢
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rcases Nat.lt_or_ge (W - e) 2 with hr | hr
  · rw [show W - e - 1 = 0 by omega, pow_zero]; exact one_dvd _
  · obtain ⟨r, hr'⟩ : ∃ r, W - e = r + 1 + 1 := ⟨W - e - 2, by omega⟩
    have hne : 2 ^ m - 1 ≠ 0 := by
      have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
      omega
    have h3 : 3 ^ (r + 1 + 1) ∣ 2 ^ m - 1 :=
      (padicValNat_dvd_iff_le hne).2 (by omega)
    rw [← two_pow_eq_one_iff, ← orderOf_dvd_iff_pow_eq_one, orderOf_two_zmod_three_pow] at h3
    rw [show W - e - 1 = r + 1 by omega]
    exact (Dvd.intro_left _ rfl).trans h3

theorem Bf_abs (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : Bf free M |ξ| = Bf free M ξ := by
  rcases abs_cases ξ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]; rw [Bf_neg]

/-- Expansion of the second moment into Riesz majorants. -/
theorem secondMoment_expand (free : ℕ → Bool) (h : ℤ) (M N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, Bf free M (h * ((2 : ℝ) ^ n - 2 ^ m)) := by
  have hG := measurable_pt free
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * pt free ω)) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * pt free ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((2 : ℝ) ^ n - 2 ^ m)) * pt free ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * 2 ^ k * pt free ω)]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * pt free ω)‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((2 : ℝ) ^ n - 2 ^ m)) * pt free ω) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  refine Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun m _ => charFun_real M free _

theorem pow_two_sub_le (W : ℕ) (F : ℕ) (hW : W = F / 2) :
    (2 / 3 : ℝ) ^ W ≤ 3 / 2 * Real.exp (-(Real.log (3 / 2) / 2) * F) := by
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have h1 : (2 / 3 : ℝ) ^ W = Real.exp (-(W * Real.log (3 / 2))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
      show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
    ring_nf
  have hWF : (F : ℝ) ≤ 2 * W + 1 := by
    have : F ≤ 2 * W + 1 := by omega
    exact_mod_cast this
  rw [h1, show (3 / 2 : ℝ) = Real.exp (Real.log (3 / 2)) by rw [Real.exp_log (by norm_num)],
    ← Real.exp_add, Real.exp_log (by norm_num)]
  apply Real.exp_le_exp.2
  nlinarith

/-! ### The exact digit-change identity -/

/-- Natural ternary digit. -/
def dg (w k : ℕ) : ℕ := w / 3 ^ k % 3

/-- Digit changes of a natural number at pairs `(k, k+1)`, `k ∈ Q`. -/
def chg (w : ℕ) (Q : Finset ℕ) : ℕ := (Q.filter fun k => dg w (k + 1) ≠ dg w k).card

theorem dg_add_low {w n t k : ℕ} (hw : w < 3 ^ n) (hk : k < n) : dg (3 ^ n * t + w) k = dg w k := by
  unfold dg
  have : 3 ^ n = 3 ^ k * 3 ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc, add_comm, Nat.add_mul_div_left _ _ (by positivity)]
  obtain ⟨r, hr⟩ : ∃ r, n - k = r + 1 := ⟨n - k - 1, by omega⟩
  rw [hr, pow_succ]
  have h0 : 3 ^ r * (3 * t) % 3 = 0 := by rw [mul_left_comm]; exact Nat.mul_mod_right 3 _
  simp [mul_assoc, Nat.add_mod, h0]

theorem dg_add_top {w n t : ℕ} (hw : w < 3 ^ n) (ht : t < 3) : dg (3 ^ n * t + w) n = t := by
  unfold dg
  rw [add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hw, zero_add,
    Nat.mod_eq_of_lt ht]

theorem chg_add (w n t : ℕ) (hw : w < 3 ^ (n + 1)) (ht : t < 3) (Q : Finset ℕ)
    (hQ : ∀ k ∈ Q, k + 1 ≤ n + 1) :
    chg (3 ^ (n + 1) * t + w) Q = chg w (Q.erase n) +
      (if n ∈ Q ∧ t ≠ dg w n then 1 else 0) := by
  unfold chg
  have hsplit : Q.filter (fun k => dg (3 ^ (n + 1) * t + w) (k + 1) ≠ dg (3 ^ (n + 1) * t + w) k) =
      (Q.erase n).filter (fun k => dg w (k + 1) ≠ dg w k) ∪
        (if n ∈ Q ∧ t ≠ dg w n then {n} else ∅) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ⟨hk, hne⟩
      by_cases hkn : k = n
      · subst hkn
        right
        rw [dg_add_top hw ht, dg_add_low hw (by omega)] at hne
        rw [if_pos ⟨hk, hne⟩]; simp
      · left
        have hk1 := hQ k hk
        rw [dg_add_low hw (by omega), dg_add_low hw (by omega)] at hne
        exact ⟨⟨hkn, hk⟩, hne⟩
    · rintro (⟨⟨hkn, hk⟩, hne⟩ | h)
      · have hk1 := hQ k hk
        refine ⟨hk, ?_⟩
        rw [dg_add_low hw (by omega), dg_add_low hw (by omega)]; exact hne
      · split_ifs at h with hc
        · simp at h; subst h
          refine ⟨hc.1, ?_⟩
          rw [dg_add_top hw ht, dg_add_low hw (by omega)]; exact hc.2
        · simp at h
  rw [hsplit, Finset.card_union_of_disjoint]
  · split_ifs <;> simp
  · split_ifs
    · simp
    · simp

theorem sum_units_pow_chg (θ : ℝ) : ∀ n : ℕ, ∀ Q : Finset ℕ, (∀ k ∈ Q, k + 1 ≤ n) →
    ∑ w ∈ Finset.range (3 ^ (n + 1)), (if 3 ∣ w then 0 else θ ^ chg w Q) =
      2 * 3 ^ n * ((1 + 2 * θ) / 3) ^ Q.card := by
  intro n
  induction n with
  | zero =>
    intro Q hQ
    have : Q = ∅ := Finset.eq_empty_of_forall_notMem fun k hk => by have := hQ k hk; omega
    subst this
    simp [chg, Finset.sum_range_succ]; norm_num
  | succ n ih =>
    intro Q hQ
    rw [show 3 ^ (n + 1 + 1) = 3 ^ (n + 1) * 3 by ring, sum_range_mul_eq, Finset.sum_comm]
    have hw : ∀ w ∈ Finset.range (3 ^ (n + 1)),
        ∑ t ∈ Finset.range 3, (if 3 ∣ 3 ^ (n + 1) * t + w then (0:ℝ) else
          θ ^ chg (3 ^ (n + 1) * t + w) Q) =
        (if n ∈ Q then 1 + 2 * θ else 3) * (if 3 ∣ w then 0 else θ ^ chg w (Q.erase n)) := by
      intro w hw
      simp only [Finset.mem_range] at hw
      simp only [three_dvd_add_iff (n + 1) _ w (by omega)]
      by_cases h3 : 3 ∣ w
      · simp [h3]
      simp only [h3, if_false]
      have hd : dg w n < 3 := Nat.mod_lt _ (by norm_num)
      rw [Finset.sum_congr rfl fun t ht => by
        rw [chg_add w n t hw (Finset.mem_range.1 ht) Q hQ, pow_add]]
      rw [← Finset.mul_sum, mul_comm]
      congr 1
      by_cases hn : n ∈ Q
      · simp only [hn, true_and, if_true]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        interval_cases h : dg w n <;> simp <;> ring
      · simp [hn]
    rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
    have hQ' : ∀ k ∈ Q.erase n, k + 1 ≤ n := by
      intro k hk; rw [Finset.mem_erase] at hk; have := hQ k hk.2; omega
    rw [ih _ hQ']
    by_cases hn : n ∈ Q
    · rw [if_pos hn, ← Finset.card_erase_add_one hn, pow_succ, pow_succ]
      ring
    · rw [if_neg hn, Finset.erase_eq_of_notMem hn, pow_succ]; ring

theorem tdig_eq_dg (X : ℤ) {k M : ℕ} (hk : k ≤ M) :
    tdig X k = (dg ((X % 3 ^ (M + 1)).toNat) k : ℤ) := by
  have hP : (0 : ℤ) < 3 ^ (M + 1) := by positivity
  have hr0 : 0 ≤ X % 3 ^ (M + 1) := Int.emod_nonneg _ hP.ne'
  unfold dg tdig
  push_cast
  rw [Int.toNat_of_nonneg hr0]
  have key : ∀ q r : ℤ, (3 ^ (M + 1) * q + r) / 3 ^ k % 3 = r / 3 ^ k % 3 := by
    intro q r
    have : (3 : ℤ) ^ (M + 1) = 3 ^ k * (3 * 3 ^ (M - k)) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [this, add_comm, mul_assoc, Int.add_mul_ediv_left _ _ (by positivity), mul_assoc,
      Int.add_mul_emod_self_left]
  conv_lhs => rw [← Int.mul_ediv_add_emod X (3 ^ (M + 1))]
  exact key _ _

theorem tdig_pow_mul (X : ℤ) {v i : ℕ} (h : v ≤ i) : tdig (3 ^ v * X) i = tdig X (i - v) := by
  unfold tdig
  have : (3 : ℤ) ^ i = 3 ^ v * 3 ^ (i - v) := by rw [← pow_add]; congr 1; omega
  rw [this, Int.mul_ediv_mul_of_pos _ _ (by positivity)]

theorem isUnit_intCast_of_not_dvd (c : ℤ) (hc : ¬ (3 : ℤ) ∣ c) (M : ℕ) :
    IsUnit (c : ZMod (3 ^ (M + 1))) := by
  have hcop : Nat.Coprime c.natAbs (3 ^ (M + 1)) := by
    refine Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_).symm
    intro h; exact hc (Int.natCast_dvd.2 h)
  have hu := (ZMod.unitOfCoprime _ hcop).isUnit
  rcases Int.natAbs_eq c with h | h
  · rw [h]; simpa using hu
  · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg

/-- **Digit changes are i.i.d. over a full period** (exact identity).  Confidence 93%.

English proof.  Let `v = v₃(c)`, `c = 3^v c'` with `3 ∤ c'`.  By `orderOf_two_zmod_three_pow`,
as `j` runs over `[0, 2·3^M)`, `c' 2ʲ mod 3^{M+1−v}` takes every unit value exactly `3^v`
times.  Units `u < 3^{n}` correspond bijectively to (digit 0 ∈ {1,2}, digits `1..n−1` ∈
{0,1,2}^{n−1}), so digits `1..M−v` of `u` are i.i.d. uniform.  Digit `i` of `c·2ʲ`, for
`v < i ≤ M`, is digit `i − v ≥ 1` of `u` (Euclidean division is compatible with reduction
mod `3^{M+1}`).  The pairs `(i, i+1)`, `i ∈ P`, are disjoint (`hsep`) and lie in
`(v, M]`, so the change indicators are independent with `P(change) = 6/9`, and
`𝔼 θ^{changes} = Π_{i∈P} (1/3 + 2θ/3)`.  Probe: `probes/cantorliou_changes_probe.py`
(236 exact rational cases, all equal; the base-3 sibling differs). -/
theorem sum_pow_changes (c : ℤ) (hc : c ≠ 0) (M : ℕ) (P : Finset ℕ)
    (hlo : ∀ i ∈ P, padicValInt 3 c < i) (hhi : ∀ i ∈ P, i + 1 ≤ M)
    (hsep : ∀ i ∈ P, ∀ i' ∈ P, i < i' → i + 2 ≤ i') (θ : ℝ) :
    ∑ j ∈ Finset.range (2 * 3 ^ M), θ ^ changes (c * 2 ^ j) P =
      2 * 3 ^ M * ((1 + 2 * θ) / 3) ^ P.card := by
  -- c = 3^v c'
  obtain ⟨v, m, hm, hcm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hc) 3 (by norm_num)
  have hv : padicValInt 3 c = v := by
    rw [padicValInt, hcm, padicValNat.mul (by positivity) (by rintro rfl; simp at hm),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [hv] at hlo
  set c' : ℤ := c.sign * m
  have hcc : c = 3 ^ v * c' := by
    conv_lhs => rw [← Int.sign_mul_natAbs c, hcm]
    push_cast; ring
  have hc' : ¬ (3 : ℤ) ∣ c' := by
    intro h
    have : (3 : ℤ) ∣ (m : ℤ) := by
      rcases Int.sign_trichotomy c with h1 | h1 | h1
      · simpa [c', h1] using h
      · exact absurd (Int.sign_eq_zero_iff_zero.1 h1) hc
      · simpa [c', h1] using h
    exact hm (Int.natCast_dvd_natCast.1 this)
  set n := 3 ^ (M + 1)
  set w : ℕ → ℕ := fun j => ((c' * 2 ^ j) % n).toNat
  set Q := P.image (fun i => i - v)
  have hQ : ∀ k ∈ Q, k + 1 ≤ M := by
    intro k hk; simp only [Q, Finset.mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk; have := hhi i hi; omega
  have hinjP : Set.InjOn (fun i => i - v) (P : Set ℕ) := by
    intro a ha b hb hab; have := hlo a ha; have := hlo b hb; simp only at hab; omega
  have hcardQ : Q.card = P.card := Finset.card_image_of_injOn hinjP
  have hch : ∀ j, changes (c * 2 ^ j) P = chg (w j) Q := by
    intro j
    unfold changes chg
    simp only [Q]
    rw [Finset.filter_image, Finset.card_image_of_injOn (hinjP.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))]
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    have h1 := hlo i hi; have h2 := hhi i hi
    rw [hcc, mul_assoc, tdig_pow_mul _ (by omega), tdig_pow_mul _ (by omega),
      tdig_eq_dg _ (M := M) (by omega), tdig_eq_dg _ (M := M) (by omega)]
    simp only [w, show i + 1 - v = i - v + 1 by omega]
    exact_mod_cast Iff.rfl
  simp_rw [hch]
  rw [← hcardQ, ← sum_units_pow_chg θ M Q hQ]
  have hfl : ∑ u ∈ Finset.range n, (if 3 ∣ u then 0 else θ ^ chg u Q) =
      ∑ u ∈ (Finset.range n).filter (fun u => ¬ 3 ∣ u), θ ^ chg u Q := by
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun u _ => ?_; split_ifs <;> simp_all
  rw [hfl]
  have hP : (0 : ℤ) < n := by positivity
  have hcast : ∀ j, ((w j : ℕ) : ZMod n) = (c' : ZMod n) * 2 ^ j := by
    intro j
    simp only [w]
    have h0 : 0 ≤ c' * 2 ^ j % n := Int.emod_nonneg _ hP.ne'
    rw [show ((((c' * 2 ^ j) % n).toNat : ℕ) : ZMod n) = (((c' * 2 ^ j) % n : ℤ) : ZMod n) by
      rw [← Int.toNat_of_nonneg h0]; simp [h0]]
    rw [ZMod.intCast_mod]; push_cast; ring
  have hord := orderOf_two_zmod_three_pow M
  have hfin : IsOfFinOrder (2 : ZMod n) := orderOf_pos_iff.1 (by rw [hord]; positivity)
  have hu := isUnit_intCast_of_not_dvd c' hc' M
  have hinj : Set.InjOn w (Finset.range (2 * 3 ^ M) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 := congrArg (fun x : ℕ => (x : ZMod n)) hab
    simp only [hcast] at h1
    have h2 := hu.mul_left_cancel h1
    rw [hfin.pow_inj_mod, hord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
    exact h2
  have hmaps : Set.MapsTo w (Finset.range (2 * 3 ^ M) : Set ℕ)
      ((Finset.range n).filter fun u => ¬ 3 ∣ u : Finset ℕ) := by
    intro j _
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    have h0 : 0 ≤ c' * 2 ^ j % n := Int.emod_nonneg _ hP.ne'
    have hlt : c' * 2 ^ j % n < n := Int.emod_lt_of_pos _ hP
    refine ⟨by simp only [w]; omega, fun h3 => ?_⟩
    have h3' : (3 : ℤ) ∣ c' * 2 ^ j % n := by
      have := Int.natCast_dvd_natCast.2 h3; simp only [w] at this
      rwa [Int.toNat_of_nonneg h0] at this
    have h3n : (3 : ℤ) ∣ n := by simp only [n]; push_cast; exact dvd_pow_self 3 (Nat.succ_ne_zero M)
    have : (3 : ℤ) ∣ c' * 2 ^ j := by
      rw [← Int.mul_ediv_add_emod (c' * 2 ^ j) n, add_comm]
      exact dvd_add h3' (Dvd.dvd.mul_right h3n _)
    rcases (Int.prime_three.dvd_or_dvd this) with h | h
    · exact hc' h
    · have := Int.prime_three.dvd_of_dvd_pow h; norm_num at this
  refine Finset.sum_nbij w (fun b hb => hmaps hb) hinj ?_ (fun _ _ => rfl)
  exact Finset.surjOn_of_injOn_of_card_le _ hmaps hinj
    (by rw [card_units_range, Finset.card_range])

/-- **The quantitative Cassels lemma** (the content of the campaign).  Confidence 85%.

English proof.  `𝔼‖S_N‖² = Σ_{a,b<N} μ̂(h(2ᵃ − 2ᵇ))`; the diagonal gives `N`.  For `m = a − b > 0`
write `ξ = c_m 2ᵇ`, `c_m = h(2ᵐ − 1)`, `v_m = v₃(c_m) ≤ v₃(h) + 1 + v₃(m)` (LTE).  Let
`M = ⌊log₃ N⌋/2`, so the period `2·3^{M−1} ≤ √N`, and `F = freeCount free M`, `V = F/2`.
* Pairs with `v_m ≥ V`: then `3^{V − v₃(h) − 1} ∣ m`, at most `N·3^{−(V − v₃(h) − 1)}` values of
  `m`, each with `≤ N` values of `b`: total `≤ C_h N² 3^{−F/2}`.
* Pairs with `v_m < V`: free positions `p ∈ (v_m + 1, M)` number `≥ F/2 − 2`; keep every other
  one, `P = {p − 1}` (`≥ F/4 − 1` elements, 2-separated).  By `charFun_norm_le` and
  `abs_cos_le_of_tdig_ne`, `|μ̂(c_m 2ᵇ)| ≤ θ^{changes(c_m 2ᵇ, P)}` with `θ = cos(π/9)`.  Sum over
  `b < N − m` in full periods (`sum_pow_changes` at modulus `3^M`), plus one partial period
  `≤ √N`: `≤ (N − m) ρ^{F/4 − 1} + √N`, `ρ = (1 + 2θ)/3 < 1`.  Summed over `m`:
  `≤ N² ρ^{F/4−1} + N^{3/2}`.
Altogether `≤ N + 2(C_h N² (3^{−F/2} + ρ^{F/4−1}) + N^{3/2}) ≤ C N² (exp(−cF) + N^{−1/2})`.

Degenerate checks: `free ≡ false` makes the right side `≥ C N²`, trivially true (`pt = 0`,
`𝔼‖S_N‖² = N²`, so `C ≥ 1` is forced and allowed); `free ≡ true` is Cassels 1959. -/
theorem secondMoment_le (free : ℕ → Bool) (h : ℤ) (hh : h ≠ 0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
        C * (N : ℝ) ^ 2 *
          (Real.exp (-c * freeCount free (Nat.log 3 N / 2)) + (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  set e := padicValNat 3 h.natAbs
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  refine ⟨1 + 3 * (3 ^ (e + 1) + 2), Real.log (3 / 2) / 2, by positivity, by positivity,
    fun N hN => ?_⟩
  set M := Nat.log 3 N / 2
  set F := freeCount free M
  set W := F / 2
  have hMN : 3 ^ M ≤ N :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
      (Nat.pow_log_le_self 3 (by omega))
  set G : ℕ → ℕ → ℝ := fun d b => Bf free M (h * ((2 : ℝ) ^ d - 1) * 2 ^ b)
  have hpair := pair_sum_le (fun n m => Bf free M (h * ((2 : ℝ) ^ n - 2 ^ m))) G
    (fun d b => Bf_nonneg _ _ _) (fun n => Bf_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← Bf_neg]; congr 1
      rw [show (2 : ℝ) ^ m = 2 ^ (m - n) * 2 ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  -- per-shift bound
  have hshift : ∀ d ∈ Finset.Ico 1 N, ∑ b ∈ Finset.range N, G d b ≤
      (if W ≤ e + padicValNat 3 (2 ^ d - 1) then (N : ℝ) else 0) +
        2 * N * (2 / 3 : ℝ) ^ W := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd1 : 1 ≤ 2 ^ d - 1 := by
      have : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2
      omega
    split_ifs with hbad
    · refine (Finset.sum_le_sum fun b _ => Bf_le_one free M _).trans ?_
      have : (0 : ℝ) ≤ 2 * N * (2 / 3 : ℝ) ^ W := by positivity
      simp; linarith
    · rw [zero_add]
      set c := h.natAbs * (2 ^ d - 1)
      have hc : c ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.2 hh) (by omega)
      have hv : padicValNat 3 c = e + padicValNat 3 (2 ^ d - 1) :=
        padicValNat.mul (Int.natAbs_ne_zero.2 hh) (by omega)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun b _ => ?_)
        (good_shift free M N hMN c hc (by omega))
      simp only [G]
      rw [← Bf_abs]
      congr 1
      have hd2 : (0 : ℝ) ≤ 2 ^ d - 1 := by
        have : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num); linarith
      simp only [c]
      push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 ^ b),
        abs_of_nonneg hd2, Nat.cast_natAbs, Int.cast_abs]
  have hsumd : ∑ d ∈ Finset.Ico 1 N, ∑ b ∈ Finset.range N, G d b ≤
      N * ((N / 3 ^ (W - e - 1) : ℕ) : ℝ) + N * (2 * N * (2 / 3 : ℝ) ^ W) := by
    refine (Finset.sum_le_sum hshift).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico]
    have hb := bad_count e W N
    have : (((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 3 (2 ^ m - 1))).card : ℝ) ≤
        ((N / 3 ^ (W - e - 1) : ℕ) : ℝ) := by exact_mod_cast hb
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have : (0 : ℝ) ≤ 2 * N * (2 / 3 : ℝ) ^ W := by positivity
    nlinarith
  have hdiv : ((N / 3 ^ (W - e - 1) : ℕ) : ℝ) ≤ N * 3 ^ (e + 1) * (2 / 3 : ℝ) ^ W := by
    have h1 : (N / 3 ^ (W - e - 1)) * 3 ^ W ≤ N * 3 ^ (e + 1) := by
      calc (N / 3 ^ (W - e - 1)) * 3 ^ W ≤ (N / 3 ^ (W - e - 1)) * (3 ^ (W - e - 1) * 3 ^ (e + 1)) := by
            gcongr; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (N / 3 ^ (W - e - 1)) * 3 ^ (W - e - 1) * 3 ^ (e + 1) := by ring
        _ ≤ N * 3 ^ (e + 1) := by gcongr; exact Nat.div_mul_le_self _ _
    have h2 : ((N / 3 ^ (W - e - 1) : ℕ) : ℝ) * 3 ^ W ≤ N * 3 ^ (e + 1) := by exact_mod_cast h1
    have h3 : (2 / 3 : ℝ) ^ W * 3 ^ W = 2 ^ W := by rw [← mul_pow]; norm_num
    have h4 : (1 : ℝ) ≤ 2 ^ W := one_le_pow₀ (by norm_num)
    have h5 : (0 : ℝ) < 3 ^ W := by positivity
    rw [← mul_le_mul_iff_of_pos_right h5]
    calc _ ≤ (N : ℝ) * 3 ^ (e + 1) := h2
      _ ≤ (N : ℝ) * 3 ^ (e + 1) * 2 ^ W := le_mul_of_one_le_right (by positivity) h4
      _ = _ := by rw [mul_assoc _ ((2 / 3 : ℝ) ^ W), h3]
  have hexp := pow_two_sub_le W F rfl
  have hNr : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = N * N ^ (1 : ℝ) by rw [Real.rpow_one]; ring, mul_assoc,
        ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN0 (by norm_num)
    nlinarith
  have hI := (secondMoment_expand free h M N).trans hpair
  set E := Real.exp (-(Real.log (3 / 2) / 2) * F)
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  set P := (2 / 3 : ℝ) ^ W
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR : 0 ≤ R := by positivity
  have hP : 0 ≤ P := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h3e : (1 : ℝ) ≤ 3 ^ (e + 1) := one_le_pow₀ (by norm_num)
  -- I ≤ N + 2 (N * N * 3^{e+1} P + 2 N² P)
  have hfin : ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + 1) + 2) * P) := by
    have := mul_le_mul_of_nonneg_left hdiv hN0
    nlinarith
  calc _ ≤ N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + 1) + 2) * P) := hfin
    _ ≤ (N : ℝ) ^ 2 * R + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + 1) + 2) * (3 / 2 * E)) := by
        gcongr
    _ ≤ _ := by
        have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
        nlinarith [mul_nonneg hN2 hE, mul_nonneg hN2 hR, mul_nonneg (mul_nonneg hN2 hR) (by positivity : (0:ℝ) ≤ 3 ^ (e + 1) + 2)]

/-! ## Davenport–Erdős–LeVeque along a slow schedule -/

theorem tendsto_of_tendsto_sched (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1) (n : ℕ → ℕ) (hn : StrictMono n)
    (hratio : Tendsto (fun j => (n (j + 1) : ℝ) / n j) atTop (𝓝 1))
    (h : Tendsto (fun j : ℕ => ‖∑ k ∈ Finset.range (n j), z k‖ / (n j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, z k) / (N : ℂ)) atTop (𝓝 0) := by
  set S : ℕ → ℂ := fun N => ∑ k ∈ Finset.range N, z k
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  have h1 := Metric.tendsto_atTop.1 h (ε / 2) (by positivity)
  have h2 := Metric.tendsto_atTop.1 hratio (ε / 2) (by positivity)
  obtain ⟨J1, hJ1⟩ := h1
  obtain ⟨J2, hJ2⟩ := h2
  set J := max (max J1 J2) 1
  refine ⟨n J, fun N hN => ?_⟩
  have hex : ∃ j, N < n (j + 1) := ⟨N, lt_of_lt_of_le (Nat.lt_succ_self N) (hn.id_le (N + 1) : N + 1 ≤ n (N + 1))⟩
  classical
  set j := Nat.find hex
  have hj1 : N < n (j + 1) := Nat.find_spec hex
  have hJj : J ≤ j := by
    by_contra hc
    push_neg at hc
    have : n (j + 1) ≤ n J := hn.monotone (by omega)
    omega
  have hjN : n j ≤ N := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · omega
    · have hm : ¬ N < n (j - 1 + 1) := Nat.find_min hex (by omega)
      rw [Nat.sub_add_cancel hpos] at hm; omega
  have hnj : (1 : ℝ) ≤ n j := by
    have : 1 ≤ n j := le_trans (by omega : 1 ≤ j) (hn.id_le j : j ≤ n j); exact_mod_cast this
  have hdiff : ‖S N - S (n j)‖ ≤ (N - n j : ℕ) := by
    have : S N - S (n j) = ∑ k ∈ Finset.Ico (n j) N, z k := by
      simp only [S]; rw [Finset.sum_range_sub_sum_range hjN]
      congr 1; ext k; simp [Finset.mem_Ico]; omega
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hz k).trans ?_
    simp
  have hA := hJ1 j (by omega)
  have hB := hJ2 j (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hA
  rw [Real.dist_eq, abs_lt] at hB
  have hNR : (n j : ℝ) ≤ N := by exact_mod_cast hjN
  have hNR2 : (N : ℝ) < n (j + 1) := by exact_mod_cast hj1
  have hdR : ((N - n j : ℕ) : ℝ) = N - n j := by push_cast [hjN]; ring
  rw [hdR] at hdiff
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), norm_div, Complex.norm_natCast]
  have hSN : ‖S N‖ ≤ ‖S (n j)‖ + (N - n j) := by
    have := norm_le_insert' (S N) (S (n j)); linarith
  have hq : (n (j + 1) : ℝ) < (1 + ε / 2) * n j := by
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < n j)).1 (by linarith : (n (j + 1) : ℝ) / n j < 1 + ε / 2)
    linarith
  rw [div_lt_iff₀ hNpos]
  have hA' : ‖S (n j)‖ < ε / 2 * n j := by
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < n j)).1 hA; linarith
  nlinarith

/-- **DEL along a schedule with ratio → 1.**  Confidence 97%.

English proof.  As in `DecayAeNormal.ae_tendsto_weyl`: the hypothesis makes
`Σ_j ‖S_{n j}(ω)‖²/(n j)²` integrable, hence a.e. finite, so `S_{n j}/n j → 0` a.s. for each
`h ≠ 0` (countably many).  For `n j ≤ N < n (j+1)`, `‖S_N/N − S_{n j}/N‖ ≤ (n(j+1) − n j)/n j
→ 0`, and `‖S_{n j}‖/N ≤ ‖S_{n j}‖/n j`; so `S_N/N → 0`.  Then `equidistributed_of_weyl` and
`isNormal_iff_equidistributed_orbit`, as in `ae_isNormal_two_of_decay`. -/
theorem ae_isNormal_two_of_secondMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Measurable G) (n : ℕ → ℕ) (hn : StrictMono n)
    (hratio : Tendsto (fun j => (n (j + 1) : ℝ) / n j) atTop (𝓝 1))
    (hsum : ∀ h : ℤ, h ≠ 0 → Summable fun j =>
      (∫ ω, ‖∑ k ∈ Finset.range (n j), ee (h * 2 ^ k * G ω)‖ ^ 2 ∂μ) / ((n j : ℝ) ^ 2)) :
    ∀ᵐ ω ∂μ, IsNormal 2 (G ω) := by
  have hone : ∀ h : ℤ, h ≠ 0 → ∀ᵐ ω ∂μ, Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    intro h hh
    set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω) with hSdef
    have hSm : ∀ N, Measurable (S N) := fun N =>
      Finset.measurable_sum _ fun k _ => measurable_ee.comp (hG.const_mul _)
    have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω =>
      (norm_sum_le _ _).trans (by simp [norm_ee])
    set f : ℕ → Ω → ℝ := fun j ω => ‖S (n j) ω‖ ^ 2 / ((n j : ℝ)) ^ 2 with hfdef
    have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
    have hfm : ∀ j, Measurable (f j) := fun j => (((hSm _).norm.pow_const 2).div_const _)
    have hfi : ∀ j, Integrable (f j) μ := fun j =>
      Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hf0 j ω)]
        rcases Nat.eq_zero_or_pos (n j) with h0 | hpos
        · simp [f, h0]
        · have hpos' : (0 : ℝ) < n j := by exact_mod_cast hpos
          rw [div_le_one (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
    have hfI : ∀ j, ∫ ω, f j ω ∂μ =
        (∫ ω, ‖∑ k ∈ Finset.range (n j), ee (h * 2 ^ k * G ω)‖ ^ 2 ∂μ) / ((n j : ℝ) ^ 2) := by
      intro j; simp only [f, S]; rw [integral_div]
    have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
        (r := ∑' j : ℕ, ∫ ω, f j ω ∂μ)) ?_
      have hs : Summable fun j => ∫ ω, f j ω ∂μ := by simp_rw [hfI]; exact hsum h hh
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hf0 j)) hs]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
      (hfm j).ennreal_ofReal.aemeasurable) hlin
    filter_upwards [hae] with ω hω
    have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
    have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
    have h3 : Tendsto (fun j : ℕ => ‖S (n j) ω‖ / (n j : ℝ)) atTop (𝓝 0) := by
      have := h2.sqrt
      rw [Real.sqrt_zero] at this
      refine this.congr fun j => ?_
      simp only [hfdef]
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)]
    exact tendsto_of_tendsto_sched (fun k => ee (h * 2 ^ k * G ω)) (fun k => (norm_ee _).le) n hn
      hratio h3
  have hall : ∀ᵐ ω ∂μ, ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun ω hne => absurd hh hne
    · filter_upwards [hone h hh] with ω hω _ using hω
  filter_upwards [hall] with ω hω
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  have := hω h hh
  refine this.congr fun N => ?_
  rw [fourierMean_orbit_two]

/-- The schedule `⌊exp √j⌋ + j`. -/
noncomputable def sched (j : ℕ) : ℕ := ⌊Real.exp (Real.sqrt j)⌋₊ + j

theorem sched_strictMono : StrictMono sched := by
  intro a b hab
  have : ⌊Real.exp (Real.sqrt a)⌋₊ ≤ ⌊Real.exp (Real.sqrt b)⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.2 (Real.sqrt_le_sqrt (by exact_mod_cast hab.le)))
  unfold sched
  omega

theorem one_le_sched (j : ℕ) : 1 ≤ sched j := by
  have : 1 ≤ ⌊Real.exp (Real.sqrt j)⌋₊ :=
    Nat.le_floor (by simp [Real.one_le_exp (Real.sqrt_nonneg _)])
  unfold sched
  omega

/-- **The schedule's ratio tends to `1`.**  Confidence 97%.

English proof.  `sched j = e^{√j}(1 + O(j e^{−√j}))` and `e^{√(j+1)}/e^{√j} = e^{√(j+1) − √j}`
with `√(j+1) − √j ≤ 1/(2√j) → 0`. -/
theorem sched_ratio :
    Tendsto (fun j => (sched (j + 1) : ℝ) / sched j) atTop (𝓝 1) := by
  have hs : Tendsto (fun j : ℕ => 1 / Real.sqrt j) atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => Real.sqrt j) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop.congr fun j => by simp
  have h2 : Tendsto (fun j : ℕ => 2 / (j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have hu : Tendsto (fun j : ℕ => Real.exp (1 / Real.sqrt j) * (1 + 2 / (j : ℝ))) atTop (𝓝 1) := by
    have := ((Real.continuous_exp.tendsto 0).comp hs).mul ((tendsto_const_nhds (x := (1:ℝ))).add h2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · refine Eventually.of_forall fun j => ?_
    have h0 : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    rw [le_div_iff₀ h0, one_mul]
    exact_mod_cast (sched_strictMono (Nat.lt_succ_self j)).le
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have h0 : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    rw [div_le_iff₀ h0]
    set E := Real.exp (Real.sqrt j)
    set q := Real.exp (1 / Real.sqrt j)
    have hsq : 0 < Real.sqrt j := Real.sqrt_pos.2 (by linarith)
    have hE1 : 1 ≤ E := Real.one_le_exp (Real.sqrt_nonneg _)
    have hq1 : 1 ≤ q := Real.one_le_exp (by positivity)
    have hEs : Real.exp (Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤ q * E := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (Real.sqrt j) ^ 2 = j := Real.sq_sqrt (by linarith)
      have h1 : (1 / Real.sqrt j + Real.sqrt j) ^ 2 = 1 / j + 2 + j := by
        field_simp; rw [this]; ring
      rw [h1]; push_cast
      have : 0 ≤ 1 / (j : ℝ) := by positivity
      linarith
    have hup : (sched (j + 1) : ℝ) ≤ q * E + (j + 1) := by
      unfold sched; push_cast
      have := Nat.floor_le (Real.exp_pos (Real.sqrt ((j + 1 : ℕ) : ℝ))).le
      push_cast at this hEs
      linarith
    have hlow : E - 1 + j ≤ (sched j : ℝ) := by
      unfold sched; push_cast
      have := Nat.lt_floor_add_one E
      linarith
    have hkey : (E - 1 + j) * (1 + 2 / j) ≥ E + j + 1 := by
      have : (E - 1 + j) * (2 / j) ≥ 2 := by
        rw [ge_iff_le, mul_div_assoc', le_div_iff₀ (by linarith)]; nlinarith
      nlinarith
    calc (sched (j + 1) : ℝ) ≤ q * E + (j + 1) := hup
      _ ≤ q * (E + j + 1) := by nlinarith
      _ ≤ q * ((E - 1 + j) * (1 + 2 / j)) := by gcongr
      _ ≤ q * ((sched j : ℝ) * (1 + 2 / j)) := by gcongr
      _ = _ := by ring

/-- **The runs keep a `1/log` fraction of free positions.**  Confidence 95%.

English proof.  For `M < a 0 = 4` all positions are free.  For `a k ≤ M < a (k+1)`: the block
`[(k+1)·a (k−1), a k)` (for `k ≥ 1`; `[0, 4)` for `k = 0`) is free and has `a k / 2` elements
(`≥ 4` for `k = 0`); if `M < (k+2) a k` this is `≥ M/(2(k+2))`, and if `M ≥ (k+2) a k` the free
block `[(k+2) a k, M)` adds `M − (k+2) a k`, again giving `≥ M/(2(k+2))`.  Finally
`a k ≥ 4^{k+1}`, so `k + 2 ≤ log₂ M + 2`. -/
theorem le_freeCount (M : ℕ) : M ≤ 2 * (Nat.log 2 M + 2) * freeCount isFree M := by
  rcases Nat.lt_or_ge M 4 with hM | hM
  · have := card_le_freeCount (s := 0) (e := M) (M := M) le_rfl
      (fun i _ h2 => isFree_gap (k := 0) (by simp [gapStart]) (by simp [runStart]; omega))
    simp only [Nat.sub_zero] at this
    nlinarith [Nat.zero_le (Nat.log 2 M)]
  have hex : ∃ k, M < runStart (k + 1) :=
    ⟨M, lt_of_lt_of_le (Nat.lt_two_pow_self) (two_pow_le_runStart _ |>.trans' (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ M)))⟩
  classical
  set k := Nat.find hex
  have hk1 : M < runStart (k + 1) := Nat.find_spec hex
  have hk0 : runStart k ≤ M := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp [runStart]; omega
    · have hm : ¬ M < runStart (k - 1 + 1) := Nat.find_min hex (by omega)
      rw [Nat.sub_add_cancel hpos] at hm; omega
  have hF := card_le_freeCount₂ (s := gapStart k) (e := runStart k) (s' := (k + 2) * runStart k)
    (M := M) (by nlinarith) hk0 (fun i h1 h2 => isFree_gap h1 h2)
    (fun i h1 h2 => isFree_after h1 (by omega))
  have hg := gap_size k
  have hlog : k ≤ Nat.log 2 M :=
    Nat.le_log_of_pow_le (by norm_num) ((two_pow_le_runStart k).trans hk0)
  have hmain : M ≤ 2 * (k + 2) * freeCount isFree M := by
    rcases Nat.lt_or_ge M ((k + 2) * runStart k) with hc | hc
    · have : M - (k + 2) * runStart k = 0 := by omega
      rw [this, add_zero] at hF
      nlinarith
    · obtain ⟨t, ht⟩ : ∃ t, M = (k + 2) * runStart k + t := ⟨M - (k + 2) * runStart k, by omega⟩
      have : M - (k + 2) * runStart k = t := by omega
      rw [this] at hF
      nlinarith
  calc M ≤ 2 * (k + 2) * freeCount isFree M := hmain
    _ ≤ _ := by gcongr

theorem ev_log_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε * x ^ r := by
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound hε, eventually_ge_atTop 0] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  exact (le_abs_self _).trans hx

theorem sqrt_sqrt_eq (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

theorem exp_neg_two_log (j : ℕ) (hj : 1 ≤ j) : Real.exp (-(2 * Real.log j)) = 1 / (j : ℝ) ^ 2 := by
  have : (0 : ℝ) < j := by exact_mod_cast hj
  rw [Real.exp_neg, show 2 * Real.log j = Real.log ((j : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity), one_div]

theorem summable_inv_sq_nat : Summable fun j : ℕ => 1 / (j : ℝ) ^ 2 :=
  Real.summable_one_div_nat_pow.2 (by norm_num)

theorem exp_sqrt_le_sched (j : ℕ) (hj : 1 ≤ j) : Real.exp (Real.sqrt j) ≤ sched j := by
  unfold sched; push_cast
  have := Nat.lt_floor_add_one (Real.exp (Real.sqrt j))
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  linarith

theorem log_three_lt : Real.log 3 < (7 / 5) := by
  have h : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

/-- `M_j = ⌊log₃ sched j⌋/2 ≥ √j/4` eventually. -/
theorem ev_M_ge : ∀ᶠ j : ℕ in atTop, Real.sqrt j / 4 ≤ ((Nat.log 3 (sched j) / 2 : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop 100] with j hj
  have hj1 : 1 ≤ j := by omega
  set n := sched j
  set L := Nat.log 3 n
  have hn : (0 : ℝ) < n := by exact_mod_cast one_le_sched j
  have hlt : (n : ℝ) < 3 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
  have hlog : Real.log n < (L + 1) * Real.log 3 := by
    have := Real.log_lt_log hn hlt
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hsq : Real.sqrt j ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn]; exact exp_sqrt_le_sched j hj1
  have h3 := log_three_lt
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hL : Real.sqrt j / (7 / 5) - 1 < L := by
    have : Real.sqrt j < (L + 1) * (7 / 5) := by nlinarith
    have : Real.sqrt j / (7 / 5) < L + 1 := by rw [div_lt_iff₀ (by norm_num)]; linarith
    linarith
  have hM : ((L : ℝ) - 1) / 2 ≤ ((L / 2 : ℕ) : ℝ) := by
    have : L ≤ 2 * (L / 2) + 1 := by omega
    have : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have h10 : 10 ≤ Real.sqrt j := by
    rw [show (10 : ℝ) = Real.sqrt 100 by rw [show (100:ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hj)
  linarith

/-- **The Cassels bound is summable along the schedule.**  Confidence 92%.

English proof.  With `N = sched j ≥ e^{√j} − 1` and `M = ⌊log₃ N⌋/2 ≥ √j/(2 ln 3) − 2`,
`le_freeCount` gives `freeCount ≥ M/(2(log₂ M + 2)) ≥ c₁ √j / log(j + 2)`, so the first term is
`≤ exp(−c c₁ √j / log(j+2))`, summable (it is `o(j^{-2})`).  The second is
`≤ (e^{√j} − 1)^{-1/2}`, summable. -/
theorem summable_sched_bound (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    Summable fun j => C * (Real.exp (-c * freeCount isFree (Nat.log 3 (sched j) / 2)) +
      (sched j : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine Summable.mul_left C (Summable.add ?_ ?_)
  · -- first term
    have hMt : Tendsto (fun j : ℕ => ((Nat.log 3 (sched j) / 2 : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono' atTop ev_M_ge ?_
      exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
    have hA : ∀ᶠ x : ℝ in atTop, Real.log x ≤ Real.log 2 / 2 * x ^ (1 / 2 : ℝ) ∧ 16 ≤ x :=
      (ev_log_le (by norm_num) (by positivity)).and (eventually_ge_atTop 16)
    have hA' := hMt.eventually hA
    have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 4) (ε := c / 8)
      (by norm_num) (by positivity))
    refine Summable.of_norm_bounded_eventually summable_inv_sq_nat ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hA', hB, ev_M_ge, eventually_ge_atTop 1] with j hjA hjB hjM hj1
    set M := Nat.log 3 (sched j) / 2
    set F := freeCount isFree M
    obtain ⟨hlogM, hM16⟩ := hjA
    have hMpos : (0 : ℝ) < M := by linarith
    have hsM : Real.sqrt M = (M : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    -- Nat.log 2 M + 2 ≤ √M
    have hl2 : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log M := by
      have : ((2 ^ Nat.log 2 M : ℕ) : ℝ) ≤ M := by
        exact_mod_cast Nat.pow_log_le_self 2 (by intro h; rw [h] at hMpos; simp at hMpos)
      have := Real.log_le_log (by positivity) this
      push_cast at this; rw [Real.log_pow] at this; exact this
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hsq4 : 4 ≤ Real.sqrt M := by
      rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hM16
    have hden : (Nat.log 2 M : ℝ) + 2 ≤ Real.sqrt M := by
      have : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log 2 / 2 * Real.sqrt M := by
        rw [hsM]; linarith
      have : (Nat.log 2 M : ℝ) ≤ Real.sqrt M / 2 := by nlinarith
      linarith
    have hF : Real.sqrt M / 2 ≤ F := by
      have h := le_freeCount M
      have h' : (M : ℝ) ≤ 2 * ((Nat.log 2 M : ℝ) + 2) * F := by exact_mod_cast h
      have hsMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hMpos.le
      have hF0 : (0 : ℝ) ≤ F := by positivity
      have hspos : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
      nlinarith
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hsqM : Real.sqrt (Real.sqrt j) / 2 ≤ Real.sqrt M := by
      have := Real.sqrt_le_sqrt hjM
      rw [Real.sqrt_div' _ (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
      exact this
    rw [sqrt_sqrt_eq _ hj0] at hsqM
    have hkey : 2 * Real.log j ≤ c * F := by
      have : c * ((j : ℝ) ^ (1 / 4 : ℝ) / 4) ≤ c * F := by
        apply mul_le_mul_of_nonneg_left _ hc.le; linarith
      linarith
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← exp_neg_two_log j hj1]
    apply Real.exp_le_exp.2; linarith
  · -- second term
    have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 2) (ε := 1 / 4)
      (by norm_num) (by norm_num))
    refine Summable.of_norm_bounded_eventually summable_inv_sq_nat ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hB, eventually_ge_atTop 1] with j hjB hj1
    have hs : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), ← exp_neg_two_log j hj1]
    calc (sched j : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (Real.exp (Real.sqrt j)) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (exp_sqrt_le_sched j hj1) (by norm_num)
      _ = Real.exp (-(Real.sqrt j / 2)) := by rw [← Real.exp_mul]; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          rw [Real.sqrt_eq_rpow]; linarith

/-- **Almost every Cantor–Liouville point is normal to base 2** (wiring, proved from the
leaves above). -/
theorem ae_isNormal_two :
    ∀ᵐ ω ∂coinMeasure, IsNormal 2 (cantorLiouvilleReal ω) := by
  refine ae_isNormal_two_of_secondMoment coinMeasure _ (measurable_pt isFree) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  obtain ⟨C, c, hC, hc, hb⟩ := secondMoment_le isFree h hh
  refine (summable_sched_bound C c hC hc).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := hb (sched j) (one_le_sched j)
    _ = _ := by ring

/-! ## Headlines -/

/-- **Bugeaud 2012, Problem 10.37.**  The middle-third Cantor set contains a Liouville number
that is normal to base 2.  (Wiring, proved from the leaves: a.e. coin sequence works.) -/
theorem exists_liouville_mem_cantorSet_isNormal_two :
    ∃ x : ℝ, x ∈ cantorSet ∧ Liouville x ∧ IsNormal 2 x := by
  obtain ⟨ω, hn, hf⟩ := (ae_isNormal_two.and ae_frequently_free).exists
  exact ⟨_, pt_mem_cantorSet _ _, liouville_cantorLiouvilleReal ω hf, hn⟩

/-- **Computable strengthening.**  Confidence 60%.

English proof (plan).  Derandomize with `Derandomize.exists_primrec_avoid`.  Test `j`
(`N = sched j`, frequencies `0 < |h| ≤ H_j`, `H_j → ∞` slowly): the Weyl mean of the
dyadic-rational approximation of `x` read from the first `L_j ≈ N log₃ 2 + O(log N)` coins
exceeds `ε_j`, decided exactly in rational arithmetic.  Chebyshev with `secondMoment_le` (its
constant is `≤ C·3^{v₃(h)} ≤ C|h|`) bounds the test's mass by
`ε_j^{-2} H_j² (exp(−c F) + N^{-1/2})`, summable for slowly chosen `ε_j, H_j`; a second test
family "no free `true` in the `j`-th free block" has mass `2^{-a j / 2}`.  An avoiding `e`
is computable, has Weyl means `→ 0` along `sched` at every `h` (eventually `|h| ≤ H_j`), hence
along all `N` (ratio → 1), and has infinitely many free `2`s (Liouville).  The missing engine is
the rate-generic replacement for `ComputableNormal`'s `n^{10}` schedule; see `HANDOFF`. -/
theorem exists_computable_liouville_mem_cantorSet_isNormal_two :
    ∃ e : ℕ → Bool, Computable e ∧ cantorLiouvilleReal e ∈ cantorSet ∧
      Liouville (cantorLiouvilleReal e) ∧ IsNormal 2 (cantorLiouvilleReal e) := by
  sorry

end NormalNumbers.CantorLiouville
