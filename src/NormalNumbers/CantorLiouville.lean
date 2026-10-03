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
  sorry

/-- **Almost every coin sequence has infinitely many free `2`s.**  Confidence 98%.

English proof.  Free positions are infinite (`[(k+2) a k, a (k+1))` is free and nonempty).  For
`n` and `L`, take `L` free positions `≥ n`; the coins there are independent fair, so
`P(all false) = 2^{-L}`.  Letting `L → ∞` the event "no free `true` past `n`" is null; take the
countable union over `n`. -/
theorem ae_frequently_free :
    ∀ᵐ ω ∂coinMeasure, ∀ n, ∃ i, n ≤ i ∧ isFree i = true ∧ ω i = true := by
  sorry

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
  sorry

/-- **A digit change forces a Riesz factor below `cos(π/9)`.**  Confidence 97%.

English proof.  `t = ξ/3^{i+2} mod 1` has leading ternary digits `(tdig ξ (i+1), tdig ξ i)`, so
`t ∈ [a/3 + b/9, a/3 + (b+1)/9)`.  When `a ≠ b` this interval lies in `[1/9, 4/9] ∪ [5/9, 8/9]`,
at distance `≥ 1/18` from `{0, 1/2, 1}`, so `|cos(2πt)| ≤ cos(π/9)`.  Probe: maximum over
`|ξ| < 3000`, `i < 6` is `0.93969262078603 ≈ cos(π/9)` (attained). -/
theorem abs_cos_le_of_tdig_ne (ξ : ℤ) (i : ℕ) (h : tdig ξ (i + 1) ≠ tdig ξ i) :
    |Real.cos (2 * Real.pi * ξ / 3 ^ (i + 2))| ≤ Real.cos (Real.pi / 9) := by
  sorry

theorem summable_ptDigit (free : ℕ → Bool) (ω : ℕ → Bool) :
    Summable fun i => (ptDigit free ω i : ℝ) / (3 : ℝ) ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)))
  have : (ptDigit free ω i : ℝ) ≤ 3 := by exact_mod_cast (ptDigit_lt free ω i).le
  rw [inv_pow, div_le_iff₀ (by positivity), pow_succ, inv_mul_cancel_left₀ (by positivity)]
  exact this

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
  sorry

/-- **The runs keep a `1/log` fraction of free positions.**  Confidence 95%.

English proof.  For `M < a 0 = 4` all positions are free.  For `a k ≤ M < a (k+1)`: the block
`[(k+1)·a (k−1), a k)` (for `k ≥ 1`; `[0, 4)` for `k = 0`) is free and has `a k / 2` elements
(`≥ 4` for `k = 0`); if `M < (k+2) a k` this is `≥ M/(2(k+2))`, and if `M ≥ (k+2) a k` the free
block `[(k+2) a k, M)` adds `M − (k+2) a k`, again giving `≥ M/(2(k+2))`.  Finally
`a k ≥ 4^{k+1}`, so `k + 2 ≤ log₂ M + 2`. -/
theorem le_freeCount (M : ℕ) : M ≤ 2 * (Nat.log 2 M + 2) * freeCount isFree M := by
  sorry

/-- **The Cassels bound is summable along the schedule.**  Confidence 92%.

English proof.  With `N = sched j ≥ e^{√j} − 1` and `M = ⌊log₃ N⌋/2 ≥ √j/(2 ln 3) − 2`,
`le_freeCount` gives `freeCount ≥ M/(2(log₂ M + 2)) ≥ c₁ √j / log(j + 2)`, so the first term is
`≤ exp(−c c₁ √j / log(j+2))`, summable (it is `o(j^{-2})`).  The second is
`≤ (e^{√j} − 1)^{-1/2}`, summable. -/
theorem summable_sched_bound (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    Summable fun j => C * (Real.exp (-c * freeCount isFree (Nat.log 3 (sched j) / 2)) +
      (sched j : ℝ) ^ (-(1 / 2 : ℝ))) := by
  sorry

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
