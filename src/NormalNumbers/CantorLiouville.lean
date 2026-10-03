/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.DecayAeNormal
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

open DecayAeNormal ExplicitSquare

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

/-- **Content locator: `2` generates `(ℤ/3^{M+1})ˣ`.**  Confidence 99%.

English proof.  `2 ≡ −1 (mod 3)` has order `2` mod `3`; by lifting the exponent,
`v₃(2^{2t} − 1) = v₃(4ᵗ − 1) = 1 + v₃(t)`, so the order of `4` mod `3^{M+1}` is `3^M`, and the
order of `2` is `2·3^M = φ(3^{M+1})`.  This is exactly what fails for `3` (`3` is not a unit). -/
theorem orderOf_two_zmod_three_pow (M : ℕ) :
    orderOf (2 : ZMod (3 ^ (M + 1))) = 2 * 3 ^ M := by
  sorry

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

/-- **Riesz-product bound for the characteristic function.**  Confidence 94%.

English proof.  `pt free ω = Σ_{p<M} d_p 3^{-(p+1)} + 3^{-M}·(tail)`, the two parts independent
under `coinMeasure` (disjoint coordinates).  So `𝔼 e(ξx)` factors; each free `p < M` contributes
`𝔼 e(2ξ ω_p/3^{p+1}) = (1 + e(2ξ/3^{p+1}))/2`, of modulus `|cos(2πξ/3^{p+1})|`; forced `p`
contribute `1`; the tail factor has modulus `≤ 1`. -/
theorem charFun_norm_le (free : ℕ → Bool) (ξ : ℤ) (M : ℕ) :
    ‖∫ ω, ee (ξ * pt free ω) ∂coinMeasure‖ ≤
      ∏ p ∈ (Finset.range M).filter (fun p => free p = true),
        |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| := by
  sorry

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
  sorry

/-! ## Davenport–Erdős–LeVeque along a slow schedule -/

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
  sorry

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
