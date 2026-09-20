/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.Walsh

/-!
# The digit-character criterion for normality in any base

`Walsh.lean` is base two: the characters of `(ℤ/2)^L` are the parity products `∏ (-1)^{s(n+i)}`.
This file is the same theorem for every base `b`.  The characters of `(ℤ/b)^L` are indexed by
`k : Fin L → Fin b` and evaluate on a digit window as

  `digitChar ζ s k n = ∏_{i < L} ζ^{s(n+i) · k_i}`,   `ζ = exp(2πi/b)`.

Everything base two did with `(-1)^a (-1)^c ∈ {±1}` is done here with the geometric sum
`∑_{j<b} x^j`, which is `b` at `x = 1` and `0` at any other `b`-th root of unity.  The word
enumeration that was a powerset becomes `Finset.univ` on `Fin L → Fin b`, and
`Finset.prod_add` becomes `Fintype.prod_sum`.

Headline: `isNormalSequence_iff_digitMean` — a base-`b` digit sequence is normal iff every
nontrivial character mean tends to zero.  Exact finite transform, no truncation term.
-/

namespace NormalNumbers.WalshBase

open Finset Walsh

variable {b : ℕ} [NeZero b]

/-- The standard primitive `b`-th root of unity. -/
noncomputable def zeta (b : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / b)

theorem isPrimitiveRoot_zeta (b : ℕ) [NeZero b] : IsPrimitiveRoot (zeta b) b :=
  Complex.isPrimitiveRoot_exp b (NeZero.ne b)

/-- The character indexed by `k : Fin L → Fin b`, evaluated on a digit vector `d`. -/
def charOf (ζ : ℂ) {L : ℕ} (k : Fin L → Fin b) (d : Fin L → ℕ) : ℂ :=
  ∏ i, ζ ^ (d i * (k i : ℕ))

/-- The length-`L` digit window of `s` starting at `n`. -/
def window (s : ℕ → ℕ) (L n : ℕ) : Fin L → ℕ := fun i => s (n + i)

/-- A block as a digit vector. -/
def blockVec (w : List ℕ) : Fin w.length → ℕ := fun i => w.getD i 0

/-- The digit character of `s` at index `k`, read at position `n`. -/
def digitChar (ζ : ℂ) (s : ℕ → ℕ) {L : ℕ} (k : Fin L → Fin b) (n : ℕ) : ℂ :=
  charOf ζ k (window s L n)

/-- The character mean of `s` at index `k` across the first `N` positions. -/
noncomputable def digitMean (ζ : ℂ) (s : ℕ → ℕ) {L : ℕ} (k : Fin L → Fin b) (N : ℕ) : ℂ :=
  (∑ n ∈ range N, digitChar ζ s k n) / N

@[simp] theorem charOf_zero (ζ : ℂ) {L : ℕ} (d : Fin L → ℕ) : charOf ζ (0 : Fin L → Fin b) d = 1 := by
  simp [charOf]

@[simp] theorem digitMean_zero_of_pos (ζ : ℂ) (s : ℕ → ℕ) {L : ℕ} {N : ℕ} (hN : 0 < N) :
    digitMean ζ s (0 : Fin L → Fin b) N = 1 := by
  simp [digitMean, digitChar, Nat.cast_ne_zero.mpr hN.ne']

theorem norm_charOf {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) {L : ℕ} (k : Fin L → Fin b)
    (d : Fin L → ℕ) : ‖charOf ζ k d‖ = 1 := by
  rw [charOf, norm_prod]
  refine Finset.prod_eq_one (fun i _ => ?_)
  rw [norm_pow, hζ.norm'_eq_one (NeZero.ne b), one_pow]

/-- `MatchesAt` is equality of the window with the block vector. -/
theorem matchesAt_iff_window_eq (s : ℕ → ℕ) (w : List ℕ) (n : ℕ) :
    MatchesAt s w n ↔ window s w.length n = blockVec w := by
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h j hj
    exact congrFun h ⟨j, hj⟩

/-- **The product collapse, base `b`.**  Summing `χ_k(a)⁻¹ χ_k(c)` over all characters gives
`b^L` when the digit vectors agree and `0` otherwise: each coordinate contributes a geometric
sum of a `b`-th root of unity, which vanishes unless that root is `1`. -/
theorem sum_inv_char_mul_char {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) {L : ℕ} (a c : Fin L → ℕ)
    (ha : ∀ i, a i < b) (hc : ∀ i, c i < b) :
    ∑ k : Fin L → Fin b, (charOf ζ k a)⁻¹ * charOf ζ k c
      = if a = c then (b : ℂ) ^ L else 0 := by
  classical
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne b)
  have hsummand : ∀ k : Fin L → Fin b, (charOf ζ k a)⁻¹ * charOf ζ k c
      = ∏ i, ((ζ ^ a i)⁻¹ * ζ ^ c i) ^ (k i : ℕ) := by
    intro k
    simp only [charOf, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, pow_mul, mul_pow,
      inv_pow]
  simp only [hsummand]
  rw [← Fintype.prod_sum (fun i (j : Fin b) => ((ζ ^ a i)⁻¹ * ζ ^ c i) ^ (j : ℕ))]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl]
    have : ∀ i, ∑ j : Fin b, ((ζ ^ a i)⁻¹ * ζ ^ a i) ^ (j : ℕ) = (b : ℂ) := by
      intro i
      rw [inv_mul_cancel₀ (pow_ne_zero _ hζ0)]
      simp
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ c i := by
      by_contra hcon
      push Not at hcon
      exact h (funext hcon)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have hx1 : (ζ ^ a i)⁻¹ * ζ ^ c i ≠ 1 := by
      intro hx
      rw [inv_mul_eq_one₀ (pow_ne_zero _ hζ0)] at hx
      exact hi (hζ.pow_inj (ha i) (hc i) hx)
    have hxb : ((ζ ^ a i)⁻¹ * ζ ^ c i) ^ b = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (a i), mul_comm (c i), pow_mul,
        pow_mul, hζ.pow_eq_one, one_pow, one_pow, inv_one, one_mul]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((ζ ^ a i)⁻¹ * ζ ^ c i) ^ j) b, geom_sum_eq hx1,
      hxb, sub_self, zero_div]

/-- **The Fourier expansion of a block indicator, base `b`.** -/
theorem matchesAt_indicator_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ) (w : List ℕ)
    (n : ℕ) (hs : ∀ m, s m < b) (hw : ∀ d ∈ w, d < b) :
    (if MatchesAt s w n then (1 : ℂ) else 0)
      = ((b : ℂ) ^ w.length)⁻¹ * ∑ k : Fin w.length → Fin b,
          (charOf ζ k (blockVec w))⁻¹ * digitChar ζ s k n := by
  simp only [digitChar]
  rw [sum_inv_char_mul_char hζ (blockVec w) (window s _ n)
    (fun i => hw _ (getD_mem_of_lt i.isLt)) (fun i => hs _)]
  have hb : ((b : ℂ) ^ w.length) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne b))
  by_cases hm : MatchesAt s w n
  · rw [if_pos hm, if_pos ((matchesAt_iff_window_eq s w n).mp hm).symm, inv_mul_cancel₀ hb]
  · rw [if_neg hm, if_neg (fun h => hm ((matchesAt_iff_window_eq s w n).mpr h.symm)), mul_zero]

/-! ## The summed transform and inequality (A) -/

/-- **The transform, summed.**  Block frequency is the character-weighted average of the
character means.  Exact at every finite `N`. -/
theorem blockMean_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ) (w : List ℕ) (N : ℕ)
    (hs : ∀ m, s m < b) (hw : ∀ d ∈ w, d < b) :
    ((blockMean s w N : ℝ) : ℂ)
      = ((b : ℂ) ^ w.length)⁻¹ * ∑ k : Fin w.length → Fin b,
          (charOf ζ k (blockVec w))⁻¹ * digitMean ζ s k N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [blockMean, blockCount, digitMean]
  have hcount : ((blockCount s w N : ℕ) : ℂ)
      = ∑ n ∈ range N, (if MatchesAt s w n then (1 : ℂ) else 0) := by
    rw [blockCount, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> simp)
  rw [blockMean]
  push_cast
  rw [hcount, Finset.sum_congr rfl (fun n _ => matchesAt_indicator_eq hζ s w n hs hw),
    ← Finset.mul_sum, mul_div_assoc]
  congr 1
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.mul_sum, digitMean, mul_div_assoc]

/-- Splitting the trivial character out of the transform. -/
theorem blockMean_sub_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ) (w : List ℕ) {N : ℕ}
    (hN : 0 < N) (hs : ∀ m, s m < b) (hw : ∀ d ∈ w, d < b) :
    ((blockMean s w N : ℝ) : ℂ) - ((b : ℂ) ^ w.length)⁻¹
      = ((b : ℂ) ^ w.length)⁻¹ * ∑ k ∈ (univ : Finset (Fin w.length → Fin b)).erase 0,
          (charOf ζ k (blockVec w))⁻¹ * digitMean ζ s k N := by
  classical
  rw [blockMean_eq hζ s w N hs hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
    charOf_zero, digitMean_zero_of_pos ζ s hN]
  ring

/-- **Inequality (A), base `b`.**  Every block frequency is controlled by the nontrivial
character means. -/
theorem abs_blockMean_sub_le {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ) (w : List ℕ)
    {N : ℕ} (hN : 0 < N) (hs : ∀ m, s m < b) (hw : ∀ d ∈ w, d < b) :
    |blockMean s w N - ((b : ℝ) ^ w.length)⁻¹|
      ≤ ((b : ℝ) ^ w.length)⁻¹ *
          ∑ k ∈ (univ : Finset (Fin w.length → Fin b)).erase 0, ‖digitMean ζ s k N‖ := by
  classical
  have hcast : |blockMean s w N - ((b : ℝ) ^ w.length)⁻¹|
      = ‖((blockMean s w N : ℝ) : ℂ) - ((b : ℂ) ^ w.length)⁻¹‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [hcast, blockMean_sub_eq hζ s w hN hs hw, norm_mul, norm_inv, norm_pow,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [norm_mul, norm_inv, norm_charOf hζ, inv_one, one_mul]

/-! ## Sufficiency -/

open Filter Topology

theorem tendsto_sum_norm_digitMean {ζ : ℂ} (s : ℕ → ℕ) (L : ℕ)
    (h : ∀ k : Fin L → Fin b, k ≠ 0 → Tendsto (digitMean ζ s k) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ k ∈ (univ : Finset (Fin L → Fin b)).erase 0, ‖digitMean ζ s k N‖)
      atTop (𝓝 0) := by
  classical
  have : Tendsto (fun N => ∑ k ∈ (univ : Finset (Fin L → Fin b)).erase 0, ‖digitMean ζ s k N‖)
      atTop (𝓝 (∑ k ∈ (univ : Finset (Fin L → Fin b)).erase 0, (0 : ℝ))) := by
    refine tendsto_finsetSum _ (fun k hk => ?_)
    simpa using (h k (Finset.ne_of_mem_erase hk)).norm
  simpa using this

theorem tendsto_blockMean {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ) (w : List ℕ)
    (hs : ∀ m, s m < b) (hw : ∀ d ∈ w, d < b)
    (h : ∀ k : Fin w.length → Fin b, k ≠ 0 → Tendsto (digitMean ζ s k) atTop (𝓝 0)) :
    Tendsto (blockMean s w) atTop (𝓝 (((b : ℝ) ^ w.length))⁻¹) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hmaj : Tendsto
      (fun N => ((b : ℝ) ^ w.length)⁻¹ *
        ∑ k ∈ (univ : Finset (Fin w.length → Fin b)).erase 0, ‖digitMean ζ s k N‖)
      atTop (𝓝 0) := by
    simpa using (tendsto_sum_norm_digitMean s w.length h).const_mul (((b : ℝ) ^ w.length)⁻¹)
  refine squeeze_zero' (Eventually.of_forall (fun N => dist_nonneg)) ?_ hmaj
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.dist_eq]
  exact abs_blockMean_sub_le hζ s w hN hs hw

/-- 🎯 **Sufficiency.**  A base-`b` digit sequence whose every nontrivial character mean
vanishes is normal in base `b`. -/
theorem isNormalSequence_of_digitMean_tendsto {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ)
    (hs : ∀ m, s m < b)
    (h : ∀ L, ∀ k : Fin L → Fin b, k ≠ 0 → Tendsto (digitMean ζ s k) atTop (𝓝 0)) :
    IsNormalSequence b s := by
  intro w hwne hw
  have hmain : Tendsto (blockMean s w) atTop (𝓝 (((b : ℝ) ^ w.length))⁻¹) :=
    tendsto_blockMean hζ s w hs hw (h w.length)
  have hdiff : Tendsto
      (fun N => (countOccurrences w ((List.range N).map s) : ℝ) / N - blockMean s w N)
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ => (w.length : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, blockMean, div_sub_div_same, abs_div, abs_of_pos hNpos]
    gcongr
    exact abs_count_sub_blockCount_le s hwne N
  have := hmain.add hdiff
  simp only [add_zero] at this
  convert this using 2 with N
  ring

/-! ## Necessity -/

/-- The word of length `L` with digit vector `T`. -/
def wordOf {L : ℕ} (T : Fin L → Fin b) : List ℕ := List.ofFn (fun i => (T i : ℕ))

/-- The digit vector as natural numbers. -/
def natVec {L : ℕ} (T : Fin L → Fin b) : Fin L → ℕ := fun i => (T i : ℕ)

@[simp] theorem length_wordOf {L : ℕ} (T : Fin L → Fin b) : (wordOf T).length = L := by
  simp [wordOf]

theorem getD_wordOf {L : ℕ} (T : Fin L → Fin b) {i : ℕ} (hi : i < L) :
    (wordOf T).getD i 0 = (T ⟨i, hi⟩ : ℕ) := by
  rw [wordOf, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem wordOf_lt {L : ℕ} (T : Fin L → Fin b) : ∀ d ∈ wordOf T, d < b := by
  intro d hd
  rw [wordOf, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  exact (T i).isLt

theorem wordOf_ne_nil {L : ℕ} (hL : 0 < L) (T : Fin L → Fin b) : wordOf T ≠ [] := by
  intro h
  have := length_wordOf T
  rw [h] at this
  simp at this
  omega

/-- The window of `s` at `n` as a `Fin b`-valued vector. -/
def windowVec (s : ℕ → ℕ) (hs : ∀ m, s m < b) (L n : ℕ) : Fin L → Fin b :=
  fun i => ⟨s (n + i), hs _⟩

theorem natVec_windowVec (s : ℕ → ℕ) (hs : ∀ m, s m < b) (L n : ℕ) :
    natVec (windowVec s hs L n) = window s L n := rfl

theorem matchesAt_wordOf_windowVec (s : ℕ → ℕ) (hs : ∀ m, s m < b) (L n : ℕ) :
    MatchesAt s (wordOf (windowVec s hs L n)) n := by
  intro j hj
  have hjL : j < L := by simpa using hj
  rw [getD_wordOf _ hjL]
  rfl

theorem eq_windowVec_of_matchesAt (s : ℕ → ℕ) (hs : ∀ m, s m < b) {L n : ℕ}
    {T : Fin L → Fin b} (h : MatchesAt s (wordOf T) n) : T = windowVec s hs L n := by
  funext i
  have := h i (by simpa using i.isLt)
  rw [getD_wordOf _ i.isLt] at this
  exact Fin.ext this.symm

/-- **Orthogonality.**  A nontrivial character sums to zero over all words of its length. -/
theorem sum_charOf_eq_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) {L : ℕ} {k : Fin L → Fin b}
    (hk : k ≠ 0) : ∑ T : Fin L → Fin b, charOf ζ k (natVec T) = 0 := by
  classical
  have hsummand : ∀ T : Fin L → Fin b, charOf ζ k (natVec T)
      = ∏ i, (ζ ^ (k i : ℕ)) ^ (T i : ℕ) := by
    intro T
    simp only [charOf, natVec, pow_mul']
  simp only [hsummand]
  rw [← Fintype.prod_sum (fun i (j : Fin b) => (ζ ^ (k i : ℕ)) ^ (j : ℕ))]
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk (funext hcon)
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hx1 : ζ ^ (k i : ℕ) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (fun h => hi (Fin.ext h)) (k i).isLt
  have hxb : (ζ ^ (k i : ℕ)) ^ b = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ (k i : ℕ)) ^ j) b, geom_sum_eq hx1, hxb,
    sub_self, zero_div]

/-- **The pointwise inverse transform.**  Exactly one word matches at each position. -/
theorem digitChar_eq_sum (ζ : ℂ) (s : ℕ → ℕ) (hs : ∀ m, s m < b) {L : ℕ} (k : Fin L → Fin b)
    (n : ℕ) :
    digitChar ζ s k n
      = ∑ T : Fin L → Fin b,
          (if MatchesAt s (wordOf T) n then charOf ζ k (natVec T) else 0) := by
  classical
  rw [Finset.sum_eq_single (windowVec s hs L n)]
  · rw [if_pos (matchesAt_wordOf_windowVec s hs L n), natVec_windowVec]
    rfl
  · intro T _ hne
    exact if_neg (fun hm => hne (eq_windowVec_of_matchesAt s hs hm))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- 🎯 **Necessity.**  A base-`b` normal sequence has every nontrivial character mean tending
to zero. -/
theorem tendsto_digitMean_of_isNormalSequence {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) {s : ℕ → ℕ}
    (hs : ∀ m, s m < b) (h : IsNormalSequence b s) {L : ℕ} {k : Fin L → Fin b} (hk : k ≠ 0) :
    Tendsto (digitMean ζ s k) atTop (𝓝 0) := by
  classical
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · exact absurd (funext (fun i => i.elim0)) hk
    · exact hL
  -- each word of length `L` has frequency tending to `b⁻ᴸ`
  have hword : ∀ T : Fin L → Fin b,
      Tendsto (fun N => |blockMean s (wordOf T) N - ((b : ℝ) ^ L)⁻¹|) atTop (𝓝 0) := by
    intro T
    have hb := tendsto_blockMean_of_isNormal h (wordOf_ne_nil hL T) (wordOf_lt T)
    rw [length_wordOf] at hb
    have : Tendsto (fun N => blockMean s (wordOf T) N - ((b : ℝ) ^ L)⁻¹) atTop
        (𝓝 (((b : ℝ) ^ L)⁻¹ - ((b : ℝ) ^ L)⁻¹)) := hb.sub_const _
    rw [sub_self] at this
    simpa using this.abs
  -- the transform: the character mean is the character-weighted sum of block frequencies
  have hrepr : ∀ N : ℕ, 0 < N → digitMean ζ s k N
      = ∑ T : Fin L → Fin b,
          (((blockMean s (wordOf T) N : ℝ) : ℂ) - ((b : ℂ) ^ L)⁻¹) * charOf ζ k (natVec T) := by
    intro N hN
    have hsum : ∑ n ∈ range N, digitChar ζ s k n
        = ∑ T : Fin L → Fin b, ((blockCount s (wordOf T) N : ℝ) : ℂ) * charOf ζ k (natVec T) := by
      rw [Finset.sum_congr rfl (fun n _ => digitChar_eq_sum ζ s hs k n), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, blockCount]
      push_cast
      rfl
    have horth : ∑ T : Fin L → Fin b, ((b : ℂ) ^ L)⁻¹ * charOf ζ k (natVec T) = 0 := by
      rw [← Finset.mul_sum, sum_charOf_eq_zero hζ hk, mul_zero]
    have hexp : ∑ T : Fin L → Fin b,
          (((blockMean s (wordOf T) N : ℝ) : ℂ) - ((b : ℂ) ^ L)⁻¹) * charOf ζ k (natVec T)
        = (∑ T : Fin L → Fin b,
            ((blockMean s (wordOf T) N : ℝ) : ℂ) * charOf ζ k (natVec T))
          - ∑ T : Fin L → Fin b, ((b : ℂ) ^ L)⁻¹ * charOf ζ k (natVec T) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun T _ => by ring)
    rw [hexp, horth, sub_zero, digitMean, hsum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [blockMean]
    push_cast
    rw [div_mul_eq_mul_div]
  -- squeeze
  have hmaj : Tendsto
      (fun N => ∑ T : Fin L → Fin b, |blockMean s (wordOf T) N - ((b : ℝ) ^ L)⁻¹|)
      atTop (𝓝 0) := by
    have : Tendsto
        (fun N => ∑ T : Fin L → Fin b, |blockMean s (wordOf T) N - ((b : ℝ) ^ L)⁻¹|)
        atTop (𝓝 (∑ T : Fin L → Fin b, (0 : ℝ))) :=
      tendsto_finsetSum _ (fun T _ => hword T)
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [hrepr N hN]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun T _ => ?_))
  rw [norm_mul, norm_charOf hζ, mul_one, ← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  exact le_refl _

/-- 🎯 **THE DIGIT-CHARACTER CRITERION, any base.**  For a base-`b` digit sequence, normality
is *exactly* the vanishing of every nontrivial character mean of the digit group `(ℤ/b)^L`,
for every window length `L`.

Base two (`Walsh.isNormalSequence_two_iff_parityMean`) is the case `ζ = -1`, where the
characters are the parity products.  As there, the transform is exact at every finite `N`. -/
theorem isNormalSequence_iff_digitMean {ζ : ℂ} (hζ : IsPrimitiveRoot ζ b) (s : ℕ → ℕ)
    (hs : ∀ m, s m < b) :
    IsNormalSequence b s ↔
      ∀ L, ∀ k : Fin L → Fin b, k ≠ 0 → Tendsto (digitMean ζ s k) atTop (𝓝 0) :=
  ⟨fun h L k hk => tendsto_digitMean_of_isNormalSequence hζ hs h hk,
   fun h => isNormalSequence_of_digitMean_tendsto hζ s hs h⟩

/-- The criterion at the standard root `exp(2πi/b)`. -/
theorem isNormalSequence_iff_digitMean_zeta (s : ℕ → ℕ) (hs : ∀ m, s m < b) :
    IsNormalSequence b s ↔
      ∀ L, ∀ k : Fin L → Fin b, k ≠ 0 → Tendsto (digitMean (zeta b) s k) atTop (𝓝 0) :=
  isNormalSequence_iff_digitMean (isPrimitiveRoot_zeta b) s hs

/-! ## Base two recovers `Walsh.lean` exactly

So that nobody re-litigates whether the two files say the same thing at `b = 2`: the standard
root is `-1`, the parity character of an offset set `S ⊆ range L` is the digit character at
the indicator index `kOf L S`, every index `k : Fin L → Fin 2` is such an indicator, and the
two criterion statements are equivalent **directly**, with no digit hypothesis and without
passing through normality. -/

theorem zeta_two : zeta 2 = -1 := by
  rw [zeta, Nat.cast_ofNat, show (2 * (Real.pi : ℂ) * Complex.I / 2) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- The base-two index attached to an offset set: its indicator on `Fin L`. -/
def kOf (L : ℕ) (S : Finset ℕ) : Fin L → Fin 2 := fun i => if (i : ℕ) ∈ S then 1 else 0

/-- The offset set attached to a base-two index: the positions where it is `1`. -/
def setOf' {L : ℕ} (k : Fin L → Fin 2) : Finset ℕ :=
  (Finset.univ.filter (fun i => k i = 1)).map Fin.valEmbedding

theorem fin_two_eq_zero_or_one (j : Fin 2) : j = 0 ∨ j = 1 := by
  fin_cases j <;> simp

theorem setOf'_subset {L : ℕ} (k : Fin L → Fin 2) : setOf' k ⊆ range L := by
  intro i hi
  rw [setOf', Finset.mem_map] at hi
  obtain ⟨j, _, rfl⟩ := hi
  exact Finset.mem_range.mpr j.isLt

theorem mem_setOf' {L : ℕ} (k : Fin L → Fin 2) (i : Fin L) : (i : ℕ) ∈ setOf' k ↔ k i = 1 := by
  rw [setOf', Finset.mem_map]
  constructor
  · rintro ⟨j, hj, hji⟩
    have : j = i := Fin.ext hji
    subst this
    exact (Finset.mem_filter.mp hj).2
  · intro h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem kOf_setOf' {L : ℕ} (k : Fin L → Fin 2) : kOf L (setOf' k) = k := by
  funext i
  rw [kOf]
  rcases fin_two_eq_zero_or_one (k i) with h | h
  · rw [if_neg (fun hm => by rw [(mem_setOf' k i).mp hm] at h; exact absurd h (by decide)), h]
  · rw [if_pos ((mem_setOf' k i).mpr h), h]

theorem setOf'_nonempty_iff {L : ℕ} (k : Fin L → Fin 2) : (setOf' k).Nonempty ↔ k ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ hk
    rw [setOf', Finset.mem_map] at hi
    obtain ⟨j, hj, _⟩ := hi
    have := (Finset.mem_filter.mp hj).2
    rw [hk, Pi.zero_apply] at this
    exact absurd this (by decide)
  · intro hk
    by_contra hne
    apply hk
    funext i
    rcases fin_two_eq_zero_or_one (k i) with h | h
    · exact h
    · exact absurd ⟨_, (mem_setOf' k i).mpr h⟩ hne

theorem kOf_ne_zero {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L) :
    kOf L S ≠ 0 := by
  obtain ⟨j, hj⟩ := hS
  intro h
  have hjL : j < L := Finset.mem_range.mp (hSL hj)
  have := congrFun h ⟨j, hjL⟩
  rw [kOf] at this
  simp only [if_pos hj, Pi.zero_apply] at this
  exact absurd this (by decide)

/-- 🔗 **Pointwise wiring.**  The parity character of `Walsh.lean` is the base-two digit
character at the indicator index. -/
theorem digitChar_neg_one_kOf (s : ℕ → ℕ) {L : ℕ} {S : Finset ℕ} (hSL : S ⊆ range L) (n : ℕ) :
    digitChar (-1) s (kOf L S) n = ((parityChar s S n : ℝ) : ℂ) := by
  rw [digitChar, charOf, parityChar]
  push_cast
  have hfac : ∀ i : Fin L, (-1 : ℂ) ^ (window s L n i * (kOf L S i : ℕ))
      = if (i : ℕ) ∈ S then (-1 : ℂ) ^ s (n + i) else 1 := by
    intro i
    rw [window, kOf]
    split_ifs <;> simp
  simp only [hfac]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i ∈ S then (-1 : ℂ) ^ s (n + i) else 1) L,
    ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSL]

theorem digitMean_neg_one_kOf (s : ℕ → ℕ) {L : ℕ} {S : Finset ℕ} (hSL : S ⊆ range L) (N : ℕ) :
    digitMean (-1) s (kOf L S) N = ((parityMean s S N : ℝ) : ℂ) := by
  rw [digitMean, parityMean, Finset.sum_congr rfl (fun n _ => digitChar_neg_one_kOf s hSL n)]
  push_cast
  rfl

theorem digitMean_zeta_two_kOf (s : ℕ → ℕ) {L : ℕ} {S : Finset ℕ} (hSL : S ⊆ range L)
    (N : ℕ) : digitMean (zeta 2) s (kOf L S) N = ((parityMean s S N : ℝ) : ℂ) := by
  rw [zeta_two, digitMean_neg_one_kOf s hSL]

/-- 🔗 **The two criteria are one statement at base two** — proved directly, with no digit
hypothesis and without going through `IsNormalSequence`. -/
theorem parityMean_criterion_iff_digitMean_criterion (s : ℕ → ℕ) :
    (∀ S : Finset ℕ, S.Nonempty → Tendsto (parityMean s S) atTop (𝓝 0)) ↔
      ∀ L, ∀ k : Fin L → Fin 2, k ≠ 0 → Tendsto (digitMean (zeta 2) s k) atTop (𝓝 0) := by
  constructor
  · intro h L k hk
    have hS := (setOf'_nonempty_iff k).mpr hk
    have hSL := setOf'_subset k
    have hre := (Complex.continuous_ofReal.tendsto 0).comp (h _ hS)
    rw [← kOf_setOf' k]
    refine hre.congr' (Eventually.of_forall (fun N => ?_))
    simp [Function.comp, digitMean_zeta_two_kOf s hSL]
  · intro h S hS
    obtain ⟨L, hSL⟩ : ∃ L, S ⊆ range L := ⟨S.max' hS + 1, fun i hi =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' i hi))⟩
    have hk := h L (kOf L S) (kOf_ne_zero hS hSL)
    have hre := (Complex.continuous_re.tendsto 0).comp hk
    refine hre.congr' (Eventually.of_forall (fun N => ?_))
    simp [Function.comp, digitMean_zeta_two_kOf s hSL]

end NormalNumbers.WalshBase
