/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import NormalNumbers.VandeheyS7Tight

/-!
# S7-D: the crux's tail cell IS a Diophantine counting problem

`OrbitCellBound`'s hardest special case is `w = []`: the frequency of digits `≥ T` in the
expansion of the image `y = Int.fract (q x + r₀)` must be `O(1/T)`, not the free `O(1/log T)`
that `VandeheyS7Tight` gets for nothing.

This module converts that case, **unconditionally**, into a statement about the denominators of
the image: a digit `≥ T` at position `p` is exactly a `T`-good rational approximation at the
`p`-th convergent, so

  `#{i < p : cfDigit y i ≥ T} ≤ 1 + #{q ≤ Q : ‖q y‖ ≤ 2/(T q)}`,  `Q = cfK (digitWord y p)`

(`largeDigitCount_le_goodDenCount`, where `‖·‖` is distance to the nearest integer).  Under any Lévy bound `log Q_p ≤ Λ p`, a counting bound
`#{q ≤ Q : ‖q y‖ ≤ 2/(Tq)} ≤ (D/T) · log Q` therefore delivers the frequency `≤ DΛ/T` that the
crux demands (`tailFreq_le_of_goodDenBound`) — the `1/log T → 1/T` passage that lap 30 isolated as
the whole open content of S7-T.

The point of the reformulation: with `y = φ x` the target sets `E_q = {u : ‖q φ u‖ ≤ 2/(Tq)}` are
**`x`-independent** subsets of the circle of measure `≍ 1/(Tq)`, and `∑_{q ≤ Q} 2/(Tq) ≍ (log Q)/T`
is exactly the demanded bound (`heuristic_sum_le`).  So the Diophantine form is *sharp*, not
lossy: the arithmetic of `φ` is the only missing input.

## Guard rule

Content locator: `cfDet` at `w = [a]` is `a·0 − 1·1 = −1`; `goodDenCount_le_card` is the trivial
`≤ Q`, and `tailFreq_le_of_goodDenBound` improves on `blockCount_cellSet_nil_le_length` exactly
when `DΛ/T < 1`.  Degenerate cases: at `T = 1` the hypothesis `GoodDenBound` is *false* for small
`D` (every `q` with `‖q y‖ ≤ 2/q` is counted, and by `abs_convDen_mul_sub_le` all the convergent
denominators qualify), so it really is a large-`T` statement; and `le_cfK_digitWord` /
`heuristic_sum_le` pin the two scales (`Q_p ≥ p`, and the heuristic total `(2/T)(1 + log Q)`)
against which the hypothesis must be read.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-! ## Convergent numerators and the determinant identity -/

/-- The convergent **numerator** `pₙ` of the word `w = a₁…aₙ`: `p₀ = 0` and `p(a :: l) = K(l)`.
This differs from `cfP` only at the empty word, where `cfP [] = cfK [] = 1` is the wrong
convention for a numerator, and that single value is what makes the determinant identity hold. -/
def cfNum : List ℕ → ℕ
  | [] => 0
  | _ :: l => cfK l

@[simp] lemma cfNum_nil : cfNum [] = 0 := rfl

lemma cfNum_eq_cfP {w : List ℕ} (hw : w ≠ []) : cfNum w = cfP w := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a l => simp [cfNum, cfP]

/-- The snoc recursion for numerators, matching `cfK_concat` for denominators. -/
lemma cfNum_concat (v : List ℕ) (z : ℕ) (hv : v ≠ []) :
    cfNum (v ++ [z]) = z * cfNum v + cfNum v.dropLast := by
  cases v with
  | nil => exact absurd rfl hv
  | cons b l =>
      by_cases hl : l = []
      · subst hl; simp [cfNum, cfK]
      · have h1 : cfNum ((b :: l) ++ [z]) = cfK (l ++ [z]) := rfl
        have h3 : (b :: l).dropLast = b :: l.dropLast := by
          simp [List.dropLast_cons_of_ne_nil hl]
        rw [h1, cfK_concat l z hl, h3]
        simp [cfNum]

/-- **The determinant identity.**  `qₙ pₙ₋₁ − pₙ qₙ₋₁ = (−1)ⁿ`. -/
theorem cfDet : ∀ (w : List ℕ), w ≠ [] →
    (cfK w : ℤ) * cfNum w.dropLast - (cfNum w : ℤ) * cfK w.dropLast
      = (-1) ^ w.length := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton v z ih =>
      intro _
      by_cases hv : v = []
      · subst hv; simp [cfNum, cfK]
      · have hK := cfK_concat v z hv
        have hN := cfNum_concat v z hv
        have hd : (v ++ [z]).dropLast = v := by simp
        have hlen : (v ++ [z]).length = v.length + 1 := by simp
        have ihv := ih hv
        rw [hd, hK, hN, hlen, pow_succ]
        push_cast
        ring_nf
        ring_nf at ihv
        linarith [ihv]

lemma bumpLast_ne_nil' (w : List ℕ) : bumpLast w ≠ [] := by simp [bumpLast]

/-- `K(bump w) = K(w) + K(w⁻)` and `p(bump w) = p(w) + p(w⁻)`: the endpoint of the cylinder
`I_w` opposite `pₙ/qₙ` is the mediant. -/
lemma cfK_bumpLast' {w : List ℕ} (hw : w ≠ []) :
    cfK (bumpLast w) = cfK w + cfK w.dropLast ∧
      cfNum (bumpLast w) = cfNum w + cfNum w.dropLast := by
  obtain ⟨v, z, rfl⟩ : ∃ v z, w = v ++ [z] :=
    ⟨w.dropLast, w.getLast hw, (List.dropLast_append_getLast hw).symm⟩
  have hb : bumpLast (v ++ [z]) = v ++ [z + 1] := by simp [bumpLast]
  have hd : (v ++ [z]).dropLast = v := by simp
  by_cases hv : v = []
  · subst hv; simp [bumpLast, cfK, cfNum]
  · rw [hb, hd, cfK_concat v (z + 1) hv, cfK_concat v z hv,
      cfNum_concat v (z + 1) hv, cfNum_concat v z hv]
    constructor <;> ring

/-! ## The approximation bound -/

private lemma cfK_pos {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) : (0:ℝ) < (cfK w : ℝ) := by
  have h := one_le_cfK w hpos
  have : 0 < cfK w := Nat.lt_of_lt_of_le Nat.zero_lt_one h
  exact_mod_cast this

/-- `|pₙ/qₙ − pₙ₋₁/qₙ₋₁| = 1/(qₙ qₙ₋₁)`, the determinant identity in divided form. -/
lemma abs_convergent_sub_convergent {v : List ℕ} (hv : v ≠ []) (hpos : ∀ a ∈ v, 1 ≤ a) :
    |(cfNum v : ℝ) / (cfK v : ℝ) - (cfNum v.dropLast : ℝ) / (cfK v.dropLast : ℝ)|
      = 1 / ((cfK v : ℝ) * (cfK v.dropLast : ℝ)) := by
  have hdpos : ∀ a ∈ v.dropLast, 1 ≤ a := fun a ha => hpos a (List.mem_of_mem_dropLast ha)
  have hK := cfK_pos hpos
  have hKd := cfK_pos hdpos
  have hdet := cfDet v hv
  have habsZ : |(cfNum v : ℤ) * cfK v.dropLast - (cfK v : ℤ) * cfNum v.dropLast| = 1 := by
    have h : (cfNum v : ℤ) * cfK v.dropLast - (cfK v : ℤ) * cfNum v.dropLast
        = -((-1) ^ v.length) := by linarith [hdet]
    rw [h, abs_neg, abs_pow, abs_neg, abs_one, one_pow]
  have habs : |(cfNum v : ℝ) * (cfK v.dropLast : ℝ) - (cfK v : ℝ) * (cfNum v.dropLast : ℝ)|
      = 1 := by
    have := congrArg (fun z : ℤ => ((z : ℝ))) habsZ
    simpa [Int.cast_abs] using this
  rw [div_sub_div _ _ (ne_of_gt hK) (ne_of_gt hKd), abs_div,
    abs_of_pos (mul_pos hK hKd), habs]

/-- The cylinder-endpoint bound with the numerator **named**: every point of `I_w` is within
`1/(qₙ(qₙ+qₙ₋₁))` of `pₙ/qₙ`.  (`CFCylinder.cfCylinder_endpoints` only gives this for an
existentially quantified numerator, which the determinant argument cannot use.) -/
lemma abs_sub_convergent_le {w : List ℕ} (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    {y : ℝ} (hy : y ∈ cfCylinder w) :
    |y - (cfNum w : ℝ) / (cfK w : ℝ)|
      ≤ 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) := by
  have hdpos : ∀ a ∈ w.dropLast, 1 ≤ a := fun a ha => hpos a (List.mem_of_mem_dropLast ha)
  have hbpos : ∀ a ∈ bumpLast w, 1 ≤ a := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hpos a (List.mem_of_mem_dropLast h)
    · simp only [List.mem_singleton] at h; omega
  obtain ⟨hKb, hNb⟩ := cfK_bumpLast' hw
  have hK := cfK_pos hpos
  have hKd := cfK_pos hdpos
  -- the two endpoints, as explicit rationals
  have hE0 : (((cfVal w : ℚ)) : ℝ) = (cfNum w : ℝ) / (cfK w : ℝ) := by
    rw [cfVal_eq_div w hw hpos, cfNum_eq_cfP hw]
    push_cast; ring
  have hE1 : (((cfVal (bumpLast w) : ℚ)) : ℝ)
      = ((cfNum w : ℝ) + (cfNum w.dropLast : ℝ)) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by
    rw [cfVal_eq_div (bumpLast w) (bumpLast_ne_nil' w) hbpos,
      show cfP (bumpLast w) = cfNum (bumpLast w) from
      (cfNum_eq_cfP (bumpLast_ne_nil' w)).symm, hNb, hKb]
    push_cast; ring
  -- the gap between them
  have hgap : |(((cfVal w : ℚ)) : ℝ) - (((cfVal (bumpLast w) : ℚ)) : ℝ)|
      = 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) := by
    rw [hE0, hE1]
    have hsum : (0:ℝ) < (cfK w : ℝ) + (cfK w.dropLast : ℝ) := by linarith
    rw [div_sub_div _ _ (ne_of_gt hK) (ne_of_gt hsum), abs_div,
      abs_of_pos (mul_pos hK hsum)]
    have hnum : (cfNum w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))
        - (cfK w : ℝ) * ((cfNum w : ℝ) + (cfNum w.dropLast : ℝ))
        = (cfNum w : ℝ) * (cfK w.dropLast : ℝ) - (cfK w : ℝ) * (cfNum w.dropLast : ℝ) := by
      ring
    rw [hnum]
    have hdet := cfDet w hw
    have habsZ : |(cfNum w : ℤ) * cfK w.dropLast - (cfK w : ℤ) * cfNum w.dropLast| = 1 := by
      have h : (cfNum w : ℤ) * cfK w.dropLast - (cfK w : ℤ) * cfNum w.dropLast
          = -((-1) ^ w.length) := by linarith [hdet]
      rw [h, abs_neg, abs_pow, abs_neg, abs_one, one_pow]
    have habs : |(cfNum w : ℝ) * (cfK w.dropLast : ℝ) - (cfK w : ℝ) * (cfNum w.dropLast : ℝ)|
        = 1 := by
      have := congrArg (fun z : ℤ => ((z : ℝ))) habsZ
      simpa [Int.cast_abs] using this
    rw [habs]
  -- `y` lies in the closed interval spanned by the endpoints
  have hmem := cfCylinder_subset_uIcc w hw hpos hy
  rw [Set.mem_uIcc] at hmem
  rw [← hE0]
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_sub_comm] at hgap
    rw [abs_of_nonneg (by linarith)]
    have hg : (((cfVal (bumpLast w) : ℚ)) : ℝ) - (((cfVal w : ℚ)) : ℝ)
        ≤ |(((cfVal (bumpLast w) : ℚ)) : ℝ) - (((cfVal w : ℚ)) : ℝ)| := le_abs_self _
    rw [hgap] at hg
    linarith
  · rw [abs_of_nonpos (by linarith)]
    have hg : (((cfVal w : ℚ)) : ℝ) - (((cfVal (bumpLast w) : ℚ)) : ℝ)
        ≤ |(((cfVal w : ℚ)) : ℝ) - (((cfVal (bumpLast w) : ℚ)) : ℝ)| := le_abs_self _
    rw [hgap] at hg
    linarith

/-! ## Large digits are good approximations -/

lemma digitWord_succ (y : ℝ) (p : ℕ) :
    digitWord y (p + 1) = digitWord y p ++ [cfDigit y p] := by
  simp [digitWord, List.range_succ]

lemma dropLast_digitWord_succ (y : ℝ) (p : ℕ) :
    (digitWord y (p + 1)).dropLast = digitWord y p := by
  rw [digitWord_succ, List.dropLast_concat]

/-- `T ≤ aₚ₊₁ ⟹ T qₚ ≤ qₚ₊₁`. -/
lemma cfK_succ_ge_of_large_digit {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T p : ℕ} (hp : 1 ≤ p) (hT : T ≤ cfDigit y p) :
    T * cfK (digitWord y p) ≤ cfK (digitWord y (p + 1)) := by
  have hne : digitWord y p ≠ [] := digitWord_ne_nil hp
  rw [digitWord_succ, cfK_concat _ _ hne]
  exact le_trans (Nat.mul_le_mul_right _ hT) (Nat.le_add_right _ _)

/-- `qₚ < qₚ₊₁` for `p ≥ 1`. -/
lemma cfK_digitWord_lt_succ {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {p : ℕ} (hp : 1 ≤ p) : cfK (digitWord y p) < cfK (digitWord y (p + 1)) := by
  have hne : digitWord y p ≠ [] := digitWord_ne_nil hp
  have hpos := digitWord_pos hy hmem p
  have ha : 1 ≤ cfDigit y p := one_le_cfDigit y hy hmem p
  have hd : 1 ≤ cfK (digitWord y p).dropLast :=
    one_le_cfK _ fun a ha' => hpos a (List.mem_of_mem_dropLast ha')
  rw [digitWord_succ, cfK_concat _ _ hne]
  have h1 : cfK (digitWord y p) ≤ cfDigit y p * cfK (digitWord y p) :=
    Nat.le_mul_of_pos_left _ ha
  omega

lemma cfK_digitWord_lt {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : cfK (digitWord y i) < cfK (digitWord y j) := by
  induction j with
  | zero => omega
  | succ j ih =>
      rcases Nat.lt_or_ge i j with h | h
      · exact lt_trans (ih h) (cfK_digitWord_lt_succ hy hmem (le_trans hi h.le))
      · have : i = j := by omega
        subst this
        exact cfK_digitWord_lt_succ hy hmem hi

lemma cfK_digitWord_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : cfK (digitWord y i) ≤ cfK (digitWord y j) := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (cfK_digitWord_lt hy hmem hi h).le

/-- **The approximation bound.**  `|qₚ y − pₚ| ≤ 2/qₚ₊₁` for every irrational `y ∈ (0,1)`. -/
theorem abs_convDen_mul_sub_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {p : ℕ} (hp : 1 ≤ p) :
    |(cfK (digitWord y p) : ℝ) * y - (cfNum (digitWord y p) : ℝ)|
      ≤ 2 / (cfK (digitWord y (p + 1)) : ℝ) := by
  set w := digitWord y p with hw
  set v := digitWord y (p + 1) with hv
  have hwne : w ≠ [] := digitWord_ne_nil hp
  have hvne : v ≠ [] := digitWord_ne_nil (by omega)
  have hwpos := digitWord_pos hy hmem p
  have hvpos := digitWord_pos hy hmem (p + 1)
  have hvd : v.dropLast = w := dropLast_digitWord_succ y p
  have hKw := cfK_pos hwpos
  have hKv := cfK_pos hvpos
  -- step 1: `y` is close to `p_{p+1}/q_{p+1}`
  have h1 : |y - (cfNum v : ℝ) / (cfK v : ℝ)|
      ≤ 1 / ((cfK v : ℝ) * ((cfK v : ℝ) + (cfK w : ℝ))) := by
    have := abs_sub_convergent_le hvne hvpos (mem_cfCylinder_digitWord hmem (p + 1))
    rwa [hvd] at this
  -- step 2: the two convergents are `1/(q_{p+1} q_p)` apart
  have h2 : |(cfNum v : ℝ) / (cfK v : ℝ) - (cfNum w : ℝ) / (cfK w : ℝ)|
      = 1 / ((cfK v : ℝ) * (cfK w : ℝ)) := by
    have := abs_convergent_sub_convergent hvne hvpos
    rwa [hvd] at this
  -- step 3: combine
  have h3 : |y - (cfNum w : ℝ) / (cfK w : ℝ)| ≤ 2 / ((cfK v : ℝ) * (cfK w : ℝ)) := by
    have hle : 1 / ((cfK v : ℝ) * ((cfK v : ℝ) + (cfK w : ℝ)))
        ≤ 1 / ((cfK v : ℝ) * (cfK w : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (cfK w : ℝ) ≤ (cfK v : ℝ) + (cfK w : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left this hKv.le
    calc |y - (cfNum w : ℝ) / (cfK w : ℝ)|
        ≤ |y - (cfNum v : ℝ) / (cfK v : ℝ)|
            + |(cfNum v : ℝ) / (cfK v : ℝ) - (cfNum w : ℝ) / (cfK w : ℝ)| :=
          abs_sub_le _ _ _
      _ ≤ 1 / ((cfK v : ℝ) * (cfK w : ℝ)) + 1 / ((cfK v : ℝ) * (cfK w : ℝ)) := by
          rw [h2]; exact add_le_add (le_trans h1 hle) le_rfl
      _ = 2 / ((cfK v : ℝ) * (cfK w : ℝ)) := by ring
  -- multiply through by `q_p`
  have hid : (cfK w : ℝ) * y - (cfNum w : ℝ)
      = (cfK w : ℝ) * (y - (cfNum w : ℝ) / (cfK w : ℝ)) := by
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hKw)]
  rw [hid, abs_mul, abs_of_pos hKw]
  calc (cfK w : ℝ) * |y - (cfNum w : ℝ) / (cfK w : ℝ)|
      ≤ (cfK w : ℝ) * (2 / ((cfK v : ℝ) * (cfK w : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 hKw.le
    _ = 2 / (cfK v : ℝ) := by
        have hKw' : (cfK w : ℝ) ≠ 0 := ne_of_gt hKw
        have hKv' : (cfK v : ℝ) ≠ 0 := ne_of_gt hKv
        field_simp

/-! ## The converse: a `T`-good convergent forces a large digit

The reduction above is one-sided.  This section proves the other direction *at the convergent
denominators*, which is where `goodDenCount` actually lives (any `q` with `‖q y‖ < 1/(2q)` is a
convergent denominator — Legendre; not formalized here, and the only remaining gap between the two
counts).  Consequence: the Diophantine hypothesis is **not strictly stronger** than the crux's tail
case — up to the loss `T ↦ (T−4)/2` the two are equivalent, so the route is lossless.
-/

/-- **The matching lower bound.**  `|qₚ y − pₚ| ≥ 1/(qₚ + qₚ₊₁)`: a convergent is never
*too* good.  `y` sits inside the cylinder of depth `p+1`, whose endpoint `pₚ₊₁/qₚ₊₁` is already
`1/(qₚ qₚ₊₁)` away from `pₚ/qₚ`. -/
theorem abs_convDen_mul_sub_ge {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {p : ℕ} (hp : 1 ≤ p) :
    1 / ((cfK (digitWord y p) : ℝ) + (cfK (digitWord y (p + 1)) : ℝ))
      ≤ |(cfK (digitWord y p) : ℝ) * y - (cfNum (digitWord y p) : ℝ)| := by
  set w := digitWord y p with hw
  set v := digitWord y (p + 1) with hv
  have hwne : w ≠ [] := digitWord_ne_nil hp
  have hvne : v ≠ [] := digitWord_ne_nil (by omega)
  have hwpos := digitWord_pos hy hmem p
  have hvpos := digitWord_pos hy hmem (p + 1)
  have hvd : v.dropLast = w := dropLast_digitWord_succ y p
  have hKw := cfK_pos hwpos
  have hKv := cfK_pos hvpos
  have h1 : |y - (cfNum v : ℝ) / (cfK v : ℝ)|
      ≤ 1 / ((cfK v : ℝ) * ((cfK v : ℝ) + (cfK w : ℝ))) := by
    have := abs_sub_convergent_le hvne hvpos (mem_cfCylinder_digitWord hmem (p + 1))
    rwa [hvd] at this
  have h2 : |(cfNum v : ℝ) / (cfK v : ℝ) - (cfNum w : ℝ) / (cfK w : ℝ)|
      = 1 / ((cfK v : ℝ) * (cfK w : ℝ)) := by
    have := abs_convergent_sub_convergent hvne hvpos
    rwa [hvd] at this
  -- reverse triangle inequality
  have h3 : 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK v : ℝ)))
      ≤ |y - (cfNum w : ℝ) / (cfK w : ℝ)| := by
    have hkey : |(cfNum v : ℝ) / (cfK v : ℝ) - (cfNum w : ℝ) / (cfK w : ℝ)|
        ≤ |y - (cfNum w : ℝ) / (cfK w : ℝ)| + |y - (cfNum v : ℝ) / (cfK v : ℝ)| := by
      have h := abs_sub_le ((cfNum v : ℝ) / (cfK v : ℝ)) y ((cfNum w : ℝ) / (cfK w : ℝ))
      rw [abs_sub_comm ((cfNum v : ℝ) / (cfK v : ℝ)) y] at h
      linarith
    rw [h2] at hkey
    have harith : 1 / ((cfK v : ℝ) * (cfK w : ℝ))
        - 1 / ((cfK v : ℝ) * ((cfK v : ℝ) + (cfK w : ℝ)))
        = 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK v : ℝ))) := by
      have hKw' : (cfK w : ℝ) ≠ 0 := ne_of_gt hKw
      have hKv' : (cfK v : ℝ) ≠ 0 := ne_of_gt hKv
      have h4 : ((cfK v : ℝ) + (cfK w : ℝ)) ≠ 0 := by positivity
      have h5 : ((cfK w : ℝ) + (cfK v : ℝ)) ≠ 0 := by positivity
      field_simp
      ring
    linarith [h1, hkey, harith]
  -- multiply through by `qₚ`
  have hid : (cfK w : ℝ) * y - (cfNum w : ℝ)
      = (cfK w : ℝ) * (y - (cfNum w : ℝ) / (cfK w : ℝ)) := by
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hKw)]
  rw [hid, abs_mul, abs_of_pos hKw]
  have hmul := mul_le_mul_of_nonneg_left h3 hKw.le
  refine le_trans (le_of_eq ?_) hmul
  have hKw' : (cfK w : ℝ) ≠ 0 := ne_of_gt hKw
  have hsum : ((cfK w : ℝ) + (cfK v : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

/-- If an integer is within `1/2` of `x`, it is `round x`. -/
private lemma round_eq_of_abs_lt {x : ℝ} {m : ℤ} (h : |x - m| < 1/2) : round x = m := by
  have h1 : |x - (round x : ℝ)| ≤ 1/2 := abs_sub_round x
  have h2 : |((round x : ℝ)) - (m : ℝ)| < 1 := by
    calc |((round x : ℝ)) - (m : ℝ)| ≤ |(round x : ℝ) - x| + |x - (m : ℝ)| := abs_sub_le _ _ _
      _ < 1 := by rw [abs_sub_comm ((round x : ℝ)) x]; linarith
  have h3 : ((round x - m : ℤ) : ℝ) = (round x : ℝ) - (m : ℝ) := by push_cast; ring
  have h4 : |(round x - m : ℤ)| < 1 := by
    have : |((round x - m : ℤ) : ℝ)| < 1 := by rw [h3]; exact h2
    exact_mod_cast this
  have h5 := abs_lt.1 h4
  omega

/-- **The converse.**  A `T`-good convergent denominator forces a large digit:
`‖qₚ y‖ ≤ 2/(T qₚ)` implies `T ≤ 2 aₚ₊₁ + 4`.  Together with
`nearInt_convDen_le` this makes the Diophantine form of S7-T *equivalent* to the crux's tail case,
up to `T ↦ (T−4)/2`. -/
theorem le_digit_of_nearInt_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T p : ℕ} (hp : 1 ≤ p) (hbig : 4 < cfK (digitWord y (p + 1)))
    (hgood : |(cfK (digitWord y p) : ℝ) * y - (round ((cfK (digitWord y p) : ℝ) * y) : ℝ)|
      ≤ 2 / ((T : ℝ) * (cfK (digitWord y p) : ℝ))) :
    (T : ℝ) ≤ 2 * cfDigit y p + 4 := by
  have hwpos := digitWord_pos hy hmem p
  have hvpos := digitWord_pos hy hmem (p + 1)
  have hKw := cfK_pos hwpos
  have hKv := cfK_pos hvpos
  have hwne : digitWord y p ≠ [] := digitWord_ne_nil hp
  -- the nearest integer to `qₚ y` is `pₚ`
  have hupper := abs_convDen_mul_sub_le hy hmem hp
  have hhalf : |(cfK (digitWord y p) : ℝ) * y - (cfNum (digitWord y p) : ℝ)| < 1/2 := by
    have h4 : (4:ℝ) < (cfK (digitWord y (p + 1)) : ℝ) := by exact_mod_cast hbig
    have : 2 / (cfK (digitWord y (p + 1)) : ℝ) < 1/2 := by
      rw [div_lt_div_iff₀ hKv (by norm_num)]
      linarith
    linarith
  have hround : round ((cfK (digitWord y p) : ℝ) * y) = (cfNum (digitWord y p) : ℤ) := by
    refine round_eq_of_abs_lt ?_
    simpa using hhalf
  rw [hround] at hgood
  have hgood' : |(cfK (digitWord y p) : ℝ) * y - (cfNum (digitWord y p) : ℝ)|
      ≤ 2 / ((T : ℝ) * (cfK (digitWord y p) : ℝ)) := by simpa using hgood
  -- the lower bound
  have hlower := abs_convDen_mul_sub_ge hy hmem hp
  have hTpos : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · have : (0:ℝ) ≤ 2 * cfDigit y p + 4 := by positivity
    simpa using this
  have hTposR : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  -- `1/(qₚ + qₚ₊₁) ≤ 2/(T qₚ)` gives `T qₚ ≤ 2 qₚ + 2 qₚ₊₁`
  have hkey : 1 / ((cfK (digitWord y p) : ℝ) + (cfK (digitWord y (p + 1)) : ℝ))
      ≤ 2 / ((T : ℝ) * (cfK (digitWord y p) : ℝ)) := le_trans hlower hgood'
  have hsum : (0:ℝ) < (cfK (digitWord y p) : ℝ) + (cfK (digitWord y (p + 1)) : ℝ) := by linarith
  rw [div_le_div_iff₀ hsum (by positivity)] at hkey
  -- `qₚ₊₁ = aₚ₊₁ qₚ + qₚ₋₁ ≤ (aₚ₊₁ + 1) qₚ`
  have hqv : (cfK (digitWord y (p + 1)) : ℝ)
      ≤ ((cfDigit y p : ℝ) + 1) * (cfK (digitWord y p) : ℝ) := by
    have hdl : cfK (digitWord y p).dropLast ≤ cfK (digitWord y p) :=
      cfK_dropLast_le _ hwpos
    have hrec : cfK (digitWord y (p + 1))
        = cfDigit y p * cfK (digitWord y p) + cfK (digitWord y p).dropLast := by
      rw [digitWord_succ, cfK_concat _ _ hwne]
    have : cfK (digitWord y (p + 1)) ≤ (cfDigit y p + 1) * cfK (digitWord y p) := by
      rw [hrec]; nlinarith [hdl]
    calc (cfK (digitWord y (p + 1)) : ℝ) ≤ (((cfDigit y p + 1) * cfK (digitWord y p) : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = ((cfDigit y p : ℝ) + 1) * (cfK (digitWord y p) : ℝ) := by push_cast; ring
  nlinarith [hkey, hqv, hKw]

/-! ## The counting form -/

/-- `#{q ∈ [1,Q] : ‖q y‖ ≤ 2/(T q)}` — the number of `T`-good denominators up to `Q`. -/
noncomputable def goodDenCount (y : ℝ) (T Q : ℕ) : ℕ :=
  ((Finset.Icc 1 Q).filter
    (fun q : ℕ => |(q : ℝ) * y - (round ((q : ℝ) * y) : ℝ)| ≤ 2 / ((T : ℝ) * q))).card

lemma goodDenCount_le (y : ℝ) (T Q : ℕ) : goodDenCount y T Q ≤ Q := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Nat.card_Icc]

/-- A large digit at position `p ≥ 1` makes `qₚ` a `T`-good denominator. -/
theorem nearInt_convDen_le {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T p : ℕ} (hT : 1 ≤ T) (hp : 1 ≤ p) (hdig : T ≤ cfDigit y p) :
    |(cfK (digitWord y p) : ℝ) * y - (round ((cfK (digitWord y p) : ℝ) * y) : ℝ)|
      ≤ 2 / ((T : ℝ) * (cfK (digitWord y p) : ℝ)) := by
  have hKw := cfK_pos (digitWord_pos hy hmem p)
  have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hround := round_le ((cfK (digitWord y p) : ℝ) * y) (cfNum (digitWord y p) : ℤ)
  have happ := abs_convDen_mul_sub_le hy hmem hp
  have hTq : (T : ℝ) * (cfK (digitWord y p) : ℝ) ≤ (cfK (digitWord y (p + 1)) : ℝ) := by
    have := cfK_succ_ge_of_large_digit hy hmem hp hdig
    exact_mod_cast this
  have hle : 2 / (cfK (digitWord y (p + 1)) : ℝ) ≤ 2 / ((T:ℝ) * (cfK (digitWord y p) : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hTq
  refine le_trans hround (le_trans ?_ hle)
  simpa using happ

/-! ## The reduction -/

lemma countP_digitWord_eq_card (y : ℝ) (T p : ℕ) :
    (digitWord y p).countP (fun a => decide (T ≤ a))
      = ((Finset.range p).filter (fun i => T ≤ cfDigit y i)).card := by
  induction p with
  | zero => simp [digitWord]
  | succ p ih =>
      rw [digitWord_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases h : T ≤ cfDigit y p
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        simp [h]
      · rw [if_neg h]
        simp [h]

/-- **The reduction.**  Unconditionally, the number of large digits in the first `p` digits of an
irrational `y ∈ (0,1)` is at most `1` plus the number of `T`-good denominators up to `qₚ`. -/
theorem largeDigitCount_le_goodDenCount {y : ℝ} (hy : Irrational y)
    (hmem : y ∈ Set.Ioo (0:ℝ) 1) {T p : ℕ} (hT : 1 ≤ T) (hp : 1 ≤ p) :
    blockCount (cellSet [] T) p y ≤ 1 + goodDenCount y T (cfK (digitWord y p)) := by
  rw [blockCount_cellSet_nil_eq hy hmem T p, countP_digitWord_eq_card]
  set S := (Finset.range p).filter (fun i => T ≤ cfDigit y i) with hS
  set G := (Finset.Icc 1 (cfK (digitWord y p))).filter
    (fun q : ℕ => |(q : ℝ) * y - (round ((q : ℝ) * y) : ℝ)| ≤ 2 / ((T : ℝ) * q)) with hG
  -- the indices `≥ 1` inject into `G` via `i ↦ qᵢ`
  have hsub : S ⊆ insert 0 (S.filter (fun i => 1 ≤ i)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hi, hpos⟩)
  have hinj : Set.InjOn (fun i => cfK (digitWord y i)) (S.filter (fun i => 1 ≤ i) : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS, Finset.mem_filter] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_lt (cfK_digitWord_lt hy hmem ha.2 h))
    · exact h
    · exact absurd hab.symm (ne_of_lt (cfK_digitWord_lt hy hmem hb.2 h))
  have hmaps : ∀ i ∈ S.filter (fun i => 1 ≤ i), cfK (digitWord y i) ∈ G := by
    intro i hi
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hir, hid⟩, hi1⟩ := hi
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨one_le_cfK _ (digitWord_pos hy hmem i),
      cfK_digitWord_le hy hmem hi1 hir.le⟩, ?_⟩
    exact nearInt_convDen_le hy hmem hT hi1 hid
  have hcard : (S.filter (fun i => 1 ≤ i)).card ≤ G.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have h1 : S.card ≤ 1 + (S.filter (fun i => 1 ≤ i)).card := by
    have := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le 0 (S.filter (fun i => 1 ≤ i))
    omega
  have : S.card ≤ 1 + G.card := by omega
  rw [goodDenCount, ← hG]
  exact_mod_cast this

/-! ## The heuristic is exact -/

/-- **The heuristic count.**  `∑_{q ≤ Q} 2/(Tq) ≤ (2/T)(1 + log Q)`: summing the measures
`|E_q| ≍ 2/(Tq)` of the `x`-independent target sets gives exactly the bound `GoodDenBound`
demands.  So the Diophantine form of the crux is sharp — the sets are the right size, and only the
arithmetic of the multiplier is missing. -/
theorem heuristic_sum_le {T : ℕ} (hT : 1 ≤ T) (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, 2 / ((T:ℝ) * q) ≤ (2 / T) * (1 + Real.log Q) := by
  have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hsum : ∑ q ∈ Finset.Icc 1 Q, 2 / ((T:ℝ) * q)
      = (2 / T) * ∑ q ∈ Finset.Icc 1 Q, ((q:ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    field_simp
  rw [hsum]
  have hharm : ∑ q ∈ Finset.Icc 1 Q, ((q:ℝ))⁻¹ ≤ 1 + Real.log Q := by
    have h := harmonic_le_one_add_log Q
    have hcast : ((harmonic Q : ℚ) : ℝ) = ∑ q ∈ Finset.Icc 1 Q, ((q:ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rwa [hcast] at h
  exact mul_le_mul_of_nonneg_left hharm (by positivity)

/-! ## What a counting bound buys -/

/-- The Diophantine hypothesis: the `T`-good denominators up to `Q` number at most
`(D/T) log Q`.  This is the *sharp* heuristic count (`heuristic_sum_le`), and by
`tailFreq_le_of_goodDenBound` it supplies exactly the `O(1/T)` rate the crux demands. -/
def GoodDenBound (y : ℝ) (D : ℝ) : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ᶠ Q : ℕ in atTop, (goodDenCount y T Q : ℝ) ≤ (D / T) * Real.log Q

/-- `p ≤ qₚ`: the denominators grow at least linearly, so they tend to infinity. -/
lemma le_cfK_digitWord {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1) :
    ∀ p : ℕ, p ≤ cfK (digitWord y p)
  | 0 => Nat.zero_le _
  | (p + 1) => by
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simpa using one_le_cfK _ (digitWord_pos hy hmem 1)
      · have h1 := cfK_digitWord_lt_succ hy hmem hp
        have ih := le_cfK_digitWord hy hmem p
        omega

lemma tendsto_cfK_digitWord {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (fun p : ℕ => cfK (digitWord y p)) atTop atTop :=
  tendsto_atTop_mono (le_cfK_digitWord hy hmem) tendsto_id

/-- **What the Diophantine bound buys: the missing `1/T`.**  A `GoodDenBound` plus a Lévy bound
gives the frequency of digits `≥ T` in the image expansion as `≤ DΛ/T + ε` — the rate
`OrbitCellBound` demands, and the one the free argument (`tailFreq_le_of_levyBound`, `Λ/log T`)
cannot reach. -/
theorem tailFreq_le_of_goodDenBound {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {D Λ : ℝ} (hD : 0 ≤ D) (hgd : GoodDenBound y D) (hL : LevyBound y Λ)
    {T : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, blockCount (cellSet [] T) p y / p ≤ (D / T) * Λ + ε := by
  have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hDT : 0 ≤ D / T := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
  filter_upwards [(tendsto_cfK_digitWord hy hmem).eventually (hgd T hT), hL,
    eventually_ge_atTop N, eventually_gt_atTop 0] with p h1 h2 h3 h4
  have hpr : (0:ℝ) < p := by exact_mod_cast h4
  have hpN : (N:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
  have hinv : 1 / (p:ℝ) ≤ ε := by
    have hle : 1 / (p:ℝ) ≤ 1 / (N:ℝ) := one_div_le_one_div_of_le hNpos hpN
    have hlt : 1 / (N:ℝ) < ε := by
      rw [div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hε] at hN
      linarith
    linarith
  have hone : (1:ℝ) ≤ ε * p := by
    rw [div_le_iff₀ hpr] at hinv
    linarith
  have hbc := largeDigitCount_le_goodDenCount hy hmem hT h4
  rw [div_le_iff₀ hpr]
  calc blockCount (cellSet [] T) p y
      ≤ 1 + (goodDenCount y T (cfK (digitWord y p)) : ℝ) := hbc
    _ ≤ 1 + (D / T) * Real.log (cfK (digitWord y p)) := by linarith
    _ ≤ 1 + (D / T) * (Λ * p) := by
        have := mul_le_mul_of_nonneg_left h2 hDT
        linarith
    _ ≤ ε * p + (D / T) * (Λ * p) := by linarith
    _ = ((D / T) * Λ + ε) * p := by ring

section Audit

#print axioms cfDet
#print axioms abs_convergent_sub_convergent
#print axioms abs_sub_convergent_le
#print axioms abs_convDen_mul_sub_le
#print axioms nearInt_convDen_le
#print axioms largeDigitCount_le_goodDenCount
#print axioms tailFreq_le_of_goodDenBound
#print axioms heuristic_sum_le
#print axioms abs_convDen_mul_sub_ge
#print axioms le_digit_of_nearInt_le

end Audit

end NormalNumbers.VandeheyS7
