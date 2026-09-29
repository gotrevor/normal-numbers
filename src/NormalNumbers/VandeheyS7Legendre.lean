/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-L2: Legendre's criterion — every primitive `T`-good denominator IS a convergent denominator

The Diophantine reformulation of the crux (`VandeheyS7Dioph`) bounds the frequency of large
image digits by `goodDenCountPrim y T Q`, the number of primitive `T`-good denominators `q ≤ Q`.
Lap 32 proved the converse *at the convergents* (`le_digit_of_nearInt_le`).  The gap between the
two counts was the possibility of good denominators that are **not** convergent denominators.

This module closes that gap, in the kernel, with an elementary argument that does **not** need
the sign-alternation of `qₙ y − pₙ` (which the repo does not have) and does not need Fibonacci
growth.  Let `m = round (q y)` and, for each `p`, let `c p := q · pₚ − m · qₚ ∈ ℤ`.

* If `c p = 0` then `q = qₚ` — both fractions are in lowest terms (`hcop` and
  `coprime_cfNum_cfK`).
* Otherwise `|c p| ≥ 1`, and expanding `−c p = q (qₚ y − pₚ) − qₚ (q y − m)` against
  `abs_convDen_mul_sub_le` and the goodness hypothesis gives

      1 ≤ 2q / qₚ₊₁ + 2 qₚ / (T q).

So if `q` is *no* convergent denominator, that inequality holds for every `p ≥ 1`, and it is a
**self-propagating bound**: `qₚ ≤ 3q` forces `2qₚ/(Tq) ≤ 6/T ≤ 1/4` (for `T ≥ 24`), hence
`2q/qₚ₊₁ ≥ 3/4`, hence `qₚ₊₁ ≤ 8q/3 ≤ 3q`.  Starting from `q₀ = 1 ≤ 3q` the whole sequence stays
below `3q`, contradicting `qₚ → ∞`.

(The single index `p = 0` is not covered by `abs_convDen_mul_sub_le`; there the base case is
handled directly: `q₁ > 3q` forces `y ≤ 1/q₁ < 1/(3q)`, so `round (q y) = 0`, so `q = 1 = q₀`.)

**Consequence for the route.**  Combined with `le_digit_of_nearInt_le` this makes
`goodDenCountPrim` *equal*, up to `T ↦ (T−4)/2`, to the count of large digits of `y` itself:
the Diophantine hypothesis `GoodDenBoundPrim` is a reformulation of the crux's tail cell, not a
weakening of it.  That is a real constraint on the route — no further slack is available on the
Diophantine side, and the remaining content is entirely the digit statistics of `y`.
-/
import NormalNumbers.VandeheyS7Dioph

namespace NormalNumbers.VandeheyS7

open NormalNumbers Filter

variable {y : ℝ}

/-- Convergent numerators are coprime to the denominators, including at the empty word
(`p₀ = 0`, `q₀ = 1`). -/
lemma coprime_cfNum_cfK' (w : List ℕ) : Nat.Coprime (cfNum w) (cfK w) := by
  cases w with
  | nil => simp [cfNum, cfK]
  | cons a l => exact coprime_cfNum_cfK (by simp)

/-- **The cross-determinant vanishes only at `q = qₚ`.**  If `q pₚ = m qₚ` with both fractions
primitive, the denominators agree. -/
lemma eq_cfK_of_cross_zero {q M : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime M q) (w : List ℕ)
    (h : q * cfNum w = M * cfK w) : q = cfK w := by
  have hPQ := coprime_cfNum_cfK' w
  have h1 : q ∣ cfK w :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop.symm ⟨cfNum w, by rw [h, Nat.mul_comm]⟩
  have h2 : cfK w ∣ q :=
    Nat.Coprime.dvd_of_dvd_mul_left hPQ.symm ⟨M, by rw [Nat.mul_comm (cfNum w) q, h, Nat.mul_comm]⟩
  exact Nat.dvd_antisymm h1 h2

/-- **The propagating inequality.**  If `q` is a primitive `T`-good denominator that is not the
`p`-th convergent denominator, then `1 ≤ 2q/qₚ₊₁ + 2qₚ/(Tq)`. -/
theorem one_le_cross_bound (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T q p : ℕ} (hT : 24 ≤ T) (hq : 1 ≤ q) (hp : 1 ≤ p)
    (hgood : nearInt ((q : ℝ) * y) ≤ 2 / ((T : ℝ) * q))
    (hcop : Nat.Coprime (round ((q : ℝ) * y)).natAbs q)
    (hne : q ≠ cfK (digitWord y p)) :
    (1:ℝ) ≤ 2 * q / (cfK (digitWord y (p + 1)) : ℝ) + 2 * (cfK (digitWord y p) : ℝ) / ((T:ℝ) * q) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hTR : (24:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have hKp := cfK_pos (digitWord_pos hy hmem p)
  have hKp1 := cfK_pos (digitWord_pos hy hmem (p+1))
  set m : ℤ := round ((q : ℝ) * y) with hm
  set P : ℕ := cfNum (digitWord y p) with hP
  set Q : ℕ := cfK (digitWord y p) with hQ
  -- the numerator `m` is nonnegative
  have hgoodabs : |(q:ℝ) * y - (m:ℝ)| ≤ 2 / ((T:ℝ) * q) := hgood
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hbd : 2 / ((T:ℝ) * q) ≤ 1/12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ (T:ℝ))]
  have hmnn : (-1:ℝ) < (m:ℝ) := by
    have h := (abs_le.1 hgoodabs).2
    nlinarith [mul_pos hqR hmem.1]
  have hm0 : (0:ℤ) ≤ m := by
    have : (-1:ℤ) < m := by exact_mod_cast hmnn
    omega
  set M : ℕ := m.natAbs with hM
  have hMcast : ((M:ℤ)) = m := Int.natAbs_of_nonneg hm0
  have hMR : ((M:ℕ):ℝ) = (m:ℝ) := by exact_mod_cast hMcast
  -- the cross term is a nonzero integer
  set c : ℤ := (q:ℤ) * (P:ℤ) - m * (Q:ℤ) with hc
  have hcne : c ≠ 0 := by
    intro h0
    refine hne (eq_cfK_of_cross_zero hq hcop (digitWord y p) ?_)
    have : (q:ℤ) * (P:ℤ) = (M:ℤ) * (Q:ℤ) := by rw [hMcast]; omega
    exact_mod_cast this
  have hcabs : (1:ℝ) ≤ |(c:ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by omega : c ≠ 0)
  -- expand
  have hexp : (c:ℝ) = -((q:ℝ) * ((Q:ℝ) * y - (P:ℝ)) - (Q:ℝ) * ((q:ℝ) * y - (m:ℝ))) := by
    rw [hc]; push_cast; ring
  have happ : |(Q:ℝ) * y - (P:ℝ)| ≤ 2 / (cfK (digitWord y (p+1)) : ℝ) :=
    abs_convDen_mul_sub_le hy hmem hp
  have hsplit : |(c:ℝ)| ≤ (q:ℝ) * |(Q:ℝ) * y - (P:ℝ)| + (Q:ℝ) * |(q:ℝ) * y - (m:ℝ)| := by
    rw [hexp, abs_neg]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hqR.le, abs_of_nonneg hKp.le]
  have h1 : (q:ℝ) * |(Q:ℝ) * y - (P:ℝ)| ≤ (q:ℝ) * (2 / (cfK (digitWord y (p+1)) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left happ hqR.le
  have h2 : (Q:ℝ) * |(q:ℝ) * y - (m:ℝ)| ≤ (Q:ℝ) * (2 / ((T:ℝ) * q)) :=
    mul_le_mul_of_nonneg_left hgoodabs hKp.le
  have : (1:ℝ) ≤ (q:ℝ) * (2 / (cfK (digitWord y (p+1)) : ℝ)) + (Q:ℝ) * (2 / ((T:ℝ) * q)) := by
    linarith
  calc (1:ℝ) ≤ _ := this
    _ = 2 * q / (cfK (digitWord y (p + 1)) : ℝ) + 2 * (Q:ℝ) / ((T:ℝ) * q) := by ring

/-- **Legendre's criterion, in the form the route needs.**  For `T ≥ 24`, every primitive
`T`-good denominator of an irrational `y ∈ (0,1)` is a convergent denominator of `y`. -/
theorem exists_eq_cfK_of_good (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T q : ℕ} (hT : 24 ≤ T) (hq : 1 ≤ q)
    (hgood : nearInt ((q : ℝ) * y) ≤ 2 / ((T : ℝ) * q))
    (hcop : Nat.Coprime (round ((q : ℝ) * y)).natAbs q) :
    ∃ p : ℕ, q = cfK (digitWord y p) := by
  by_contra hcon
  push_neg at hcon
  have hT1 : 1 ≤ T := by omega
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hTR : (24:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  -- base case: `q₁ ≤ 3q`
  have hbase1 : ((cfK (digitWord y 1) : ℕ) : ℝ) ≤ 3 * q := by
    by_contra hbig
    push_neg at hbig
    -- `q₁ = a₁` and `y ≤ 1/a₁ < 1/(3q)`, so `round (q y) = 0`, so `q = 1 = q₀`
    have hw : digitWord y 1 = [cfDigit y 0] := by simp [digitWord]
    have ha1 : 1 ≤ cfDigit y 0 := by
      have := digitWord_pos hy hmem 1
      rw [hw] at this; exact this _ (by simp)
    have hK1 : cfK (digitWord y 1) = cfDigit y 0 := by rw [hw]; rfl
    have hyle : y ≤ 1 / (cfDigit y 0 : ℝ) := ((cfDigit_zero_eq_iff hmem ha1).1 rfl).2
    have haR : (3:ℝ) * q < (cfDigit y 0 : ℝ) := by rw [← hK1]; exact hbig
    have h0 : (0:ℝ) < (cfDigit y 0 : ℝ) := by linarith
    have hqy : (q:ℝ) * y < 1/3 := by
      have hqa : (q:ℝ) / (cfDigit y 0 : ℝ) < 1/3 := by
        rw [div_lt_div_iff₀ h0 (by norm_num)]; linarith
      calc (q:ℝ) * y ≤ (q:ℝ) * (1 / (cfDigit y 0 : ℝ)) := by nlinarith
        _ = (q:ℝ) / (cfDigit y 0 : ℝ) := by ring
        _ < 1/3 := hqa
    have hr0 : round ((q:ℝ) * y) = 0 := by
      refine round_eq_zero_iff.2 ?_
      rw [Set.mem_Ico]
      exact ⟨by nlinarith [mul_pos hqR hmem.1], by linarith⟩
    rw [hr0] at hcop
    simp [Nat.Coprime] at hcop
    exact hcon 0 (by simp [hcop, digitWord, cfK])
  -- propagate `qₚ ≤ 3q` for all `p ≥ 1`
  have hstep : ∀ p : ℕ, 1 ≤ p → ((cfK (digitWord y p) : ℕ) : ℝ) ≤ 3 * q →
      ((cfK (digitWord y (p+1)) : ℕ) : ℝ) ≤ 3 * q := by
    intro p hp hle
    have hKp1 := cfK_pos (digitWord_pos hy hmem (p+1))
    have hb := one_le_cross_bound hy hmem hT hq hp hgood hcop (hcon p)
    have hsmall : 2 * ((cfK (digitWord y p) : ℕ) : ℝ) / ((T:ℝ) * q) ≤ 1/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h34 : (3:ℝ)/4 ≤ 2 * q / (cfK (digitWord y (p+1)) : ℝ) := by linarith
    rw [le_div_iff₀ hKp1] at h34
    linarith
  have hall : ∀ p : ℕ, 1 ≤ p → ((cfK (digitWord y p) : ℕ) : ℝ) ≤ 3 * q := by
    intro p hp
    induction p with
    | zero => omega
    | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact hbase1
        · exact hstep n hn (ih hn)
  -- contradiction with `qₚ → ∞`
  set N : ℕ := max 1 (⌈(3:ℝ) * q⌉₊ + 1) with hNdef
  have h1 : 1 ≤ N := le_max_left _ _
  have hge : N ≤ cfK (digitWord y N) := le_cfK_digitWord hy hmem N
  have hgeR : ((N:ℕ):ℝ) ≤ ((cfK (digitWord y N) : ℕ) : ℝ) := by exact_mod_cast hge
  have hbig : (⌈(3:ℝ) * q⌉₊ + 1 : ℕ) ≤ N := le_max_right _ _
  have hbigR : ((⌈(3:ℝ) * q⌉₊ + 1 : ℕ) : ℝ) ≤ ((N:ℕ):ℝ) := by exact_mod_cast hbig
  have hceil : (3:ℝ) * q ≤ (⌈(3:ℝ) * q⌉₊ : ℝ) := Nat.le_ceil _
  have := hall N h1
  push_cast at hbigR
  linarith

section Audit

#print axioms exists_eq_cfK_of_good
#print axioms one_le_cross_bound

end Audit


/-! ## The converse reduction: the Diophantine count is *equal* to the large-digit count

`largeDigitCount_le_goodDenCountPrim` (lap 33) bounds the number of digits `≥ T` in the first `p`
digits of `y` by the primitive good-denominator count.  Legendre supplies the reverse: every
primitive `T`-good `q ≤ Q` is `qₚ` for some `p ≤ Q`, and past `p = 3` a `T`-good convergent forces
`T ≤ 2 aₚ + 4` (`le_digit_of_nearInt_le`).  So up to `T ↦ (T−4)/2` and an additive `3`, the two
counts are the *same* count.  `GoodDenBoundPrim` is therefore a restatement of the crux's tail
cell, not a reduction of it. -/
theorem goodDenCountPrim_le_largeDigitCount (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    {T Q : ℕ} (hT : 24 ≤ T) :
    goodDenCountPrim y T Q
      ≤ 3 + ((Finset.range (Q + 2)).filter (fun p => T ≤ 2 * cfDigit y p + 4)).card := by
  classical
  set F : Finset ℕ := (Finset.range (Q + 2)).filter (fun p => T ≤ 2 * cfDigit y p + 4) with hF
  set A : Finset ℕ := ({0, 1, 2} : Finset ℕ) ∪ F with hA
  have hsub : ((Finset.Icc 1 Q).filter
      (fun q : ℕ => nearInt ((q : ℝ) * y) ≤ 2 / ((T : ℝ) * q) ∧
        Nat.Coprime (round ((q : ℝ) * y)).natAbs q))
      ⊆ A.image (fun p => cfK (digitWord y p)) := by
    intro q hq
    obtain ⟨hmem', hgc⟩ := Finset.mem_filter.1 hq
    obtain ⟨hgood, hcop⟩ := hgc
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.1 hmem'
    obtain ⟨p, hp⟩ := exists_eq_cfK_of_good hy hmem hT hq1 hgood hcop
    have hple : p ≤ Q := le_trans (le_cfK_digitWord hy hmem p) (by omega)
    refine Finset.mem_image.2 ⟨p, ?_, hp.symm⟩
    rw [hA]
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · exact Finset.mem_union_left _ (by interval_cases p <;> simp)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩)
      -- past index `3` the convergent is `T`-good, so its next digit is large
      have hvpos := digitWord_pos hy hmem (p + 1)
      have hfib : Nat.fib 5 ≤ Nat.fib (p + 2) := Nat.fib_mono (by omega)
      have hbig : 4 < cfK (digitWord y (p + 1)) := by
        have h := fib_le_cfK (digitWord y (p + 1)) hvpos
        rw [digitWord_length, show p + 1 + 1 = p + 2 from rfl] at h
        have h5 : Nat.fib 5 = 5 := by decide
        omega
      have hgood' : |(cfK (digitWord y p) : ℝ) * y
          - (round ((cfK (digitWord y p) : ℝ) * y) : ℝ)|
          ≤ 2 / ((T : ℝ) * (cfK (digitWord y p) : ℝ)) := by
        rw [← hp]; exact hgood
      have := le_digit_of_nearInt_le hy hmem (by omega : 1 ≤ p) hbig hgood'
      have : (T:ℝ) ≤ ((2 * cfDigit y p + 4 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  calc goodDenCountPrim y T Q ≤ (A.image (fun p => cfK (digitWord y p))).card :=
        Finset.card_le_card hsub
    _ ≤ A.card := Finset.card_image_le
    _ ≤ ({0, 1, 2} : Finset ℕ).card + F.card := Finset.card_union_le _ _
    _ ≤ 3 + F.card := by simp

section Audit2

#print axioms goodDenCountPrim_le_largeDigitCount

end Audit2

end NormalNumbers.VandeheyS7
