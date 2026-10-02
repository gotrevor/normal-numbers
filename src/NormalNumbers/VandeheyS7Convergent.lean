/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Burst

/-!
# The convergent gap: `far = ((q + q')/q) · near`, and that is at most `2`

`VandeheyS7Burst` reduced the window lemma to one geometric input, `ConvergentGap`: the emitted
word's convergent `β = p_{k−1}/q_{k−1}` sits outside the cylinder `[e₁,…,e_k]` with

    far / near  ≤  2 ,

where `far`, `near` are its distances to the two endpoints of that cylinder.  This file proves it,
for every word, with no reference to the machine.

## The computation

With `Δ = p q' − p' q` (the continuant determinant, `Δ² = 1`), the two distances are

    p/q − p'/q'                    = Δ / (q q') ,
    (p + p')/(q + q') − p'/q'      = Δ / ((q + q') q') ,

so their ratio is `(q + q')/q` **and `Δ` cancels**.  The determinant is therefore not needed at
its value `±1` — only as a nonzero — and the bound is exactly `1 + q'/q ≤ 2`, from `q' ≤ q`.
That is `conv_far_eq` and `conv_ratio_le_two`.

Both facts are invariants of one step of the continuant recursion
`(p', q', p, q) ↦ (p, q, p' + a·p, q' + a·q)`, carried by `ConvGood` and pushed along the fold.
The burst length `k` is the length of the word and appears nowhere in the bound.

## Guard rule

Content locator: `conv_single`, the one-digit case, where `β = 0` and the bound reads
`(e + 1)/e ≤ 2` — visible by hand, and the source of the constant.  Degenerate case: the fold's
start `(1, 0, 0, 1)` has `q' = 0`, so `β` is undefined there; `one_le_convQ'` records that one
digit is enough to fix it, which is why every statement below asks `w ≠ []`.
-/

namespace NormalNumbers.VandeheyS7

/-- The continuant state: the previous and current convergents `(p', q')`, `(p, q)`. -/
structure Conv where
  p' : ℤ
  q' : ℤ
  p : ℤ
  q : ℤ

namespace Conv

/-- One step of the continuant recursion, reading the digit `a`. -/
def step (c : Conv) (a : ℕ) : Conv := ⟨c.p, c.q, c.p' + a * c.p, c.q' + a * c.q⟩

/-- The continuants of a word, read left to right from `(p₋₁, q₋₁, p₀, q₀) = (1, 0, 0, 1)`. -/
def of (w : List ℕ) : Conv := w.foldl step ⟨1, 0, 0, 1⟩

@[simp] theorem of_nil : of [] = ⟨1, 0, 0, 1⟩ := rfl

theorem of_append_digit (w : List ℕ) (a : ℕ) : of (w ++ [a]) = (of w).step a := by
  simp [of, List.foldl_append]

/-- The invariant carried along the fold. -/
def Good (c : Conv) : Prop :=
  0 ≤ c.p' ∧ 0 ≤ c.q' ∧ 0 ≤ c.p ∧ 1 ≤ c.q ∧ c.q' ≤ c.q ∧ (c.p * c.q' - c.p' * c.q) ^ 2 = 1

theorem good_start : Good ⟨1, 0, 0, 1⟩ := by
  refine ⟨zero_le_one, le_refl 0, le_refl 0, le_refl 1, zero_le_one, ?_⟩
  norm_num

theorem Good.step {c : Conv} (h : Good c) {a : ℕ} (ha : 1 ≤ a) : Good (c.step a) := by
  obtain ⟨hp', hq', hp, hq, hqq, hdet⟩ := h
  have ha' : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  refine ⟨hp, by simpa [Conv.step] using (by linarith : (0:ℤ) ≤ c.q),
    by simp only [Conv.step]; nlinarith,
    by simp only [Conv.step]; nlinarith,
    by simp only [Conv.step]; nlinarith, ?_⟩
  simp only [Conv.step]
  linear_combination hdet

theorem good_of (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) : Good (of w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using good_start
  | append_singleton v a ih =>
      rw [of_append_digit]
      exact (ih fun x hx => hpos x (by simp [hx])).step (hpos a (by simp))

/-- One digit already makes `q'` positive, so `β = p'/q'` is defined.  (At the fold's start
`q' = 0` and it is not — which is why every statement below asks `w ≠ []`.) -/
theorem one_le_q'_of (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) : 1 ≤ (of w).q' := by
  obtain ⟨v, a, rfl⟩ : ∃ v a, w = v ++ [a] :=
    ⟨w.dropLast, w.getLast hw, (List.dropLast_append_getLast hw).symm⟩
  rw [of_append_digit]
  exact (good_of v fun x hx => hpos x (by simp [hx])).2.2.2.1

@[simp] theorem of_single (a : ℕ) : of [a] = ⟨0, 1, 1, a⟩ := by
  simp [of, step]

end Conv

/-! ## The gap identity -/

open Conv

variable (w : List ℕ)

/-- **The gap identity.**  The far distance is `(q + q')/q` times the near distance — the
determinant `Δ = p q' − p' q` cancels, so its value `±1` is not needed, only that it is there. -/
theorem conv_far_eq (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    (((of w).p : ℝ) / (of w).q - ((of w).p' : ℝ) / (of w).q')
      = ((((of w).q : ℝ) + (of w).q') / (of w).q) *
        ((((of w).p : ℝ) + (of w).p') / (((of w).q : ℝ) + (of w).q')
          - ((of w).p' : ℝ) / (of w).q') := by
  obtain ⟨-, -, -, hq, -, -⟩ := good_of w hpos
  have hq1 : (1 : ℝ) ≤ ((of w).q : ℝ) := by exact_mod_cast hq
  have hq'1 : (1 : ℝ) ≤ ((of w).q' : ℝ) := by exact_mod_cast one_le_q'_of w hw hpos
  have hqne : ((of w).q : ℝ) ≠ 0 := by linarith
  have hq'ne : ((of w).q' : ℝ) ≠ 0 := by linarith
  have hsum : ((of w).q : ℝ) + (of w).q' ≠ 0 := by linarith
  field_simp
  ring

/-- The gap constant is between `1` and `2`: `q' ≤ q` is the whole of it, and the word's length
— the burst length — does not appear. -/
theorem conv_ratio_le_two (hpos : ∀ a ∈ w, 1 ≤ a) :
    (((of w).q : ℝ) + (of w).q') / (of w).q ≤ 2 ∧
      1 ≤ (((of w).q : ℝ) + (of w).q') / (of w).q := by
  obtain ⟨-, hq'0, -, hq, hqq, -⟩ := good_of w hpos
  have hq1 : (1 : ℝ) ≤ ((of w).q : ℝ) := by exact_mod_cast hq
  have hqq' : ((of w).q' : ℝ) ≤ ((of w).q : ℝ) := by exact_mod_cast hqq
  have hq'0' : (0 : ℝ) ≤ ((of w).q' : ℝ) := by exact_mod_cast hq'0
  constructor
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [le_div_iff₀ (by linarith)]; linarith

/-- **`ConvergentGap`, discharged as an inequality between distances.**  `far ≤ 2 · near`, for
every word of positive digits, of every length. -/
theorem conv_far_le_two_near (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    |((of w).p : ℝ) / (of w).q - ((of w).p' : ℝ) / (of w).q'|
      ≤ 2 * |(((of w).p : ℝ) + (of w).p') / (((of w).q : ℝ) + (of w).q')
          - ((of w).p' : ℝ) / (of w).q'| := by
  obtain ⟨h2, h1⟩ := conv_ratio_le_two w hpos
  rw [conv_far_eq w hw hpos, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ _)]
  exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)

/-- The ordered form, which is what `ConvergentGap` asks for. -/
theorem gap_of_far_eq {β u v k : ℝ} (hk : k ≤ 2) (hβ : β < u) (h : v - β = k * (u - β)) :
    v - β ≤ 2 * (u - β) := by
  rw [h]
  nlinarith

/-- **Content locator**: one digit, where the constant is visible by hand.  `β = 0`, the cylinder
is `(1/(e+1), 1/e)`, and the ratio is `(e + 1)/e ≤ 2`. -/
theorem conv_single (e : ℕ) (he : 1 ≤ e) :
    (((of [e]).q : ℝ) + (of [e]).q') / (of [e]).q = ((e : ℝ) + 1) / e := by
  have : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  simp [of_single]

section Audit

#print axioms conv_far_eq
#print axioms conv_far_le_two_near
#print axioms Conv.good_of

end Audit

end NormalNumbers.VandeheyS7
