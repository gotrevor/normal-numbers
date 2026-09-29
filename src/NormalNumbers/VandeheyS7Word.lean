/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Merge
import NormalNumbers.VandeheyS7Convergent

/-!
# The word matrix: Fibonacci growth of both rows, and determinant `±1`

`VandeheyS7Merge` reduced merging to a DIAMETER bound for the input word alone
(`hdist_comp_le`: the initial state can only shrink the spread the word produces).  This module
supplies the two facts that make that diameter tend to zero.

## The word state

`wordState w = A_{a₁} ⋯ A_{aₙ}` (`wordState`), built by prepending, and `runWord s w =
s.comp (wordState w)` (`runWord_eq_comp`), so the machine's state really is `initial · word`.

## Both rows grow like Fibonacci

Prepending a branch acts on the rows by

    A_a · (a b ; c d)  =  (c, d ; a + A c, b + A d),      A = max 1 a ≥ 1,

so the new FIRST row is the old second row, and the new second row dominates the sum of the two
old rows.  Writing `rowMin₁ = min a b` and `rowMin₂ = min c d`, that is exactly

    rowMin₁(A_a · W) = rowMin₂(W),    rowMin₂(A_a · W) ≥ rowMin₁(W) + rowMin₂(W),

a Fibonacci recursion with no arithmetic in it at all (`rowMin_one_prepend`,
`rowMin_two_prepend`).  Hence `fib_le_rowMin` : every entry of a word of length `n` is at least
`fib (n-1)`, and in particular **all four entries tend to infinity**.  This is the growth that,
with `det = ±1`, forces `a d / (b c) = 1 ± 1/(b c) → 1`, i.e. image diameter `→ 0`.

Note what is NOT used: no continuant identification, no Gauss measure, no CF theory.  The
recursion is read straight off the matrix product, so it holds for every digit sequence including
the ones a CF-normal `x` produces.

## Determinant

`det_comp` (multiplicativity, a ring identity) plus `det_gaussBranch = -1` give
`det (wordState w) = (-1)^(length w)` (`det_wordState`), so `|det| = 1` exactly.

## Guard rule

Content locator: `rowMin_two_prepend` — the whole growth is in this one inequality, and it is
where `A ≥ 1` (the totalisation `max 1 a`) is spent.  Degenerate case: `rowMin_idState` — the
empty word has `rowMin₁ = rowMin₂ = 0`, so the growth cannot start at length `0`; it starts at
length `1`, which is why `fib_le_rowMin` is offset by one.
-/

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- Composition is associative (a matrix product). -/
theorem comp_assoc (s t u : MobState) : (s.comp t).comp u = s.comp (t.comp u) := by
  cases s; cases t; cases u
  simp only [comp, MobState.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- The word matrix `A_{a₁} ⋯ A_{aₙ}`. -/
noncomputable def wordState : List ℕ → MobState
  | [] => idState
  | a :: w => (gaussBranch a).comp (wordState w)

@[simp] theorem wordState_nil : wordState [] = idState := rfl

@[simp] theorem wordState_cons (a : ℕ) (w : List ℕ) :
    wordState (a :: w) = (gaussBranch a).comp (wordState w) := rfl

/-- The machine's state after reading `w` really is `initial · word`. -/
theorem runWord_eq_comp (s : MobState) (w : List ℕ) : runWord s w = s.comp (wordState w) := by
  induction w generalizing s with
  | nil => simp [comp_idState]
  | cons a w ih => rw [runWord_cons, ih, comp_assoc]; rfl

/-! ## The two row minima -/

/-- The smaller entry of the first row. -/
noncomputable def rowMin₁ (s : MobState) : ℝ := min s.a s.b

/-- The smaller entry of the second row. -/
noncomputable def rowMin₂ (s : MobState) : ℝ := min s.c s.d

theorem rowMin₁_nonneg (s : MobState) : 0 ≤ rowMin₁ s := le_min s.ha s.hb
theorem rowMin₂_nonneg (s : MobState) : 0 ≤ rowMin₂ s := le_min s.hc s.hd.le

/-- Degenerate case: the empty word has both minima `0`, so the growth starts at length `1`. -/
theorem rowMin_idState : rowMin₁ idState = 0 ∧ rowMin₂ idState = 0 := by
  constructor <;> simp [rowMin₁, rowMin₂, idState]

/-- Prepending a branch moves the second row up into the first. -/
theorem rowMin_one_prepend (a : ℕ) (W : MobState) :
    rowMin₁ ((gaussBranch a).comp W) = rowMin₂ W := by
  simp [rowMin₁, rowMin₂, gaussBranch]

/-- **The growth step.**  The new second row dominates the sum of the two old rows; this is where
`A = max 1 a ≥ 1` is spent. -/
theorem rowMin_two_prepend (a : ℕ) (W : MobState) :
    rowMin₁ W + rowMin₂ W ≤ rowMin₂ ((gaussBranch a).comp W) := by
  have hA : (1:ℝ) ≤ ((max 1 a : ℕ) : ℝ) := one_le_gaussBranch_d a
  have hc : rowMin₂ W ≤ W.c := min_le_left _ _
  have hd : rowMin₂ W ≤ W.d := min_le_right _ _
  have ha : rowMin₁ W ≤ W.a := min_le_left _ _
  have hb : rowMin₁ W ≤ W.b := min_le_right _ _
  have h2 : 0 ≤ rowMin₂ W := rowMin₂_nonneg W
  have hcc : ((gaussBranch a).comp W).c = W.a + ((max 1 a : ℕ) : ℝ) * W.c := by
    simp [gaussBranch]
  have hdd : ((gaussBranch a).comp W).d = W.b + ((max 1 a : ℕ) : ℝ) * W.d := by
    simp [gaussBranch]
  simp only [rowMin₂] at hc hd h2 ⊢
  simp only [hcc, hdd, le_min_iff]
  constructor <;> nlinarith [W.hc, W.hd.le, ha, hb, hc, hd, h2, hA]

/-- **Fibonacci growth.**  Every entry of a word matrix of length `n` is at least `fib (n-1)`;
in particular all four entries tend to infinity. -/
theorem fib_le_rowMin : ∀ w : List ℕ,
    ((Nat.fib w.length : ℝ) ≤ rowMin₂ (wordState w)
      ∧ (Nat.fib (w.length - 1) : ℝ) ≤ rowMin₁ (wordState w))
  | [] => by
      refine ⟨?_, ?_⟩ <;> simp [rowMin₁, rowMin₂, idState]
  | [a] => by
      constructor
      · simp only [wordState_cons, wordState_nil, List.length_singleton, Nat.fib_one]
        rw [rowMin₂]
        have : ((gaussBranch a).comp idState) = gaussBranch a := comp_idState _
        rw [this]
        exact le_min (by simp [gaussBranch]) (by exact_mod_cast one_le_gaussBranch_d a)
      · simp [rowMin₁, gaussBranch, comp_idState]
  | a :: b :: w => by
      obtain ⟨h2, h1⟩ := fib_le_rowMin (b :: w)
      have hlen : (b :: w).length = w.length + 1 := rfl
      constructor
      · have hstep := rowMin_two_prepend a (wordState (b :: w))
        have hfib : (Nat.fib ((a :: b :: w).length) : ℝ)
            = (Nat.fib ((b :: w).length - 1) : ℝ) + (Nat.fib ((b :: w).length) : ℝ) := by
          simp only [List.length_cons, hlen]
          push_cast [Nat.fib_add_two]
          ring
        rw [wordState_cons, hfib]
        linarith
      · rw [wordState_cons, rowMin_one_prepend]
        simpa using h2

/-! ## Determinant -/

/-- The determinant of a state. -/
noncomputable def det (s : MobState) : ℝ := s.a * s.d - s.b * s.c

theorem det_comp (s t : MobState) : det (s.comp t) = det s * det t := by
  simp only [det, comp_a, comp_b, comp_c, comp_d]; ring

@[simp] theorem det_gaussBranch (a : ℕ) : det (gaussBranch a) = -1 := by
  simp [det, gaussBranch]

@[simp] theorem det_idState : det idState = 1 := by simp [det, idState]

/-- The word matrix is unimodular. -/
theorem det_wordState (w : List ℕ) : det (wordState w) = (-1) ^ w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [wordState_cons, det_comp, det_gaussBranch, ih, List.length_cons, pow_succ]
      ring

theorem abs_det_wordState (w : List ℕ) : |det (wordState w)| = 1 := by
  rw [det_wordState, abs_pow, abs_neg, abs_one, one_pow]

/-! ## The diameter bound, and the spread of a long word -/

/-- The image of a positive state has `hdist`-diameter at most `log (a d / (b c))`: the Birkhoff
diameter, now as a statement about `hdist` and not just about ratios. -/
theorem hdist_mob_le_log (s : MobState) (ha : 0 < s.a) (hb : 0 < s.b) (hc : 0 < s.c)
    (hdet : 0 ≤ det s) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hdist (s.mob x) (s.mob y) ≤ Real.log (s.a * s.d / (s.b * s.c)) := by
  have hd : 0 < s.d := s.hd
  have hdet' : 0 ≤ s.a * s.d - s.b * s.c := hdet
  have hpx : 0 < s.mob x := s.mob_pos hx
  have hpy : 0 < s.mob y := s.mob_pos hy
  have h1 : s.mob x / s.mob y ≤ s.a * s.d / (s.b * s.c) :=
    hdist_image_le ha hb hc hd hdet' hx hy
  have h2 : s.mob y / s.mob x ≤ s.a * s.d / (s.b * s.c) :=
    hdist_image_le ha hb hc hd hdet' hy hx
  have hK : 0 < s.a * s.d / (s.b * s.c) := by positivity
  have hl1 := Real.log_le_log (div_pos hpx hpy) h1
  have hl2 := Real.log_le_log (div_pos hpy hpx) h2
  have hinv : Real.log (s.mob y / s.mob x) = -Real.log (s.mob x / s.mob y) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv] at hl2
  rw [hdist, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Every entry of a word of length `≥ 3` is positive, with the Fibonacci lower bound. -/
theorem wordState_entries_pos {w : List ℕ} (h3 : 3 ≤ w.length) :
    0 < (wordState w).a ∧ 0 < (wordState w).b ∧ 0 < (wordState w).c := by
  obtain ⟨h2, h1⟩ := fib_le_rowMin w
  have hfib : (1:ℝ) ≤ (Nat.fib (w.length - 1) : ℝ) := by
    have : Nat.fib 2 ≤ Nat.fib (w.length - 1) := Nat.fib_mono (by omega)
    simpa using (by exact_mod_cast this : (Nat.fib 2 : ℝ) ≤ (Nat.fib (w.length - 1) : ℝ))
  have hfib2 : (1:ℝ) ≤ (Nat.fib w.length : ℝ) := by
    have : Nat.fib 2 ≤ Nat.fib w.length := Nat.fib_mono (by omega)
    simpa using (by exact_mod_cast this : (Nat.fib 2 : ℝ) ≤ (Nat.fib w.length : ℝ))
  refine ⟨?_, ?_, ?_⟩
  · have := min_le_left (wordState w).a (wordState w).b
    rw [← rowMin₁] at this; linarith
  · have := min_le_right (wordState w).a (wordState w).b
    rw [← rowMin₁] at this; linarith
  · have := min_le_left (wordState w).c (wordState w).d
    rw [← rowMin₂] at this; linarith

/-- **The spread of a long word goes to zero, at a Fibonacci rate.**  Combined with
`hdist_comp_le` this bounds the spread from EVERY initial state at once: the loss of memory,
quantitatively, with `det = ±1` doing all the work. -/
theorem spread_wordState_le {w : List ℕ} (heven : Even w.length) (h3 : 3 ≤ w.length)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hdist ((wordState w).mob x) ((wordState w).mob y)
      ≤ 1 / ((Nat.fib (w.length - 1) : ℝ) * (Nat.fib w.length : ℝ)) := by
  obtain ⟨ha, hb, hc⟩ := wordState_entries_pos h3
  obtain ⟨hr2, hr1⟩ := fib_le_rowMin w
  have hdet : det (wordState w) = 1 := by
    rw [det_wordState]; exact heven.neg_one_pow
  have hdet0 : 0 ≤ det (wordState w) := by rw [hdet]; norm_num
  have hbc : 0 < (wordState w).b * (wordState w).c := mul_pos hb hc
  -- `b ≥ fib (n-1)`, `c ≥ fib n`
  have hbf : (Nat.fib (w.length - 1) : ℝ) ≤ (wordState w).b := by
    have := min_le_right (wordState w).a (wordState w).b
    rw [← rowMin₁] at this; linarith
  have hcf : (Nat.fib w.length : ℝ) ≤ (wordState w).c := by
    have := min_le_left (wordState w).c (wordState w).d
    rw [← rowMin₂] at this; linarith
  have hfib : (1:ℝ) ≤ (Nat.fib (w.length - 1) : ℝ) := by
    have : Nat.fib 2 ≤ Nat.fib (w.length - 1) := Nat.fib_mono (by omega)
    simpa using (by exact_mod_cast this : (Nat.fib 2 : ℝ) ≤ (Nat.fib (w.length - 1) : ℝ))
  have hprod : (Nat.fib (w.length - 1) : ℝ) * (Nat.fib w.length : ℝ)
      ≤ (wordState w).b * (wordState w).c := by
    have h0 : (0:ℝ) ≤ (Nat.fib w.length : ℝ) := by positivity
    nlinarith [hbf, hcf, hfib, h0, hb.le, hc.le]
  have hfib2 : (1:ℝ) ≤ (Nat.fib w.length : ℝ) := by
    have : Nat.fib 2 ≤ Nat.fib w.length := Nat.fib_mono (by omega)
    simpa using (by exact_mod_cast this : (Nat.fib 2 : ℝ) ≤ (Nat.fib w.length : ℝ))
  have hprodpos : (0:ℝ) < (Nat.fib (w.length - 1) : ℝ) * (Nat.fib w.length : ℝ) := by
    nlinarith [hfib, hfib2]
  calc hdist ((wordState w).mob x) ((wordState w).mob y)
      ≤ Real.log ((wordState w).a * (wordState w).d
          / ((wordState w).b * (wordState w).c)) :=
        hdist_mob_le_log _ ha hb hc hdet0 hx hy
    _ ≤ (wordState w).a * (wordState w).d / ((wordState w).b * (wordState w).c) - 1 :=
        Real.log_le_sub_one_of_pos
          (div_pos (mul_pos ha (wordState w).hd) (mul_pos hb hc))
    _ = 1 / ((wordState w).b * (wordState w).c) := by
        field_simp
        linarith [hdet, (by rw [det] : det (wordState w)
          = (wordState w).a * (wordState w).d - (wordState w).b * (wordState w).c)]
    _ ≤ 1 / ((Nat.fib (w.length - 1) : ℝ) * (Nat.fib w.length : ℝ)) := by
        exact one_div_le_one_div_of_le hprodpos hprod

/-- **Loss of memory, uniformly over initial states.**  After a long enough input word the
machine's output spread is `O(1/fib(n)^2)` NO MATTER what state it started in — the `ℤ[φ]`
state set may be infinite, but it is invisible at this range.  This is the replacement for the
finite-chain merging of Saloff-Coste–Zúñiga that `infinite_zPhi_abs_le_one` rules out. -/
theorem spread_runWord_le (s : MobState) {w : List ℕ} (heven : Even w.length)
    (h3 : 3 ≤ w.length) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hdist ((runWord s w).mob x) ((runWord s w).mob y)
      ≤ 1 / ((Nat.fib (w.length - 1) : ℝ) * (Nat.fib w.length : ℝ)) := by
  rw [runWord_eq_comp]
  exact le_trans (hdist_comp_le s (wordState w) hx hy) (spread_wordState_le heven h3 hx hy)

end MobState

/-! ## From the projective bound to an absolute one

The Hilbert metric is the right instrument for the contraction, but CF digits are read off an
ABSOLUTE position: the digit of `u` is `⌊1/u⌋`, and `u, v` have the same digit as soon as
`|u − v|` is smaller than the distance from `u` to the nearest cylinder endpoint.  So the merging
bound has to be converted, and the conversion is exact:

    hdist u v ≤ ε  ⟹  |u − v| ≤ max u v · (exp ε − 1).

Since the machine's output point lies in `(0,1)`, the factor `max u v` is harmless and the bound
is `exp ε − 1 ≤ ε exp ε`.  With `ε = 1/(fib(n-1) fib(n))` this is summably small, which is what a
boundary-avoidance (`ρ(∂U) = 0`) argument needs.
-/

namespace MobState

/-- `hdist u v ≤ ε` bounds the ABSOLUTE difference by `max u v · (exp ε − 1)`. -/
theorem abs_sub_le_of_hdist_le {u v ε : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : hdist u v ≤ ε) : |u - v| ≤ max u v * (Real.exp ε - 1) := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) h
  have habs : |Real.log (u / v)| ≤ ε := h
  obtain ⟨hlo, hup⟩ := abs_le.1 habs
  -- `u/v ≤ exp ε` and `v/u ≤ exp ε`
  have h1 : u / v ≤ Real.exp ε := by
    have := Real.exp_le_exp.2 hup
    rwa [Real.exp_log (div_pos hu hv)] at this
  have h2 : v / u ≤ Real.exp ε := by
    have hinv : Real.log (v / u) = -Real.log (u / v) := by rw [← Real.log_inv, inv_div]
    have : Real.log (v / u) ≤ ε := by rw [hinv]; linarith
    have := Real.exp_le_exp.2 this
    rwa [Real.exp_log (div_pos hv hu)] at this
  have hu' : u ≤ v * Real.exp ε := by
    rw [div_le_iff₀ hv] at h1; linarith
  have hv' : v ≤ u * Real.exp ε := by
    rw [div_le_iff₀ hu] at h2; linarith
  rcases le_total u v with hle | hle
  · rw [abs_of_nonpos (by linarith), max_eq_right hle]
    nlinarith [hv', hu.le]
  · rw [abs_of_nonneg (by linarith), max_eq_left hle]
    nlinarith [hu', hv.le]

/-- **Merging in absolute terms.**  The machine's output points from two different inputs, after
a long common word, differ by `O(exp(1/fib²) − 1)` regardless of the initial state — and the
initial state still does not appear. -/
theorem abs_sub_runWord_le (s : MobState) {w : List ℕ} (heven : Even w.length)
    (h3 : 3 ≤ w.length) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |(runWord s w).mob x - (runWord s w).mob y|
      ≤ max ((runWord s w).mob x) ((runWord s w).mob y) *
          (Real.exp (1 / ((Nat.fib (w.length - 1) : ℝ) * (Nat.fib w.length : ℝ))) - 1) :=
  abs_sub_le_of_hdist_le ((runWord s w).mob_pos hx) ((runWord s w).mob_pos hy)
    (spread_runWord_le s heven h3 hx hy)

/-- Content locator: at `ε = 0` the bound collapses to `u = v`, so all the content is in the
exponential factor and none in the `max`. -/
theorem abs_sub_le_of_hdist_le_zero {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : hdist u v ≤ 0) : u = v := by
  have := abs_sub_le_of_hdist_le hu hv h
  simp only [Real.exp_zero, sub_self, mul_zero] at this
  have := abs_nonpos_iff.1 this
  linarith [sub_eq_zero.1 this]

end MobState

/-! ## The word matrix IS the continuant matrix

The handoff's queued bookkeeping: identify the pullback matrix's columns with `Conv.of`'s
convergents.  It lands on `wordState` (this module), and the identification is exact —
**`wordState w` is the TRANSPOSE of the continuant matrix**:

    wordState w  =  (p', p ; q', q)   for   Conv.of w = ⟨p', q', p, q⟩ .

Checked against both recursions: appending a digit sends `(a,b;c,d) ↦ (b, a + e·b ; d, c + e·d)`
on the word matrix and `(p',q',p,q) ↦ (p, q, p' + e·p, q' + e·q)` on `Conv`, and under the
transpose identification these are the same map.  The base cases agree too
(`idState = (1,0;0,1)`, `Conv.of [] = ⟨1,0,0,1⟩`).

The transpose is the content, and it is not a convention slip: the word matrix is built by
PREPENDING branches (which is what the machine does, reading input) while `Conv` is built by
APPENDING digits (which is what the continuant recursion does).  Those are transpose-conjugate,
and that is why lap 13's Fibonacci growth of the ROWS is the same statement as the classical
growth of the convergent denominators.
-/

namespace MobState

theorem idState_comp (t : MobState) : idState.comp t = t := by
  cases t
  simp [comp, idState]

/-- Appending a digit multiplies on the right. -/
theorem wordState_append (w : List ℕ) (a : ℕ) :
    wordState (w ++ [a]) = (wordState w).comp (gaussBranch a) := by
  induction w with
  | nil => rw [List.nil_append, wordState_cons, wordState_nil, comp_idState, idState_comp]
  | cons b w ih =>
      rw [List.cons_append, wordState_cons, ih, wordState_cons, comp_assoc]

/-- **The word matrix is the transpose of the continuant matrix.** -/
theorem wordState_eq_conv (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    (wordState w).a = ((Conv.of w).p' : ℝ) ∧ (wordState w).b = ((Conv.of w).p : ℝ) ∧
      (wordState w).c = ((Conv.of w).q' : ℝ) ∧ (wordState w).d = ((Conv.of w).q : ℝ) := by
  induction w using List.reverseRecOn with
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [idState, Conv.of]
  | append_singleton w a ih =>
      have hposw : ∀ b ∈ w, 1 ≤ b := fun b hb => hpos b (by simp [hb])
      have hposa : 1 ≤ a := hpos a (by simp)
      obtain ⟨ha, hb, hc, hd⟩ := ih hposw
      have hmax : ((max 1 a : ℕ) : ℝ) = (a : ℝ) := by
        rw [max_eq_right hposa]
      rw [wordState_append, Conv.of_append_digit]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [comp_a, gaussBranch, Conv.step]
        rw [hb]; ring
      · simp only [comp_b, gaussBranch, Conv.step, hmax]
        push_cast
        rw [ha, hb]; ring
      · simp only [comp_c, gaussBranch, Conv.step]
        rw [hd]; ring
      · simp only [comp_d, gaussBranch, Conv.step, hmax]
        push_cast
        rw [hc, hd]; ring

end MobState

section Audit

#print axioms MobState.runWord_eq_comp
#print axioms MobState.wordState_eq_conv
#print axioms MobState.fib_le_rowMin
#print axioms MobState.det_wordState
#print axioms MobState.spread_wordState_le
#print axioms MobState.spread_runWord_le
#print axioms MobState.abs_sub_le_of_hdist_le
#print axioms MobState.abs_sub_runWord_le

end Audit

end NormalNumbers.VandeheyS7
