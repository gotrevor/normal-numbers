/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDefs

/-!
# W1 — the CF cylinder toolkit (scaffold)

Work package W1 of expedition B5′ (`KHINCHIN.md`): the elementary continuant
and cylinder-measure algebra of Becher–Yuhjtman §1.1, stated here and left
`sorry` for the campaign.  NB we prove the Euler gluing identity by list
induction instead of B–Y's `α_{r,s}`/`Ω_{r,s}` subset combinatorics (their
Prop 2) — same content, far friendlier induction; these are internal
lemmas, not paper-pinned statements.

Statement plan (provenance in each docstring):
* `cfK_append` — Euler's continuant gluing identity.
* `cfK_drop_one_le`, `cfK_dropLast_le` — monotonicity under digit removal.
* `cfK_mul_le_append`, `cfK_append_le` — quasi-multiplicativity
  `q(a)q(b) ≤ q(ab) ≤ 2q(a)q(b)` (B–Y Lemma 3.1).
* `fib_le_cfK` — Fibonacci lower bound `qₙ ≥ fib (n+1)` (deterministic
  cylinder-length upper bound; replaces the lower half of B–Y Lemma 5).
* `cfVal_eq_div` — `[0;a₁…aₙ] = pₙ/qₙ`.
* `volume_cfCylinder` — `|I_w| = 1/(qₙ(qₙ + qₙ₋₁))`.
* `volume_cylinder_append_le`, `le_volume_cylinder_append` — bounded
  distortion `|I_a||I_b|/2 ≤ |I_{ab}| ≤ 2|I_a||I_b|` (B–Y Lemma 3.2).
* `tailDensity_mem_Icc`, `cylMap_denom_ratio_le` — the `[1/2, 2]` density
  window and the branch-derivative ratio bound (gateway to W3).

Hand-checked anchors (frozen with the statements, per the planted-scaffold
doctrine): `K(1,2,3) = 10` with `[0;1,2,3] = 7/10`; `K(2) · (K(2) + K()) = 6`
matches `|I_{[2]}| = |(1/3, 1/2]| = 1/6`; the gluing anchor
`K(1,2,3,4) = K(1,2)K(3,4) + K(1)K(4) = 39 + 4 = 43`.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Anchors (kernel-checked) -/

example : cfK [1, 2, 3] = 10 := by decide
example : cfVal [1, 2, 3] = 7 / 10 := by norm_num [cfVal]
example : cfK [2] * (cfK [2] + cfK ([2].dropLast)) = 6 := by decide
example : cfK ([1, 2] ++ [3, 4]) =
    cfK [1, 2] * cfK [3, 4] + cfK [1] * cfK [4] := by decide

/-! ## Continuant recursion helpers -/

/-- Head recursion for nonempty tails: `K(a::m) = a·K(m) + K(m.drop 1)`. -/
private lemma cfK_cons (a : ℕ) {m : List ℕ} (hm : m ≠ []) :
    cfK (a :: m) = a * cfK m + cfK (m.drop 1) := by
  cases m with
  | nil => exact absurd rfl hm
  | cons b l => rfl

/-- Continuants of genuine digit words are positive. -/
private lemma one_le_cfK (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) : 1 ≤ cfK w := by
  induction w using cfK.induct with
  | case1 => simp [cfK]
  | case2 a => simpa [cfK] using hpos a (by simp)
  | case3 a b l ih1 _ =>
      have ha : 1 ≤ a := hpos a (by simp)
      have h1 : 1 ≤ cfK (b :: l) := ih1 fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      have := Nat.mul_le_mul ha h1
      simp only [cfK]; omega

/-! ## Continuant algebra -/

/-- **Euler's gluing identity** (B–Y Prop 2.3, list form): for nonempty `w`
and `u`, `K(wu) = K(w)K(u) + K(w⁻)K(u⁻)` where `w⁻` drops the last digit of
`w` and `u⁻` drops the first digit of `u`.  A polynomial identity — no
digit-positivity needed. -/
theorem cfK_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ []) :
    cfK (w ++ u) = cfK w * cfK u + cfK w.dropLast * cfK (u.drop 1) := by
  revert hw
  induction w using cfK.induct with
  | case1 => intro hw; exact absurd rfl hw
  | case2 a =>
      intro _
      simp only [List.cons_append, List.nil_append, cfK_cons a hu]
      simp [cfK]
  | case3 a b l ih1 ih2 =>
      intro _
      by_cases hl : l = []
      · subst hl
        have hbu : (b :: u) ≠ [] := by simp
        simp only [List.cons_append, List.nil_append]
        rw [show a :: b :: u = a :: (b :: u) from rfl, cfK_cons a hbu,
          cfK_cons b hu]
        simp [cfK]
        ring
      · have h1 := ih1 (by simp)
        have h2 := ih2 hl
        have hbl : (b :: l) ≠ [] := by simp
        have hdl : (b :: l).dropLast ≠ [] := by
          cases l with
          | nil => exact absurd rfl hl
          | cons c m => simp [List.dropLast_cons_cons]
        simp only [List.cons_append] at *
        rw [show cfK (a :: b :: (l ++ u)) =
              a * cfK (b :: (l ++ u)) + cfK (l ++ u) from rfl,
          h1, h2,
          show (a :: b :: l).dropLast = a :: (b :: l).dropLast from
            List.dropLast_cons_cons .., cfK_cons a hdl,
          show cfK (a :: b :: l) = a * cfK (b :: l) + cfK l from rfl]
        have hdrop : (b :: l).dropLast.drop 1 = l.dropLast := by
          cases l with
          | nil => exact absurd rfl hl
          | cons c m => simp [List.dropLast_cons_cons]
        rw [hdrop]
        ring

/-- Dropping the first digit does not increase the continuant (digits ≥ 1). -/
theorem cfK_drop_one_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfK (w.drop 1) ≤ cfK w := by
  cases w with
  | nil => simp
  | cons a m =>
      have ha : 1 ≤ a := hpos a (by simp)
      cases m with
      | nil => simpa [cfK] using ha
      | cons b l =>
          have h1 : 1 ≤ cfK (b :: l) :=
            one_le_cfK _ fun x hx => hpos x (List.mem_cons_of_mem _ hx)
          have := Nat.mul_le_mul ha (le_refl (cfK (b :: l)))
          simp only [List.drop_one, List.tail_cons, cfK]
          omega

/-- Dropping the last digit does not increase the continuant (digits ≥ 1). -/
theorem cfK_dropLast_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfK w.dropLast ≤ cfK w := by
  revert hpos
  induction w using cfK.induct with
  | case1 => intro _; simp
  | case2 a => intro hpos; simpa [cfK] using hpos a (by simp)
  | case3 a b l ih1 ih2 =>
      intro hpos
      have ha : 1 ≤ a := hpos a (by simp)
      have hbl : ∀ x ∈ b :: l, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      have h1 := ih1 hbl
      by_cases hl : l = []
      · subst hl
        have hb : 1 ≤ b := hpos b (by simp)
        show cfK [a] ≤ cfK [a, b]
        simp only [cfK]
        nlinarith
      · have hdl : (b :: l).dropLast ≠ [] := by
          cases l with
          | nil => exact absurd rfl hl
          | cons c m => simp [List.dropLast_cons_cons]
        have hdrop : (b :: l).dropLast.drop 1 = l.dropLast := by
          cases l with
          | nil => exact absurd rfl hl
          | cons c m => simp [List.dropLast_cons_cons]
        have h2 := ih2 fun x hx => hbl x (List.mem_cons_of_mem _ hx)
        rw [List.dropLast_cons_cons, cfK_cons a hdl, hdrop,
          show cfK (a :: b :: l) = a * cfK (b :: l) + cfK l from rfl]
        exact Nat.add_le_add (Nat.mul_le_mul_left a h1) h2

/-- Quasi-multiplicativity, lower half (B–Y Lemma 3.1):
`q(w)·q(u) ≤ q(wu)`. -/
theorem cfK_mul_le_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    cfK w * cfK u ≤ cfK (w ++ u) := by
  rw [cfK_append w u hw hu]
  exact Nat.le_add_right _ _

/-- Quasi-multiplicativity, upper half (B–Y Lemma 3.1):
`q(wu) ≤ 2·q(w)·q(u)`. -/
theorem cfK_append_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    cfK (w ++ u) ≤ 2 * (cfK w * cfK u) := by
  rw [cfK_append w u hw hu]
  have h1 : cfK w.dropLast ≤ cfK w := cfK_dropLast_le w hwpos
  have h2 : cfK (u.drop 1) ≤ cfK u :=
    cfK_drop_one_le u hupos
  have := Nat.mul_le_mul h1 h2
  omega

/-- Fibonacci lower bound: `qₙ ≥ fib (n+1)` for genuine digit words.  Gives
the deterministic cylinder-length upper bound `|I_w| ≤ φ^{-2(n-1)}` that
replaces the lower half of B–Y Lemma 5 in the efficiency-free construction. -/
theorem fib_le_cfK (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    Nat.fib (w.length + 1) ≤ cfK w := by
  revert hpos
  induction w using cfK.induct with
  | case1 => intro _; simp [cfK]
  | case2 a => intro hpos; simpa [cfK, Nat.fib] using hpos a (by simp)
  | case3 a b l ih1 ih2 =>
      intro hpos
      have ha : 1 ≤ a := hpos a (by simp)
      have h1 := ih1 fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      have h2 := ih2 fun x hx =>
        hpos x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons] at *
      rw [show l.length + 1 + 1 + 1 = (l.length + 1) + 2 from rfl, Nat.fib_add_two]
      have hmul : cfK (b :: l) ≤ a * cfK (b :: l) := Nat.le_mul_of_pos_left _ ha
      simp only [cfK]
      omega

/-! ## Finite CF values and cylinder measure -/

/-- `[0; a₁, …, aₙ] = pₙ/qₙ` in the continuant normal form. -/
theorem cfVal_eq_div (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfVal w = (cfP w : ℚ) / (cfK w : ℚ) := by
  revert hw hpos
  induction w using cfK.induct with
  | case1 => intro hw _; exact absurd rfl hw
  | case2 a => intro _ _; simp [cfVal, cfP, cfK]
  | case3 a b l ih1 _ =>
      intro _ hpos
      have ha : 1 ≤ a := hpos a (by simp)
      have hblpos : ∀ x ∈ b :: l, 1 ≤ x := fun x hx =>
        hpos x (List.mem_cons_of_mem _ hx)
      have ihv := ih1 (by simp) hblpos
      have hKbl : (0 : ℚ) < (cfK (b :: l) : ℚ) := by
        exact_mod_cast one_le_cfK _ hblpos
      have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
      have hD : (0 : ℚ) < (a : ℚ) * (cfK (b :: l) : ℚ) + (cfK l : ℚ) := by
        have : (0 : ℚ) ≤ (cfK l : ℚ) := by positivity
        nlinarith
      rw [show cfVal (a :: b :: l) = 1 / ((a : ℚ) + cfVal (b :: l)) from rfl,
        ihv,
        show cfP (a :: b :: l) = cfK (b :: l) from rfl,
        show cfK (a :: b :: l) = a * cfK (b :: l) + cfK l from rfl,
        show cfP (b :: l) = cfK l from rfl]
      push_cast
      have hsum : (0 : ℚ) < (a : ℚ) + (cfK l : ℚ) / (cfK (b :: l) : ℚ) := by
        have : (0 : ℚ) ≤ (cfK l : ℚ) / (cfK (b :: l) : ℚ) := by positivity
        linarith
      rw [eq_div_iff hD.ne', one_div, inv_mul_eq_div,
        div_eq_iff hsum.ne']
      field_simp

/-- **Cylinder length** (B–Y §1.1): `|I_w| = 1/(qₙ(qₙ + qₙ₋₁))`.
Anchor: `w = [2]` gives `1/6 = |(1/3, 1/2]|`.  The definitional cylinder
differs from the open interval only on a countable (null) junk set. -/
theorem volume_cfCylinder (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    volume (cfCylinder w) =
      ENNReal.ofReal (1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)))) := by
  sorry

/-- **Bounded distortion, upper half** (B–Y Lemma 3.2):
`|I_{wu}| ≤ 2·|I_w|·|I_u|`. -/
theorem volume_cylinder_append_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder (w ++ u)) ≤
      2 * (volume (cfCylinder w) * volume (cfCylinder u)) := by
  sorry

/-- **Bounded distortion, lower half** (B–Y Lemma 3.2):
`|I_w|·|I_u| ≤ 2·|I_{wu}|`. -/
theorem le_volume_cylinder_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder w) * volume (cfCylinder u) ≤
      2 * volume (cfCylinder (w ++ u)) := by
  sorry

/-! ## The density window (gateway to W3) -/

/-- The conditional-density family is trapped in `[1/2, 2]` on the unit
square: `1/(1+t) ≤ h_t(y) ≤ 1+t` for `t, y ∈ [0,1]`. -/
theorem tailDensity_mem_Icc {t y : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    tailDensity t y ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hy0, hy1⟩ := hy
  have hden : (0 : ℝ) < 1 + t * y := by nlinarith
  unfold tailDensity
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have h1 : t * y ≤ t := mul_le_of_le_one_right ht0 hy1
    have h2 : (1 + t * y) ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    have h3 : t * t ≤ 1 := by nlinarith
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg ht0 hy0, sq_nonneg (t * y)]

/-- Branch-derivative ratio bound: the denominators `qₙ + qₙ₋₁·y` of
`cylMap w` at any two points of `[0,1]` differ by a factor at most `2`
(so the derivative ratio is at most `4`) — bounded distortion of a single
inverse branch. -/
theorem cylMap_denom_ratio_le (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a)
    {y y' : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (hy' : y' ∈ Set.Icc (0 : ℝ) 1) :
    (cfK w : ℝ) + (cfK w.dropLast : ℝ) * y ≤
      2 * ((cfK w : ℝ) + (cfK w.dropLast : ℝ) * y') := by
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hy'0, _⟩ := hy'
  have hle : (cfK w.dropLast : ℝ) ≤ (cfK w : ℝ) := by
    exact_mod_cast cfK_dropLast_le w hpos
  have h0 : (0 : ℝ) ≤ (cfK w.dropLast : ℝ) := by positivity
  nlinarith

end NormalNumbers
