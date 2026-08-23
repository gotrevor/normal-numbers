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
lemma one_le_cfK (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) : 1 ≤ cfK w := by
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

/-! ## Interval characterization of cylinders

The cylinder `I_w` is, up to a countable (null) set of rationals, the
unordered interval between the endpoint values `[0; a₁,…,aₙ]` and
`[0; a₁,…,aₙ₋₁, aₙ+1]`; its length is `1/(qₙ(qₙ+qₙ₋₁))` by the classical
determinant computation.  Everything here is private scaffolding for
`volume_cfCylinder`. -/

/-- Bump the last digit: the second endpoint of `I_w` is
`cfVal (bumpLast w)`. -/
private def bumpLast (w : List ℕ) : List ℕ := w.dropLast ++ [w.getLastD 0 + 1]

private lemma bumpLast_cons {a : ℕ} {m : List ℕ} (hm : m ≠ []) :
    bumpLast (a :: m) = a :: bumpLast m := by
  cases m with
  | nil => exact absurd rfl hm
  | cons b l => simp [bumpLast]

private lemma bumpLast_pos {w : List ℕ} (hpos : ∀ a ∈ w, 1 ≤ a) :
    ∀ a ∈ bumpLast w, 1 ≤ a := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact hpos a (List.mem_of_mem_dropLast h)
  · simp only [List.mem_singleton] at h; omega

private lemma bumpLast_ne_nil (w : List ℕ) : bumpLast w ≠ [] := by
  simp [bumpLast]

lemma cfK_concat (v : List ℕ) (z : ℕ) (hv : v ≠ []) :
    cfK (v ++ [z]) = z * cfK v + cfK v.dropLast := by
  rw [cfK_append v [z] hv (by simp)]
  simp [cfK]
  ring

/-- `K(bump w) = K(w) + K(w⁻)`: continuants are affine in the last digit. -/
private lemma cfK_bumpLast {w : List ℕ} (hw : w ≠ []) :
    cfK (bumpLast w) = cfK w + cfK w.dropLast := by
  obtain ⟨v, z, rfl⟩ : ∃ v z, w = v ++ [z] :=
    ⟨w.dropLast, w.getLast hw, (List.dropLast_append_getLast hw).symm⟩
  have hb : bumpLast (v ++ [z]) = v ++ [z + 1] := by
    simp [bumpLast]
  by_cases hv : v = []
  · subst hv; simp [bumpLast, cfK]
  · rw [hb, cfK_concat v (z + 1) hv, cfK_concat v z hv,
      List.dropLast_concat]
    ring

private lemma cfVal_mem_Icc (w : List ℕ) (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfVal w ∈ Set.Icc (0 : ℚ) 1 := by
  induction w with
  | nil => simp [cfVal]
  | cons a m ih =>
      have ha : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast hpos a (by simp)
      obtain ⟨h0, h1⟩ := ih fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      have hd : (0 : ℚ) < (a : ℚ) + cfVal m := by linarith
      constructor
      · rw [show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl]
        positivity
      · rw [show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl,
          div_le_one hd]
        linarith

private lemma add_cfVal (a : ℕ) (m : List ℕ) (hpos : ∀ x ∈ m, 1 ≤ x) :
    (a : ℚ) + cfVal m = (cfK (a :: m) : ℚ) / (cfK m : ℚ) := by
  cases m with
  | nil => simp [cfVal, cfK]
  | cons b l =>
      have hK : (0 : ℚ) < (cfK (b :: l) : ℚ) := by
        exact_mod_cast one_le_cfK _ hpos
      rw [cfVal_eq_div (b :: l) (by simp) hpos,
        show cfP (b :: l) = cfK l from rfl,
        show cfK (a :: b :: l) = a * cfK (b :: l) + cfK l from rfl]
      push_cast
      field_simp

/-- The determinant computation: `|[0;w] − [0;bump w]| = 1/(K(w)·K(bump w))`. -/
private lemma abs_cfVal_sub_bumpLast (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    |cfVal w - cfVal (bumpLast w)| =
      1 / ((cfK w : ℚ) * (cfK (bumpLast w) : ℚ)) := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a m ih =>
      have haQ : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast hpos a (by simp)
      by_cases hm : m = []
      · subst hm
        have ha0 : (0 : ℚ) < (a : ℚ) := by linarith
        have ha1 : (0 : ℚ) < (a : ℚ) + 1 := by linarith
        rw [show bumpLast [a] = [a + 1] from by simp [bumpLast],
          show cfVal [a] = 1 / ((a : ℚ) + 0) from rfl,
          show cfVal [a + 1] = 1 / (((a + 1 : ℕ) : ℚ) + 0) from rfl,
          show cfK [a] = a from rfl, show cfK [a + 1] = a + 1 from rfl]
        push_cast
        rw [abs_of_nonneg (by rw [sub_nonneg]; gcongr <;> linarith)]
        field_simp
        ring
      · have hmpos : ∀ x ∈ m, 1 ≤ x := fun x hx =>
          hpos x (List.mem_cons_of_mem _ hx)
        have hbpos := bumpLast_pos hmpos
        have ihm := ih hm hmpos
        have hv := cfVal_mem_Icc m hmpos
        have hv' := cfVal_mem_Icc (bumpLast m) hbpos
        have hd : (0 : ℚ) < (a : ℚ) + cfVal m := by
          have := hv.1; linarith
        have hd' : (0 : ℚ) < (a : ℚ) + cfVal (bumpLast m) := by
          have := hv'.1; linarith
        have hQ : (0 : ℚ) < (cfK m : ℚ) := by exact_mod_cast one_le_cfK m hmpos
        have hQ' : (0 : ℚ) < (cfK (bumpLast m) : ℚ) := by
          exact_mod_cast one_le_cfK _ hbpos
        have h1 := add_cfVal a m hmpos
        have h2 := add_cfVal a (bumpLast m) hbpos
        have hK1 : (0 : ℚ) < (cfK (a :: m) : ℚ) := by
          exact_mod_cast one_le_cfK _ hpos
        have hK2 : (0 : ℚ) < (cfK (a :: bumpLast m) : ℚ) := by
          exact_mod_cast one_le_cfK _ fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hpos x (by simp)
            · exact hbpos x hx
        rw [bumpLast_cons hm,
          show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl,
          show cfVal (a :: bumpLast m) = 1 / ((a : ℚ) + cfVal (bumpLast m)) from rfl,
          div_sub_div _ _ hd.ne' hd'.ne', one_mul, mul_one, abs_div,
          abs_of_pos (mul_pos hd hd'),
          show (a : ℚ) + cfVal (bumpLast m) - ((a : ℚ) + cfVal m) =
            -(cfVal m - cfVal (bumpLast m)) from by ring,
          abs_neg, ihm, h1, h2]
        field_simp

/-! ### Digit reading and the cylinder recursion -/

lemma cfDigit_zero (x : ℝ) : cfDigit x 0 = ⌊x⁻¹⌋₊ := by
  simp [cfDigit]

lemma cfDigit_succ (x : ℝ) (n : ℕ) :
    cfDigit x (n + 1) = cfDigit (gaussMap x) n := by
  simp [cfDigit, Function.iterate_succ_apply]

/-- The digit-reading bridge: `cfDigit x 0 = a ⇔ x ∈ (1/(a+1), 1/a]`. -/
lemma cfDigit_zero_eq_iff {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    {a : ℕ} (ha : 1 ≤ a) :
    cfDigit x 0 = a ↔ 1 / ((a : ℝ) + 1) < x ∧ x ≤ 1 / (a : ℝ) := by
  obtain ⟨hx0, _⟩ := hx
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  rw [cfDigit_zero, Nat.floor_eq_iff (by positivity)]
  push_cast
  rw [inv_eq_one_div, le_div_iff₀ hx0, div_lt_iff₀ hx0,
    div_lt_iff₀ (by linarith : (0 : ℝ) < (a : ℝ) + 1),
    le_div_iff₀ (by linarith : (0 : ℝ) < (a : ℝ))]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

lemma gaussMap_eq_inv_sub {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    gaussMap x = x⁻¹ - (cfDigit x 0 : ℝ) := by
  rw [gaussMap, if_neg hx.1.ne', Int.fract, cfDigit_zero]
  congr 1
  exact (natCast_floor_eq_intCast_floor (inv_nonneg.2 hx.1.le)).symm

lemma mem_cfCylinder_cons {a : ℕ} {w : List ℕ} {x : ℝ} :
    x ∈ cfCylinder (a :: w) ↔
      x ∈ Set.Ioo (0 : ℝ) 1 ∧ cfDigit x 0 = a ∧
        (∀ i < w.length, cfDigit (gaussMap x) i = w.getD i 0) := by
  constructor
  · rintro ⟨hx, hd⟩
    refine ⟨hx, by simpa using hd 0 (by simp), fun i hi => ?_⟩
    have := hd (i + 1) (by simpa using Nat.succ_lt_succ hi)
    simpa [cfDigit_succ] using this
  · rintro ⟨hx, h0, hrest⟩
    refine ⟨hx, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h0
    | succ j =>
        have hj : j < w.length := by simpa using hi
        simpa [cfDigit_succ] using hrest j hj

lemma irrational_gaussMap {x : ℝ} (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Irrational (gaussMap x) ∧ gaussMap x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hinv : Irrational x⁻¹ := hirr.inv
  have heq : gaussMap x = Int.fract x⁻¹ := by
    rw [gaussMap, if_neg hx.1.ne']
  have hfrac : Irrational (Int.fract x⁻¹) := by
    rw [Int.fract]
    exact hinv.sub_intCast _
  refine ⟨heq ▸ hfrac, ?_⟩
  rw [heq]
  refine ⟨?_, Int.fract_lt_one _⟩
  rcases lt_or_eq_of_le (Int.fract_nonneg x⁻¹) with h | h
  · exact h
  · exact absurd (h ▸ hfrac) (by simpa using Rat.not_irrational 0)

/-! ### The two inclusions -/

private lemma cfCylinder_subset_uIcc (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    cfCylinder w ⊆
      Set.uIcc ((cfVal w : ℚ) : ℝ) ((cfVal (bumpLast w) : ℚ) : ℝ) := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a m ih =>
      intro x hxmem
      obtain ⟨hx, h0, hrest⟩ := mem_cfCylinder_cons.1 hxmem
      have ha : 1 ≤ a := hpos a (by simp)
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      obtain ⟨hlo, hhi⟩ := (cfDigit_zero_eq_iff hx ha).1 h0
      have hgm := gaussMap_eq_inv_sub hx
      have hxinv : x⁻¹ = (a : ℝ) + gaussMap x := by rw [hgm, h0]; ring
      have hxeq : x = ((a : ℝ) + gaussMap x)⁻¹ := by
        rw [← hxinv, inv_inv]
      by_cases hm : m = []
      · subst hm
        have h1a : ((cfVal [a] : ℚ) : ℝ) = 1 / (a : ℝ) := by
          rw [show cfVal [a] = 1 / ((a : ℚ) + 0) from rfl]; push_cast; ring
        have h1b : ((cfVal (bumpLast [a]) : ℚ) : ℝ) = 1 / ((a : ℝ) + 1) := by
          rw [show bumpLast [a] = [a + 1] from by simp [bumpLast],
            show cfVal [a + 1] = 1 / (((a + 1 : ℕ) : ℚ) + 0) from rfl]
          push_cast; ring
        have hle : 1 / ((a : ℝ) + 1) ≤ 1 / (a : ℝ) := by gcongr <;> linarith
        rw [h1a, h1b, Set.uIcc_of_ge hle]
        exact ⟨hlo.le, hhi⟩
      · have hmpos : ∀ y ∈ m, 1 ≤ y := fun y hy =>
          hpos y (List.mem_cons_of_mem _ hy)
        -- gaussMap x lies in the cylinder of m
        have hy01 : gaussMap x ∈ Set.Ioo (0 : ℝ) 1 := by
          have hynn : 0 ≤ gaussMap x := by
            rw [gaussMap, if_neg hx.1.ne']; exact Int.fract_nonneg _
          have hylt : gaussMap x < 1 := by
            rw [gaussMap, if_neg hx.1.ne']; exact Int.fract_lt_one _
          refine ⟨?_, hylt⟩
          rcases lt_or_eq_of_le hynn with h | h
          · exact h
          · exfalso
            have hd0 : cfDigit (gaussMap x) 0 = m.getD 0 0 := by
              have := hrest 0 (by simp [List.length_pos_iff.2 hm])
              simpa using this
            have hd0pos : 1 ≤ m.getD 0 0 := by
              cases m with
              | nil => exact absurd rfl hm
              | cons b l => simpa using hmpos b (by simp)
            rw [← h, cfDigit_zero] at hd0
            simp only [inv_zero, Nat.floor_zero] at hd0
            omega
        have hycyl : gaussMap x ∈ cfCylinder m := ⟨hy01, fun i hi => hrest i hi⟩
        have hyIcc := ih hm hmpos hycyl
        -- endpoints of the (a::m) interval are h_a of the m endpoints
        have hu := (cfVal_mem_Icc m hmpos).1
        have hv := (cfVal_mem_Icc (bumpLast m) (bumpLast_pos hmpos)).1
        have huR : (0 : ℝ) ≤ ((cfVal m : ℚ) : ℝ) := by exact_mod_cast hu
        have hvR : (0 : ℝ) ≤ ((cfVal (bumpLast m) : ℚ) : ℝ) := by
          exact_mod_cast hv
        have he0 : ((cfVal (a :: m) : ℚ) : ℝ) =
            ((a : ℝ) + ((cfVal m : ℚ) : ℝ))⁻¹ := by
          rw [show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl]
          push_cast
          rw [one_div]
        have he1 : ((cfVal (bumpLast (a :: m)) : ℚ) : ℝ) =
            ((a : ℝ) + ((cfVal (bumpLast m) : ℚ) : ℝ))⁻¹ := by
          rw [bumpLast_cons hm,
            show cfVal (a :: bumpLast m) =
              1 / ((a : ℚ) + cfVal (bumpLast m)) from rfl]
          push_cast
          rw [one_div]
        rw [he0, he1, hxeq]
        -- monotone image of uIcc under y ↦ (a+y)⁻¹
        rcases Set.mem_uIcc.1 hyIcc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Set.mem_uIcc.2 (Or.inr ⟨by gcongr <;> linarith,
            by gcongr <;> linarith⟩)
        · exact Set.mem_uIcc.2 (Or.inl ⟨by gcongr <;> linarith,
            by gcongr <;> linarith⟩)

private lemma uIoo_subset_cfCylinder (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    ∀ x ∈ Set.uIoo ((cfVal w : ℚ) : ℝ) ((cfVal (bumpLast w) : ℚ) : ℝ),
      Irrational x → x ∈ cfCylinder w := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a m ih =>
      intro x hx hirr
      have ha : 1 ≤ a := hpos a (by simp)
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      by_cases hm : m = []
      · subst hm
        have h1a : ((cfVal [a] : ℚ) : ℝ) = 1 / (a : ℝ) := by
          rw [show cfVal [a] = 1 / ((a : ℚ) + 0) from rfl]; push_cast; ring
        have h1b : ((cfVal (bumpLast [a]) : ℚ) : ℝ) = 1 / ((a : ℝ) + 1) := by
          rw [show bumpLast [a] = [a + 1] from by simp [bumpLast],
            show cfVal [a + 1] = 1 / (((a + 1 : ℕ) : ℚ) + 0) from rfl]
          push_cast; ring
        have hle : 1 / ((a : ℝ) + 1) ≤ 1 / (a : ℝ) := by gcongr <;> linarith
        rw [h1a, h1b, Set.uIoo, inf_eq_right.2 hle, sup_eq_left.2 hle,
          Set.mem_Ioo] at hx
        obtain ⟨hlo', hhi'⟩ := hx
        have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor
          · have : (0 : ℝ) < 1 / ((a : ℝ) + 1) := by positivity
            linarith
          · have : 1 / (a : ℝ) ≤ 1 := by
              rw [div_le_one (by linarith)]; linarith
            linarith
        have hd : cfDigit x 0 = a :=
          (cfDigit_zero_eq_iff hx01 ha).2 ⟨hlo', le_of_lt hhi'⟩
        exact mem_cfCylinder_cons.2 ⟨hx01, hd, by simp⟩
      · have hmpos : ∀ y ∈ m, 1 ≤ y := fun y hy =>
          hpos y (List.mem_cons_of_mem _ hy)
        have hbpos := bumpLast_pos hmpos
        have hu := cfVal_mem_Icc m hmpos
        have hv := cfVal_mem_Icc (bumpLast m) hbpos
        have huR : (0 : ℝ) ≤ ((cfVal m : ℚ) : ℝ) := by exact_mod_cast hu.1
        have hvR : (0 : ℝ) ≤ ((cfVal (bumpLast m) : ℚ) : ℝ) := by
          exact_mod_cast hv.1
        have huR1 : ((cfVal m : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hu.2
        have hvR1 : ((cfVal (bumpLast m) : ℚ) : ℝ) ≤ 1 := by
          exact_mod_cast hv.2
        set u := ((cfVal m : ℚ) : ℝ) with hu_def
        set v := ((cfVal (bumpLast m) : ℚ) : ℝ) with hv_def
        have he0 : ((cfVal (a :: m) : ℚ) : ℝ) = ((a : ℝ) + u)⁻¹ := by
          rw [show cfVal (a :: m) = 1 / ((a : ℚ) + cfVal m) from rfl]
          push_cast
          rw [one_div]
        have he1 : ((cfVal (bumpLast (a :: m)) : ℚ) : ℝ) =
            ((a : ℝ) + v)⁻¹ := by
          rw [bumpLast_cons hm,
            show cfVal (a :: bumpLast m) =
              1 / ((a : ℚ) + cfVal (bumpLast m)) from rfl]
          push_cast
          rw [one_div]
        rw [he0, he1] at hx
        have hau : (0 : ℝ) < (a : ℝ) + u := by linarith
        have hav : (0 : ℝ) < (a : ℝ) + v := by linarith
        -- x is strictly between the two branch values, hence in (1/(a+1), 1/a)
        obtain ⟨hxlo, hxhi⟩ := Set.mem_Ioo.1 hx
        have hlow : 1 / ((a : ℝ) + 1) < x := by
          have h1 : 1 / ((a : ℝ) + 1) ≤ ((a : ℝ) + u)⁻¹ := by
            rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
          have h2 : 1 / ((a : ℝ) + 1) ≤ ((a : ℝ) + v)⁻¹ := by
            rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
          calc 1 / ((a : ℝ) + 1) ≤ _ := le_inf h1 h2
            _ < x := hxlo
        have hhigh : x < 1 / (a : ℝ) := by
          have h1 : ((a : ℝ) + u)⁻¹ ≤ 1 / (a : ℝ) := by
            rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
          have h2 : ((a : ℝ) + v)⁻¹ ≤ 1 / (a : ℝ) := by
            rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
          calc x < _ := hxhi
            _ ≤ 1 / (a : ℝ) := sup_le h1 h2
        have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor
          · have : (0 : ℝ) < 1 / ((a : ℝ) + 1) := by positivity
            linarith
          · have : 1 / (a : ℝ) ≤ 1 := by
              rw [div_le_one (by linarith)]; linarith
            linarith
        have hd : cfDigit x 0 = a :=
          (cfDigit_zero_eq_iff hx01 ha).2 ⟨hlow, le_of_lt hhigh⟩
        obtain ⟨hyirr, hy01⟩ := irrational_gaussMap hirr hx01
        have hgm := gaussMap_eq_inv_sub hx01
        have hy_eq : gaussMap x = x⁻¹ - (a : ℝ) := by rw [hgm, hd]
        -- pull x back through the branch: gaussMap x strictly between u and v
        have hymem : gaussMap x ∈ Set.uIoo u v := by
          have hx0 : (0 : ℝ) < x := hx01.1
          have h0inf : (0 : ℝ) ≤ u ⊓ v := le_inf huR hvR
          have hainf : (0 : ℝ) < (a : ℝ) + (u ⊓ v) := by linarith
          have hasup : (0 : ℝ) < (a : ℝ) + (u ⊔ v) := by
            have : u ≤ u ⊔ v := le_sup_left
            linarith
          have hinf_eq : ((a : ℝ) + u)⁻¹ ⊓ ((a : ℝ) + v)⁻¹ =
              ((a : ℝ) + (u ⊔ v))⁻¹ := by
            rcases le_total u v with h | h
            · rw [sup_eq_right.2 h, inf_eq_right.2 (inv_anti₀ hau (by linarith))]
            · rw [sup_eq_left.2 h, inf_eq_left.2 (inv_anti₀ hav (by linarith))]
          have hsup_eq : ((a : ℝ) + u)⁻¹ ⊔ ((a : ℝ) + v)⁻¹ =
              ((a : ℝ) + (u ⊓ v))⁻¹ := by
            rcases le_total u v with h | h
            · rw [inf_eq_left.2 h, sup_eq_left.2 (inv_anti₀ hau (by linarith))]
            · rw [inf_eq_right.2 h, sup_eq_right.2 (inv_anti₀ hav (by linarith))]
          rw [hinf_eq] at hxlo
          rw [hsup_eq] at hxhi
          have hyl : u ⊓ v < gaussMap x := by
            have h := (lt_inv_comm₀ hx0 hainf).1 hxhi
            rw [hy_eq]; linarith
          have hyr : gaussMap x < u ⊔ v := by
            have h := (inv_lt_comm₀ hasup hx0).1 hxlo
            rw [hy_eq]; linarith
          rw [Set.uIoo]
          exact Set.mem_Ioo.2 ⟨hyl, hyr⟩
        have hycyl := ih hm hmpos (gaussMap x) hymem hyirr
        exact mem_cfCylinder_cons.2 ⟨hx01, hd, fun i hi => hycyl.2 i hi⟩

/-- **Cylinder length** (B–Y §1.1): `|I_w| = 1/(qₙ(qₙ + qₙ₋₁))`.
Anchor: `w = [2]` gives `1/6 = |(1/3, 1/2]|`.  The definitional cylinder
differs from the open interval only on a countable (null) junk set. -/
theorem volume_cfCylinder (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) :
    volume (cfCylinder w) =
      ENNReal.ofReal (1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)))) := by
  set E0 : ℝ := ((cfVal w : ℚ) : ℝ) with hE0
  set E1 : ℝ := ((cfVal (bumpLast w) : ℚ) : ℝ) with hE1
  have hlen : |E1 - E0| =
      1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) := by
    have h := abs_cfVal_sub_bumpLast w hw hpos
    have hcast : |E0 - E1| =
        ((|cfVal w - cfVal (bumpLast w)| : ℚ) : ℝ) := by
      rw [hE0, hE1]; push_cast; ring_nf
    rw [abs_sub_comm, hcast, h, cfK_bumpLast hw]
    push_cast
    ring_nf
  have hupper : volume (cfCylinder w) ≤ ENNReal.ofReal |E1 - E0| := by
    calc volume (cfCylinder w) ≤ volume (Set.uIcc E0 E1) :=
          measure_mono (cfCylinder_subset_uIcc w hw hpos)
      _ = ENNReal.ofReal |E1 - E0| := Real.volume_interval
  have hlower : ENNReal.ofReal |E1 - E0| ≤ volume (cfCylinder w) := by
    have hnull : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
      (Set.countable_range _).measure_zero _
    have hsub : Set.uIoo E0 E1 \ Set.range ((↑) : ℚ → ℝ) ⊆ cfCylinder w :=
      fun x hx => uIoo_subset_cfCylinder w hw hpos x hx.1 hx.2
    calc ENNReal.ofReal |E1 - E0| = volume (Set.uIoo E0 E1) :=
          Real.volume_uIoo.symm
      _ = volume (Set.uIoo E0 E1 \ Set.range ((↑) : ℚ → ℝ)) :=
          (measure_sdiff_null hnull).symm
      _ ≤ volume (cfCylinder w) := measure_mono hsub
  rw [← hlen]
  exact le_antisymm hupper hlower

/-- A genuine cylinder sits inside a closed interval whose length is exactly
the cylinder's measure (public packaging of `cfCylinder_subset_uIcc` +
`volume_cfCylinder`, for the Prop-12 step of the t-brick refinement). -/
theorem cfCylinder_subset_Icc_length (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    ∃ a c : ℝ, cfCylinder w ⊆ Set.Icc a c ∧
      c - a = (volume (cfCylinder w)).toReal := by
  set E0 : ℝ := ((cfVal w : ℚ) : ℝ) with hE0
  set E1 : ℝ := ((cfVal (bumpLast w) : ℚ) : ℝ) with hE1
  have hlen : |E1 - E0| =
      1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) := by
    have h := abs_cfVal_sub_bumpLast w hw hpos
    have hcast : |E0 - E1| =
        ((|cfVal w - cfVal (bumpLast w)| : ℚ) : ℝ) := by
      rw [hE0, hE1]; push_cast; ring_nf
    rw [abs_sub_comm, hcast, h, cfK_bumpLast hw]
    push_cast
    ring_nf
  refine ⟨min E0 E1, max E0 E1, ?_, ?_⟩
  · exact cfCylinder_subset_uIcc w hw hpos
  · rw [max_sub_min_eq_abs, volume_cfCylinder w hw hpos,
      ENNReal.toReal_ofReal (by positivity), ← hlen, abs_sub_comm]

/-- **Rational-endpoint packaging** for the limit-point argument: a genuine
cylinder sits between two explicit rationals `P/K` and `P'/(K+K')` (`K = cfK
w`, `K' = cfK w.dropLast`) whose gap is exactly `1/(K(K+K'))`, and every
irrational point strictly between them belongs to the cylinder. -/
theorem cfCylinder_endpoints (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 1 ≤ a) :
    ∃ P P' : ℕ,
      |((P' : ℝ) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ)))
          - ((P : ℝ) / (cfK w : ℝ))|
        = 1 / ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) ∧
      cfCylinder w ⊆ Set.uIcc ((P : ℝ) / (cfK w : ℝ))
        ((P' : ℝ) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ))) ∧
      ∀ x ∈ Set.uIoo ((P : ℝ) / (cfK w : ℝ))
        ((P' : ℝ) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ))),
        Irrational x → x ∈ cfCylinder w := by
  have hE0 : (((cfVal w : ℚ)) : ℝ) = (cfP w : ℝ) / (cfK w : ℝ) := by
    rw [cfVal_eq_div w hw hpos]
    push_cast
    ring
  have hE1 : (((cfVal (bumpLast w) : ℚ)) : ℝ)
      = (cfP (bumpLast w) : ℝ) / ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by
    rw [cfVal_eq_div (bumpLast w) (bumpLast_ne_nil w) (bumpLast_pos hpos),
      cfK_bumpLast hw]
    push_cast
    ring
  refine ⟨cfP w, cfP (bumpLast w), ?_, ?_, ?_⟩
  · have h := abs_cfVal_sub_bumpLast w hw hpos
    have hcast : |(((cfVal w : ℚ)) : ℝ) - (((cfVal (bumpLast w) : ℚ)) : ℝ)|
        = ((|cfVal w - cfVal (bumpLast w)| : ℚ) : ℝ) := by
      push_cast
      ring_nf
    rw [← hE0, ← hE1, abs_sub_comm, hcast, h, cfK_bumpLast hw]
    push_cast
    ring_nf
  · rw [← hE0, ← hE1]
    exact cfCylinder_subset_uIcc w hw hpos
  · intro x hx hirr
    rw [← hE0, ← hE1] at hx
    exact uIoo_subset_cfCylinder w hw hpos x hx hirr

/-- **Bounded distortion, upper half** (B–Y Lemma 3.2):
`|I_{wu}| ≤ 2·|I_w|·|I_u|`. -/
theorem volume_cylinder_append_le (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder (w ++ u)) ≤
      2 * (volume (cfCylinder w) * volume (cfCylinder u)) := by
  have hapos : ∀ a ∈ w ++ u, 1 ≤ a := fun a ha =>
    (List.mem_append.1 ha).elim (hwpos a) (hupos a)
  have hwu : w ++ u ≠ [] := by simp [hw]
  have hdpos : ∀ a ∈ u.dropLast, 1 ≤ a := fun a ha =>
    hupos a (List.mem_of_mem_dropLast ha)
  have hdl : (w ++ u).dropLast = w ++ u.dropLast := by
    rw [List.dropLast_append_of_ne_nil hu]
  -- sharper-than-quasi bounds from exact gluing
  have h1 : cfK (w ++ u) ≤ (cfK w + cfK w.dropLast) * cfK u := by
    rw [cfK_append w u hw hu, add_mul]
    exact Nat.add_le_add le_rfl
      (Nat.mul_le_mul le_rfl (cfK_drop_one_le u hupos))
  have h2 : cfK (w ++ u.dropLast) ≤ (cfK w + cfK w.dropLast) * cfK u.dropLast := by
    by_cases hud : u.dropLast = []
    · rw [hud]
      simp only [List.append_nil, show cfK ([] : List ℕ) = 1 from rfl, mul_one]
      omega
    · rw [cfK_append w _ hw hud, add_mul]
      exact Nat.add_le_add le_rfl
        (Nat.mul_le_mul le_rfl (cfK_drop_one_le _ hdpos))
  have h3 : cfK w.dropLast ≤ cfK w := cfK_dropLast_le w hwpos
  -- the Nat inequality A ≤ 2·B·C
  have hN : cfK (w ++ u) * (cfK (w ++ u) + cfK (w ++ u.dropLast)) ≤
      2 * ((cfK w * (cfK w + cfK w.dropLast)) *
        (cfK u * (cfK u + cfK u.dropLast))) := by
    calc cfK (w ++ u) * (cfK (w ++ u) + cfK (w ++ u.dropLast))
        ≤ ((cfK w + cfK w.dropLast) * cfK u) *
            ((cfK w + cfK w.dropLast) * cfK u +
              (cfK w + cfK w.dropLast) * cfK u.dropLast) :=
          Nat.mul_le_mul h1 (Nat.add_le_add h1 h2)
      _ = ((cfK w + cfK w.dropLast) * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast)) := by ring
      _ ≤ ((2 * cfK w) * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl
      _ = 2 * ((cfK w * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast))) := by ring
  -- pass to real volumes
  rw [volume_cfCylinder _ hwu hapos, volume_cfCylinder w hw hwpos,
    volume_cfCylinder u hu hupos, hdl,
    ← ENNReal.ofReal_mul (by positivity),
    show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hA : (0 : ℝ) < (cfK (w ++ u) : ℝ) *
      ((cfK (w ++ u) : ℝ) + (cfK (w ++ u.dropLast) : ℝ)) := by
    have := one_le_cfK (w ++ u) hapos
    have h0 : (1 : ℝ) ≤ (cfK (w ++ u) : ℝ) := by exact_mod_cast this
    positivity
  have hB : (0 : ℝ) < (cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by
    have h0 : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hwpos
    positivity
  have hC : (0 : ℝ) < (cfK u : ℝ) * ((cfK u : ℝ) + (cfK u.dropLast : ℝ)) := by
    have h0 : (1 : ℝ) ≤ (cfK u : ℝ) := by exact_mod_cast one_le_cfK u hupos
    positivity
  have key : (cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) *
      ((cfK u : ℝ) * ((cfK u : ℝ) + (cfK u.dropLast : ℝ))) ≤
      2 * ((cfK (w ++ u) : ℝ) *
        ((cfK (w ++ u) : ℝ) + (cfK (w ++ u.dropLast) : ℝ))) := by
    have h2N : (cfK w * (cfK w + cfK w.dropLast)) *
        (cfK u * (cfK u + cfK u.dropLast)) ≤
        2 * (cfK (w ++ u) * (cfK (w ++ u) + cfK (w ++ u.dropLast))) := by
      -- BC ≤ 2A : the lower-distortion Nat inequality
      have g1 : cfK w * cfK u ≤ cfK (w ++ u) :=
        cfK_mul_le_append w u hw hu hwpos hupos
      have g2 : cfK w * cfK u.dropLast ≤ cfK (w ++ u.dropLast) := by
        by_cases hud : u.dropLast = []
        · rw [hud]
          simp only [List.append_nil, show cfK ([] : List ℕ) = 1 from rfl,
            mul_one]
          exact le_rfl
        · exact cfK_mul_le_append w _ hw hud hwpos hdpos
      calc (cfK w * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast))
          ≤ (cfK w * (2 * cfK w)) * (cfK u * (cfK u + cfK u.dropLast)) :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) le_rfl
        _ = 2 * ((cfK w * cfK u) * (cfK w * cfK u + cfK w * cfK u.dropLast)) := by
            ring
        _ ≤ 2 * (cfK (w ++ u) * (cfK (w ++ u) + cfK (w ++ u.dropLast))) := by
            exact Nat.mul_le_mul le_rfl
              (Nat.mul_le_mul g1 (Nat.add_le_add g1 g2))
      -- (kept for symmetry; not needed here)
    exact_mod_cast h2N
  rw [div_mul_div_comm, one_mul, mul_one_div,
    div_le_div_iff₀ hA (mul_pos hB hC)]
  nlinarith [key]

/-- **Bounded distortion, lower half** (B–Y Lemma 3.2):
`|I_w|·|I_u| ≤ 2·|I_{wu}|`. -/
theorem le_volume_cylinder_append (w u : List ℕ) (hw : w ≠ []) (hu : u ≠ [])
    (hwpos : ∀ a ∈ w, 1 ≤ a) (hupos : ∀ a ∈ u, 1 ≤ a) :
    volume (cfCylinder w) * volume (cfCylinder u) ≤
      2 * volume (cfCylinder (w ++ u)) := by
  have hapos : ∀ a ∈ w ++ u, 1 ≤ a := fun a ha =>
    (List.mem_append.1 ha).elim (hwpos a) (hupos a)
  have hwu : w ++ u ≠ [] := by simp [hw]
  have hdpos : ∀ a ∈ u.dropLast, 1 ≤ a := fun a ha =>
    hupos a (List.mem_of_mem_dropLast ha)
  have hdl : (w ++ u).dropLast = w ++ u.dropLast := by
    rw [List.dropLast_append_of_ne_nil hu]
  have h1 : cfK (w ++ u) ≤ (cfK w + cfK w.dropLast) * cfK u := by
    rw [cfK_append w u hw hu, add_mul]
    exact Nat.add_le_add le_rfl
      (Nat.mul_le_mul le_rfl (cfK_drop_one_le u hupos))
  have h2 : cfK (w ++ u.dropLast) ≤ (cfK w + cfK w.dropLast) * cfK u.dropLast := by
    by_cases hud : u.dropLast = []
    · rw [hud]
      simp only [List.append_nil, show cfK ([] : List ℕ) = 1 from rfl, mul_one]
      omega
    · rw [cfK_append w _ hw hud, add_mul]
      exact Nat.add_le_add le_rfl
        (Nat.mul_le_mul le_rfl (cfK_drop_one_le _ hdpos))
  have h3 : cfK w.dropLast ≤ cfK w := cfK_dropLast_le w hwpos
  -- the Nat inequality A ≤ 2·B·C
  have hN : cfK (w ++ u) * (cfK (w ++ u) + cfK (w ++ u.dropLast)) ≤
      2 * ((cfK w * (cfK w + cfK w.dropLast)) *
        (cfK u * (cfK u + cfK u.dropLast))) := by
    calc cfK (w ++ u) * (cfK (w ++ u) + cfK (w ++ u.dropLast))
        ≤ ((cfK w + cfK w.dropLast) * cfK u) *
            ((cfK w + cfK w.dropLast) * cfK u +
              (cfK w + cfK w.dropLast) * cfK u.dropLast) :=
          Nat.mul_le_mul h1 (Nat.add_le_add h1 h2)
      _ = ((cfK w + cfK w.dropLast) * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast)) := by ring
      _ ≤ ((2 * cfK w) * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl
      _ = 2 * ((cfK w * (cfK w + cfK w.dropLast)) *
            (cfK u * (cfK u + cfK u.dropLast))) := by ring
  rw [volume_cfCylinder _ hwu hapos, volume_cfCylinder w hw hwpos,
    volume_cfCylinder u hu hupos, hdl,
    ← ENNReal.ofReal_mul (by positivity),
    show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hA : (0 : ℝ) < (cfK (w ++ u) : ℝ) *
      ((cfK (w ++ u) : ℝ) + (cfK (w ++ u.dropLast) : ℝ)) := by
    have h0 : (1 : ℝ) ≤ (cfK (w ++ u) : ℝ) := by
      exact_mod_cast one_le_cfK (w ++ u) hapos
    positivity
  have hB : (0 : ℝ) < (cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) := by
    have h0 : (1 : ℝ) ≤ (cfK w : ℝ) := by exact_mod_cast one_le_cfK w hwpos
    positivity
  have hC : (0 : ℝ) < (cfK u : ℝ) * ((cfK u : ℝ) + (cfK u.dropLast : ℝ)) := by
    have h0 : (1 : ℝ) ≤ (cfK u : ℝ) := by exact_mod_cast one_le_cfK u hupos
    positivity
  have keyR : (cfK (w ++ u) : ℝ) *
      ((cfK (w ++ u) : ℝ) + (cfK (w ++ u.dropLast) : ℝ)) ≤
      2 * ((cfK w : ℝ) * ((cfK w : ℝ) + (cfK w.dropLast : ℝ)) *
        ((cfK u : ℝ) * ((cfK u : ℝ) + (cfK u.dropLast : ℝ)))) := by
    exact_mod_cast hN
  rw [div_mul_div_comm, one_mul, mul_one_div,
    div_le_div_iff₀ (mul_pos hB hC) hA]
  nlinarith [keyR]

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
