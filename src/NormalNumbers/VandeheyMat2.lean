/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDigitLaw
import NormalNumbers.CFCylinder

/-!
# `2 × 2` integer matrices acting on the CF orbit

The bookkeeping layer for Vandehey §2 (Raney normal forms).  Matrices are 4-tuples, not
`Matrix (Fin 2) (Fin 2) ℤ`: the whole use is the Möbius action and the product, and the
`Matrix` API buys nothing here while costing `Fin`-indexed rewriting everywhere.

Conventions match `VandeheyClass.lean`: ingesting a digit `a` multiplies on the **right** by
`B a = [[0,1],[1,a]]`, and the row lattice `ℤ²M` is the class invariant.

The two identities everything downstream rests on:

* `act_mul` — the Möbius action is a left action;
* `act_cfMat` — `x = (B a₁ ⋯ B aₙ) · Tⁿx`, the CF algorithm as a matrix identity.

A transducer state for `x ↦ D·x` is then a matrix `M` of determinant `±D` with `M · Tⁿx`
being the current tail of `D·x`; emitting a digit `d` replaces `M` by `E d · M`, ingesting a
digit `a` replaces `M` by `M · B a`.  Both preserve `|det|`.
-/

namespace NormalNumbers

/-- A `2 × 2` integer matrix `[[a,b],[c,d]]`. -/
structure Mat2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace Mat2

/-- The determinant. -/
def det (M : Mat2) : ℤ := M.a * M.d - M.b * M.c

/-- Matrix product. -/
def mul (M N : Mat2) : Mat2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

instance : Mul Mat2 := ⟨mul⟩
instance : One Mat2 := ⟨⟨1, 0, 0, 1⟩⟩

@[simp] lemma one_a : (1 : Mat2).a = 1 := rfl
@[simp] lemma one_b : (1 : Mat2).b = 0 := rfl
@[simp] lemma one_c : (1 : Mat2).c = 0 := rfl
@[simp] lemma one_d : (1 : Mat2).d = 1 := rfl

lemma mul_def (M N : Mat2) : M * N = mul M N := rfl

@[simp] lemma det_one : (1 : Mat2).det = 1 := by simp [det]

lemma det_mul (M N : Mat2) : (M * N).det = M.det * N.det := by
  simp only [mul_def, mul, det]
  ring

lemma mul_assoc' (M N P : Mat2) : (M * N) * P = M * (N * P) := by
  simp only [mul_def, mul, Mat2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

@[simp] lemma one_mul' (M : Mat2) : (1 : Mat2) * M = M := by
  cases M; simp [mul_def, mul]

@[simp] lemma mul_one' (M : Mat2) : M * (1 : Mat2) = M := by
  cases M; simp [mul_def, mul]

/-- The denominator of the Möbius action. -/
def den (M : Mat2) (u : ℝ) : ℝ := (M.c : ℝ) * u + (M.d : ℝ)

/-- The Möbius action `u ↦ (au+b)/(cu+d)`. -/
noncomputable def act (M : Mat2) (u : ℝ) : ℝ :=
  ((M.a : ℝ) * u + (M.b : ℝ)) / M.den u

@[simp] lemma act_one (u : ℝ) : (1 : Mat2).act u = u := by
  simp [act, den]

/-- Cross-multiplied form of the action. -/
lemma act_eq_iff {M : Mat2} {u v : ℝ} (h : M.den u ≠ 0) :
    M.act u = v ↔ (M.a : ℝ) * u + (M.b : ℝ) = v * M.den u := by
  rw [act, div_eq_iff h]

lemma act_mul_den {M : Mat2} {u : ℝ} (h : M.den u ≠ 0) :
    M.act u * M.den u = (M.a : ℝ) * u + (M.b : ℝ) :=
  ((act_eq_iff h).mp rfl).symm

lemma den_mul (M N : Mat2) (u : ℝ) (hN : N.den u ≠ 0) :
    (M * N).den u = M.den (N.act u) * N.den u := by
  have hact := act_mul_den hN
  simp only [mul_def, mul, den] at hact ⊢
  push_cast
  linear_combination -(M.c : ℝ) * hact

/-- **The Möbius action is a left action.** -/
lemma act_mul (M N : Mat2) (u : ℝ) (hN : N.den u ≠ 0) (hM : M.den (N.act u) ≠ 0) :
    (M * N).act u = M.act (N.act u) := by
  have hactN := act_mul_den hN
  have hactM := act_mul_den hM
  have hden : (M * N).den u ≠ 0 := by
    rw [den_mul M N u hN]
    exact mul_ne_zero hM hN
  rw [act_eq_iff hden, den_mul M N u hN]
  simp only [mul_def, mul, den] at hactN hactM ⊢
  push_cast
  linear_combination -(M.a : ℝ) * hactN - ((N.c : ℝ) * u + (N.d : ℝ)) * hactM

/-! ## The CF generators -/

/-- Ingest: `B a = [[0,1],[1,a]]`, the matrix with `(B a) · u = 1/(a + u)`. -/
def B (a : ℕ) : Mat2 := ⟨0, 1, 1, (a : ℤ)⟩

/-- Emit: `E d = [[−d,1],[1,0]]`, the matrix with `(E d) · z = 1/z − d`. -/
def E (d : ℕ) : Mat2 := ⟨-(d : ℤ), 1, 1, 0⟩

@[simp] lemma det_B (a : ℕ) : (B a).det = -1 := by simp [det, B]

@[simp] lemma det_E (d : ℕ) : (E d).det = -1 := by simp [det, E]

lemma den_B (a : ℕ) (u : ℝ) : (B a).den u = u + (a : ℝ) := by
  simp [den, B]

lemma act_B (a : ℕ) {u : ℝ} (h : u + (a : ℝ) ≠ 0) : (B a).act u = 1 / (u + (a : ℝ)) := by
  rw [act_eq_iff (by rw [den_B]; exact h), den_B, one_div, inv_mul_cancel₀ h]
  simp [B]

lemma act_E (d : ℕ) {z : ℝ} (hz : z ≠ 0) : (E d).act z = 1 / z - (d : ℝ) := by
  have hden : (E d).den z ≠ 0 := by simpa [den, E] using hz
  rw [act_eq_iff hden]
  simp only [den, E]
  push_cast
  field_simp
  ring

/-! ## The CF algorithm as a matrix identity -/

/-- One Gauss step is the action of `E` at the current digit. -/
lemma act_E_cfDigit {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    (E (cfDigit z 0)).act z = gaussMap z := by
  have hz : z ≠ 0 := ne_of_gt hz0
  have hinv : 1 ≤ z⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hz0]
    linarith
  have hfl : ((cfDigit z 0 : ℕ) : ℝ) = (⌊z⁻¹⌋ : ℝ) := by
    rw [cfDigit, Function.iterate_zero_apply, natCast_floor_eq_intCast_floor (by positivity)]
  rw [act_E _ hz, gaussMap, if_neg hz, Int.fract, hfl, one_div]

/-- One CF step undone: `z = (B a) · (T z)` with `a` the current digit. -/
lemma act_B_gaussMap {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    (B (cfDigit z 0)).act (gaussMap z) = z := by
  have hz : z ≠ 0 := ne_of_gt hz0
  have hinv : 1 ≤ z⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hz0]
    linarith
  have hfl : ((cfDigit z 0 : ℕ) : ℝ) = (⌊z⁻¹⌋ : ℝ) := by
    rw [cfDigit, Function.iterate_zero_apply, natCast_floor_eq_intCast_floor (by positivity)]
  have hg : gaussMap z = z⁻¹ - (cfDigit z 0 : ℝ) := by
    rw [gaussMap, if_neg hz, Int.fract, hfl]
  have hsum : gaussMap z + ((cfDigit z 0 : ℕ) : ℝ) = z⁻¹ := by rw [hg]; ring
  rw [act_B _ (by rw [hsum]; positivity), hsum, one_div, inv_inv]

/-- The CF matrix `B a₁ ⋯ B aₙ` of the first `n` digits of `x`. -/
noncomputable def cfMat (x : ℝ) : ℕ → Mat2
  | 0 => 1
  | n + 1 => cfMat x n * B (cfDigit x n)

@[simp] lemma cfMat_zero (x : ℝ) : cfMat x 0 = 1 := rfl

lemma cfMat_succ (x : ℝ) (n : ℕ) : cfMat x (n + 1) = cfMat x n * B (cfDigit x n) := rfl

lemma det_cfMat (x : ℝ) (n : ℕ) : (cfMat x n).det = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [cfMat_succ, det_mul, ih, det_B]; ring

/-- The CF matrix has nonnegative entries in its bottom row, with a positive corner: the
denominators of `cfMat` never vanish on `[0,1]`. -/
lemma cfMat_bottom_nonneg {x : ℝ} (hirr : Irrational x) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    0 ≤ (cfMat x n).c ∧ 0 < (cfMat x n).d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdig : 1 ≤ cfDigit x n := by
      exact one_le_cfDigit x hirr hx n
    have hdig' : (1 : ℤ) ≤ (cfDigit x n : ℤ) := by exact_mod_cast hdig
    obtain ⟨hc, hd⟩ := ih
    rw [cfMat_succ]
    constructor
    · simp only [mul_def, mul, B]
      omega
    · simp only [mul_def, mul, B]
      nlinarith

lemma cfMat_den_pos {x : ℝ} (hirr : Irrational x) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ)
    {u : ℝ} (hu : 0 ≤ u) : 0 < (cfMat x n).den u := by
  obtain ⟨hc, hd⟩ := cfMat_bottom_nonneg hirr hx n
  have hc' : (0 : ℝ) ≤ ((cfMat x n).c : ℝ) := by exact_mod_cast hc
  have hd' : (0 : ℝ) < ((cfMat x n).d : ℝ) := by exact_mod_cast hd
  rw [den]
  positivity

/-- **The CF algorithm as a matrix identity**: `x = (B a₁ ⋯ B aₙ) · Tⁿ x`. -/
theorem act_cfMat {x : ℝ} (hirr : Irrational x) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (cfMat x n).act (gaussMap^[n] x) = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hirr', hmem'⟩ := irrational_orbit x hirr hx n
    obtain ⟨hirr'', hmem''⟩ := irrational_orbit x hirr hx (n + 1)
    have hstep : (B (cfDigit x n)).act (gaussMap^[n + 1] x) = gaussMap^[n] x := by
      rw [Function.iterate_succ_apply']
      have := act_B_gaussMap hmem'.1 hmem'.2
      rwa [cfDigit, Function.iterate_zero_apply] at this
    have hden : (B (cfDigit x n)).den (gaussMap^[n + 1] x) ≠ 0 := by
      rw [den_B]
      exact ne_of_gt (add_pos_of_pos_of_nonneg hmem''.1 (Nat.cast_nonneg _))
    have hdenM : (cfMat x n).den ((B (cfDigit x n)).act (gaussMap^[n + 1] x)) ≠ 0 := by
      rw [hstep]
      exact ne_of_gt (cfMat_den_pos hirr hx n hmem'.1.le)
    rw [cfMat_succ, act_mul _ _ _ hden hdenM, hstep, ih]

end Mat2

end NormalNumbers
