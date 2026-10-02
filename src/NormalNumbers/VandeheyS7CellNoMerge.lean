/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CN: reading never forgets — the operator check on `CellMemory`

The 2026-09-29 12:15 operator check asks whether `CellMemory` (S7-CM) is refuted by the
`no_window_function` witnesses.  This module answers it, in the kernel, by isolating the exact
invariant that the witnesses exploit and showing it is preserved by **every** run step.

## The invariant

Two states `s`, `t` (as raw `2×2` matrices `S`, `T`) are compared by their **discrepancy**

    disc s t := T · adj S ,

the matrix of the Möbius map carrying `s`'s picture to `t`'s picture.  `disc` is a complete
invariant of "same Möbius map": `s` and `t` induce the same map on `[0,1]` exactly when
`disc s t` is a nonzero multiple of the identity (`mob_eq_of_disc_smul_one`).  Two facts:

* **`disc_comp_right`** — reading is a RIGHT action, and
  `disc (s·r) (t·r) = (det r) • disc s t`.  Reading the same digits from two different states
  changes the discrepancy by a *scalar*, i.e. not at all as a Möbius map.  **Memory is never
  lost by reading, for any word, of any length.**
* **`disc_emitStep`** — an emission is a LEFT action by the inverse of a read matrix, and
  `disc u₁ u₂ = adj E₂ · (disc t₁ t₂) · E₁` with `E_i` invertible.  So an emission *transports*
  the discrepancy by invertible matrices on both sides; it cannot degenerate it either.

Hence along a run the relation between two histories is carried, never contracted.  This is
directive fact (γ) in entrywise form, and it is the precise sense in which the
`no_window_function` witnesses are not a fluke of their shape: `canEmit_runWord_of_const` is the
`disc_comp_right` phenomenon specialised to two states whose images already sit in fixed
cylinders.

## The verdict on `CellMemory`

`CellMemory` is **not** refuted by those witnesses, and the reason is sharp: `no_window_function`
quantifies over two *unrelated initial states*, while `CellMemory` is a statement about a single
run `runState Φ x ·`, whose states all share one `Φ` and one input.  The refutation does not
transfer — it says nothing about which pairs of states one run actually visits.

What this module *does* settle is where any proof of `CellMemory` must live.
`cellMemory_selIndic_congr` shows `CellMemory` forces the selection to agree at any two times
carrying the same `L`-digit window.  By `disc_comp_right` the reading part of the window
contributes **nothing** to that agreement: the discrepancy of the two histories is carried through
the whole window unchanged as a Möbius map, however long the window is.  So the ONLY mechanism
available is the emission mismatch, `disc_comp_left`: when the two histories emit different
digits the discrepancy is replaced by `E₂ · disc · adj E₁`, and only a contraction of *that*
two-sided action can merge the cells.

**Route verdict**: the memory route is alive but its content is entirely in the left action.  The
next attack is a Birkhoff–Hopf contraction statement for `M ↦ E₂ · M · adj E₁` over the read
matrices actually produced by the run — not for the read action, which is now proved inert.

## Guard rule

Content locator: `disc_comp_right` at `r = idMap` is the definition, so all of its content is in
`adj (S R) = adj R · adj S`, i.e. in reading acting on the right.  Degenerate cases: `disc s s =
(det s) • 1` (`disc_self`) — a state has no discrepancy with itself; and
`mob_eq_of_disc_smul_one` at `lam = det s` recovers that.
-/
import NormalNumbers.VandeheyS7CellMem
import NormalNumbers.VandeheyS7Box

namespace NormalNumbers.VandeheyS7

namespace MapState

/-! ## Raw `2×2` matrices -/

/-- A raw real `2×2` matrix: the entries of a state with the `MapState` inequalities dropped.
The discrepancy of two states is not itself a state (it need not map `[0,1]` into `[0,1]`). -/
@[ext] structure Mat2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

namespace Mat2

/-- Matrix product. -/
def mul (M N : Mat2) : Mat2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

/-- The adjugate: `adj M · M = M · adj M = (det M) • 1`. -/
def adj (M : Mat2) : Mat2 := ⟨M.d, -M.b, -M.c, M.a⟩

/-- Determinant. -/
def det (M : Mat2) : ℝ := M.a * M.d - M.b * M.c

/-- Scalar multiple. -/
def smul (r : ℝ) (M : Mat2) : Mat2 := ⟨r * M.a, r * M.b, r * M.c, r * M.d⟩

/-- The identity matrix. -/
def one : Mat2 := ⟨1, 0, 0, 1⟩

@[simp] lemma mul_a (M N : Mat2) : (M.mul N).a = M.a * N.a + M.b * N.c := rfl
@[simp] lemma mul_b (M N : Mat2) : (M.mul N).b = M.a * N.b + M.b * N.d := rfl
@[simp] lemma mul_c (M N : Mat2) : (M.mul N).c = M.c * N.a + M.d * N.c := rfl
@[simp] lemma mul_d (M N : Mat2) : (M.mul N).d = M.c * N.b + M.d * N.d := rfl
@[simp] lemma adj_a (M : Mat2) : M.adj.a = M.d := rfl
@[simp] lemma adj_b (M : Mat2) : M.adj.b = -M.b := rfl
@[simp] lemma adj_c (M : Mat2) : M.adj.c = -M.c := rfl
@[simp] lemma adj_d (M : Mat2) : M.adj.d = M.a := rfl
@[simp] lemma smul_a (r : ℝ) (M : Mat2) : (smul r M).a = r * M.a := rfl
@[simp] lemma smul_b (r : ℝ) (M : Mat2) : (smul r M).b = r * M.b := rfl
@[simp] lemma smul_c (r : ℝ) (M : Mat2) : (smul r M).c = r * M.c := rfl
@[simp] lemma smul_d (r : ℝ) (M : Mat2) : (smul r M).d = r * M.d := rfl

theorem mul_assoc (M N P : Mat2) : (M.mul N).mul P = M.mul (N.mul P) := by
  ext <;> simp <;> ring

/-- The adjugate is an anti-homomorphism: `adj (M · N) = adj N · adj M`. -/
theorem adj_mul (M N : Mat2) : (M.mul N).adj = N.adj.mul M.adj := by
  ext <;> simp <;> ring

/-- The adjugate is an involution on `2×2` matrices. -/
theorem adj_adj (M : Mat2) : M.adj.adj = M := by ext <;> simp

theorem mul_adj (M : Mat2) : M.mul M.adj = smul M.det one := by
  ext <;> simp [det, one] <;> ring

theorem det_mul (M N : Mat2) : (M.mul N).det = M.det * N.det := by
  simp only [det, mul_a, mul_b, mul_c, mul_d]; ring

end Mat2

/-! ## The state's matrix, and the discrepancy -/

/-- The raw matrix of a state. -/
def mat (s : MapState) : Mat2 := ⟨s.a, s.b, s.c, s.d⟩

@[simp] lemma mat_a (s : MapState) : s.mat.a = s.a := rfl
@[simp] lemma mat_b (s : MapState) : s.mat.b = s.b := rfl
@[simp] lemma mat_c (s : MapState) : s.mat.c = s.c := rfl
@[simp] lemma mat_d (s : MapState) : s.mat.d = s.d := rfl

lemma mat_comp (s t : MapState) : (s.comp t).mat = s.mat.mul t.mat := by
  ext <;> simp [mat]

lemma mat_det (s : MapState) : s.mat.det = s.det := rfl

/-- **The discrepancy** of two states: the matrix of the Möbius map taking `s`'s picture to
`t`'s.  It is the complete record of what one state knows that the other does not. -/
def disc (s t : MapState) : Mat2 := t.mat.mul s.mat.adj

@[simp] lemma disc_a (s t : MapState) : (disc s t).a = t.a * s.d - t.b * s.c := by
  simp [disc, mat]; ring
@[simp] lemma disc_b (s t : MapState) : (disc s t).b = t.b * s.a - t.a * s.b := by
  simp [disc, mat]; ring
@[simp] lemma disc_c (s t : MapState) : (disc s t).c = t.c * s.d - t.d * s.c := by
  simp [disc, mat]; ring
@[simp] lemma disc_d (s t : MapState) : (disc s t).d = t.d * s.a - t.c * s.b := by
  simp [disc, mat]; ring

/-- A state has no discrepancy with itself. -/
theorem disc_self (s : MapState) : disc s s = Mat2.smul s.det Mat2.one := by
  ext <;> simp [Mat2.one, MapState.det] <;> ring

theorem disc_det (s t : MapState) : (disc s t).det = t.det * s.det := by
  simp only [Mat2.det, disc_a, disc_b, disc_c, disc_d, MapState.det]; ring

theorem disc_det_ne_zero (s t : MapState) : (disc s t).det ≠ 0 := by
  rw [disc_det]
  exact mul_ne_zero t.hdet s.hdet

/-! ## Reading does not forget -/

/-- **Reading is a right action, and it moves the discrepancy by a scalar only.**  Two states
that read the same word keep exactly the same discrepancy as Möbius maps — for every word, of
every length.  This is the entrywise form of directive fact (γ). -/
theorem disc_comp_right (s t r : MapState) :
    disc (s.comp r) (t.comp r) = Mat2.smul r.det (disc s t) := by
  ext <;> simp [MapState.det] <;> ring

/-- **Emission is a left action, and it transports the discrepancy by invertible matrices.**
Composing on the LEFT — which is what an emission does, by the inverse of a read matrix — moves
the discrepancy to `E₂ · disc · adj E₁`.  No contraction, for any `E₁`, `E₂`. -/
theorem disc_comp_left (s t e₁ e₂ : MapState) :
    disc (e₁.comp s) (e₂.comp t) = (e₂.mat.mul (disc s t)).mul e₁.mat.adj := by
  ext <;> simp [Mat2.mul, Mat2.adj, mat, disc] <;> ring

/-- The emission step, in discrepancy form: two states of the run that emit (possibly different)
digits `b₁`, `b₂` pass their discrepancy to the reduced states, transported by the two read
matrices.  Both are invertible, so an emission cannot degenerate the discrepancy either. -/
theorem disc_emitStep {t₁ t₂ u₁ u₂ : MapState} {b₁ b₂ : ℕ}
    (h₁ : EmitStep t₁ b₁ u₁) (h₂ : EmitStep t₂ b₂ u₂) :
    ∃ e₁ e₂ : MapState,
      disc t₁ t₂ = (e₂.mat.mul (disc u₁ u₂)).mul e₁.mat.adj := by
  have hb₁ : (1:ℝ) ≤ (b₁ : ℝ) := by exact_mod_cast h₁.1
  have hb₂ : (1:ℝ) ≤ (b₂ : ℝ) := by exact_mod_cast h₂.1
  refine ⟨readMap (b₁ : ℝ) hb₁, readMap (b₂ : ℝ) hb₂, ?_⟩
  have e₁ := (emitStep_iff h₁.1).1 h₁
  have e₂ := (emitStep_iff h₂.1).1 h₂
  have key : disc t₁ t₂
      = disc ((readMap (b₁ : ℝ) hb₁).comp u₁) ((readMap (b₂ : ℝ) hb₂).comp u₂) := by
    rw [e₁, e₂]
  rw [key, disc_comp_left]

/-- The discrepancy is a complete invariant: if it is a nonzero scalar matrix then the two states
induce the same Möbius map on `[0,1]`. -/
theorem mob_eq_of_disc_smul_one {s t : MapState} {lam : ℝ} (hlam : lam ≠ 0)
    (h : disc s t = Mat2.smul lam Mat2.one) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    t.mob z = s.mob z := by
  have ha : t.a * s.d - t.b * s.c = lam := by
    have := congrArg Mat2.a h; simpa [Mat2.one] using this
  have hb : t.b * s.a - t.a * s.b = 0 := by
    have := congrArg Mat2.b h; simpa [Mat2.one] using this
  have hc : t.c * s.d - t.d * s.c = 0 := by
    have := congrArg Mat2.c h; simpa [Mat2.one] using this
  have hd : t.d * s.a - t.c * s.b = lam := by
    have := congrArg Mat2.d h; simpa [Mat2.one] using this
  set D : ℝ := s.a * s.d - s.b * s.c with hD
  have hDne : D ≠ 0 := s.hdet
  have k1 : D * t.a = lam * s.a := by rw [hD]; linear_combination s.a * ha + s.c * hb
  have k2 : D * t.b = lam * s.b := by rw [hD]; linear_combination s.b * ha + s.d * hb
  have k3 : D * t.c = lam * s.c := by rw [hD]; linear_combination s.a * hc + s.c * hd
  have k4 : D * t.d = lam * s.d := by rw [hD]; linear_combination s.b * hc + s.d * hd
  have hsden : 0 < s.c * z + s.d := s.den_pos hz
  have htden : 0 < t.c * z + t.d := t.den_pos hz
  have hnum : D * (t.a * z + t.b) = lam * (s.a * z + s.b) := by
    linear_combination z * k1 + k2
  have hden : D * (t.c * z + t.d) = lam * (s.c * z + s.d) := by
    linear_combination z * k3 + k4
  rw [mob, mob, div_eq_div_iff htden.ne' hsden.ne']
  have hD2 : D * lam ≠ 0 := mul_ne_zero hDne hlam
  apply mul_left_cancel₀ hD2
  calc D * lam * ((t.a * z + t.b) * (s.c * z + s.d))
      = (D * (t.a * z + t.b)) * (lam * (s.c * z + s.d)) := by ring
    _ = (lam * (s.a * z + s.b)) * (D * (t.c * z + t.d)) := by rw [hnum, hden]
    _ = D * lam * ((s.a * z + s.b) * (t.c * z + t.d)) := by ring

/-! ## The instrument that would refute `CellMemory` -/

open Classical in
/-- **`CellMemory` forces window-congruence of the selection.**  So to refute `CellMemory` one
must exhibit two times of the run whose `L`-digit windows start in the same cylinder but whose
selections differ.  Nothing weaker suffices, and — by `disc_comp_right` and `disc_emitStep` —
nothing about memory loss along the window can supply it. -/
theorem cellMemory_selIndic_congr {Φ : MapState} {x : ℝ} {η ρ : ℝ} {M : ℕ}
    {net : StateNet Φ x η ρ M} {L : ℕ} (h : CellMemory net L)
    (i : Fin M) {m m' : ℕ} (hm : L ≤ m + 2) (hm' : L ≤ m' + 2)
    (hwin : ∀ u : List ℕ, u.length = L →
      (gaussMap^[m + 2 - L] x ∈ cfCylinder u ↔ gaussMap^[m' + 2 - L] x ∈ cfCylinder u)) :
    selIndic net i m = selIndic net i m' := by
  obtain ⟨-, U, hUlen, hUsel⟩ := h
  rw [hUsel i m hm, hUsel i m' hm']
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, huU, hu⟩
    exact ⟨u, huU, (hwin u (hUlen i u huU).1).1 hu⟩
  · rintro ⟨u, huU, hu⟩
    exact ⟨u, huU, (hwin u (hUlen i u huU).1).2 hu⟩

end MapState

section Audit

#print axioms MapState.disc_comp_right
#print axioms MapState.disc_emitStep
#print axioms MapState.mob_eq_of_disc_smul_one
#print axioms MapState.cellMemory_selIndic_congr

end Audit

end NormalNumbers.VandeheyS7
