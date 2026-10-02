/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Cocycle

/-!
# The `φ`-machine's states: reading is free, emitting is the whole problem

`VandeheyS7Cocycle` gave the composition calculus.  This file runs it on the actual machine of
Vandehey §7 Problem 1 for `x ↦ φ·x`, and the outcome is sharper than the attack map anticipated.

## Reading an input digit is free

The state after `n` input digits is `M₀ · A_{a₁} ⋯ A_{aₙ}` with `A_a : y ↦ 1/(a + y)` the Gauss
inverse branches and `M₀ = diag(φ, 1)`.  Right-composition by `A_a` sends the lower row
`(c, d)` to `(d, c + a·d)`, so — with `a ≥ 1` and `c ≥ 0` — it **lands in the region `c ≤ d`
whatever it started from** (`lowerLe_comp_gaussBranch`), and stays there.  Since
`distortion = (c + d)/d`, this gives, unconditionally and for every initial state:

    `distortion_runWord_le_two` :  after at least one input digit, `distortion ≤ 2`.

No arithmetic of `ℤ[φ]` is used, and no finiteness.  This is the in-kernel form of the probes'
"real place flat, median distortion 1.04 → 0.98, no drift".  It also explains the classical
side: the same argument over `ℤ` is Rényi's bounded-distortion property of the Gauss map.

## Emitting an output digit is where everything happens

Emission pulls a digit `e` off the image: `z ↦ 1/z − e`, i.e. left-multiplication by
`(−e, 1; 1, 0)`.  On the matrix this sends `(a, b; c, d)` to `(c − e·a, d − e·b; a, b)` — the
**rows swap**.  So (`distortion_emit`)

    distortion (emit e s) = (s.a + s.b) / s.b ,

the *upper* row's ratio, while the invariant maintained for free by reading is about the *lower*
row.  Reading pushes the state into `c ≤ d`; emitting throws it back out.  **That exchange is
the entire content of Route A's window lemma**, and this file reduces the lemma to it:
`EmitRowBound`, the statement that the upper-row ratio `(a + b)/b` stays bounded along the run.

This is a real sharpening of the open obligation.  `BddDistortion` was a statement about a
sequence of abstract states; `EmitRowBound` is a statement about one explicit arithmetic ratio of
two `ℤ[φ]` numbers, at the emission times only.  It is also exactly what the probes measured
saturating at `≈ 2.5`.

## Guard rule

Content locators: `distortion_gaussBranch_le_two` (a single branch, where the bound is visible by
hand) and `lowerLe_phiState` (the `φ` initial state is already in the good region, so the content
is not in the choice of `M₀`).  Degenerate case: `not_bddAbove_distortion` (previous module)
still applies — the bound is bought by the branch structure, not by the ambient setting.
-/

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- The Gauss inverse branch `y ↦ 1/(a + y)`, as a state.  Totalised at `a = 0` by `max 1 a`, so
no side condition is ever carried. -/
noncomputable def gaussBranch (a : ℕ) : MobState where
  a := 0
  b := 1
  c := 1
  d := (max 1 a : ℕ)
  ha := le_refl 0
  hb := zero_le_one
  hc := zero_le_one
  hd := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 a)
  hdet := by norm_num

theorem one_le_gaussBranch_d (a : ℕ) : (1 : ℝ) ≤ (gaussBranch a).d := by
  show (1:ℝ) ≤ ((max 1 a : ℕ) : ℝ)
  exact_mod_cast le_max_left 1 a

theorem gaussBranch_mob (a : ℕ) (x : ℝ) :
    (gaussBranch a).mob x = 1 / (x + (max 1 a : ℕ)) := by
  simp [mob, gaussBranch]

/-- The initial state of the `x ↦ φ·x` machine, `diag(φ, 1)`. -/
noncomputable def phiState : MobState where
  a := Real.goldenRatio
  b := 0
  c := 0
  d := 1
  ha := Real.goldenRatio_pos.le
  hb := le_refl 0
  hc := le_refl 0
  hd := one_pos
  hdet := by simpa using Real.goldenRatio_ne_zero

theorem phiState_mob (x : ℝ) : phiState.mob x = Real.goldenRatio * x := by
  simp [mob, phiState]

/-! ## Reading: the lower-row invariant -/

/-- The good region: the lower row is nondecreasing. -/
def LowerLe (s : MobState) : Prop := s.c ≤ s.d

theorem lowerLe_phiState : LowerLe phiState := by simp [LowerLe, phiState]

/-- **Reading an input digit lands in the good region, from anywhere.**  The lower row
`(c, d)` goes to `(d, c + a·d)`, and `a ≥ 1`, `c ≥ 0` make the second dominate the first. -/
theorem lowerLe_comp_gaussBranch (s : MobState) (a : ℕ) : LowerLe (s.comp (gaussBranch a)) := by
  simp only [LowerLe, comp_c, comp_d, gaussBranch]
  have hc : 0 ≤ s.c := s.hc
  have hd : 0 < s.d := s.hd
  have h1 : (1 : ℝ) ≤ ((max 1 a : ℕ) : ℝ) := one_le_gaussBranch_d a
  nlinarith

/-- In the good region the distortion is at most `2`. -/
theorem distortion_le_two_of_lowerLe {s : MobState} (h : LowerLe s) : s.distortion ≤ 2 := by
  have h' : s.c ≤ s.d := h
  rw [distortion, div_le_iff₀ s.hd]
  linarith [s.hd]

/-- Content locator: a single branch, where the bound is visible by hand. -/
theorem distortion_gaussBranch_le_two (a : ℕ) : (gaussBranch a).distortion ≤ 2 :=
  distortion_le_two_of_lowerLe (by
    simp only [LowerLe, gaussBranch]
    exact one_le_gaussBranch_d a)

/-- Reading a whole input word. -/
noncomputable def runWord (s : MobState) : List ℕ → MobState
  | [] => s
  | a :: w => runWord (s.comp (gaussBranch a)) w

@[simp] theorem runWord_nil (s : MobState) : runWord s [] = s := rfl

@[simp] theorem runWord_cons (s : MobState) (a : ℕ) (w : List ℕ) :
    runWord s (a :: w) = runWord (s.comp (gaussBranch a)) w := rfl

/-- Once in the good region, reading keeps you there. -/
theorem lowerLe_runWord (s : MobState) : ∀ w : List ℕ, w ≠ [] → LowerLe (runWord s w)
  | [], h => absurd rfl h
  | [a], _ => by simpa using lowerLe_comp_gaussBranch s a
  | a :: b :: w, _ => by
      simpa using lowerLe_runWord (s.comp (gaussBranch a)) (b :: w) (by simp)

/-- **Reading is free.**  After at least one input digit, the state's distortion is at most `2`,
from ANY initial state and with no arithmetic hypothesis whatsoever. -/
theorem distortion_runWord_le_two (s : MobState) (w : List ℕ) (hw : w ≠ []) :
    (runWord s w).distortion ≤ 2 :=
  distortion_le_two_of_lowerLe (lowerLe_runWord s w hw)

/-! ## Emitting: the rows swap -/

/-- **Emission**: pull the digit `e` off the image, `z ↦ 1/z − e`.  On the matrix this is
left-multiplication by `(−e, 1; 1, 0)`, i.e. `(a, b; c, d) ↦ (c − e·a, d − e·b; a, b)`. -/
noncomputable def emit (e : ℕ) (s : MobState) (hb : 0 < s.b)
    (h1 : (e : ℝ) * s.a ≤ s.c) (h2 : (e : ℝ) * s.b ≤ s.d) : MobState where
  a := s.c - e * s.a
  b := s.d - e * s.b
  c := s.a
  d := s.b
  ha := by linarith
  hb := by linarith
  hc := s.ha
  hd := hb
  hdet := by
    have h : (s.c - e * s.a) * s.b - (s.d - e * s.b) * s.a = -(s.a * s.d - s.b * s.c) := by ring
    rw [h, neg_ne_zero]
    exact s.hdet

/-- Emission does what it says: it inverts and subtracts the digit. -/
theorem mob_emit (e : ℕ) (s : MobState) (hb : 0 < s.b)
    (h1 : (e : ℝ) * s.a ≤ s.c) (h2 : (e : ℝ) * s.b ≤ s.d) {x : ℝ} (hx : 0 ≤ x)
    (hnum : 0 < s.a * x + s.b) :
    (emit e s hb h1 h2).mob x = 1 / s.mob x - e := by
  have hden : 0 < s.c * x + s.d := s.den_pos hx
  simp only [emit, mob]
  rw [one_div_div]
  field_simp
  ring

/-- **The rows swap, so emission reads the OTHER ratio.**  This is the exchange that Route A's
window lemma has to control. -/
theorem distortion_emit (e : ℕ) (s : MobState) (hb : 0 < s.b)
    (h1 : (e : ℝ) * s.a ≤ s.c) (h2 : (e : ℝ) * s.b ≤ s.d) :
    (emit e s hb h1 h2).distortion = (s.a + s.b) / s.b := rfl

/-! ## The open obligation, sharpened -/

/-- **The window lemma, in its sharpened form.**  Along the run, at the emission times, the
UPPER row's ratio `(a + b)/b` stays bounded.  OPEN.

This is strictly more concrete than `BddDistortion`: reading already gives `distortion ≤ 2` for
free (`distortion_runWord_le_two`), so the only way the distortion can grow is through the row
swap of `distortion_emit`, and this Prop is exactly the statement that it does not.  Measured to
hold, saturating `≈ 2.5`, by both 2026-08 probes. -/
def EmitRowBound (s : ℕ → MobState) : Prop :=
  ∃ K : ℝ, ∀ n, (s n).a + (s n).b ≤ K * (s n).b

/-- `EmitRowBound` is exactly a distortion bound on the emitted states. -/
theorem bddDistortion_of_emitRowBound {s : ℕ → MobState} {e : ℕ → ℕ}
    (hb : ∀ n, 0 < (s n).b) (h1 : ∀ n, ((e n : ℝ)) * (s n).a ≤ (s n).c)
    (h2 : ∀ n, ((e n : ℝ)) * (s n).b ≤ (s n).d) (h : EmitRowBound s) :
    BddDistortion (fun n => emit (e n) (s n) (hb n) (h1 n) (h2 n)) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n => ?_⟩
  rw [distortion_emit, div_le_iff₀ (hb n)]
  simpa [mul_comm] using hK n

end MobState

section Audit

#print axioms MobState.distortion_runWord_le_two
#print axioms MobState.mob_emit
#print axioms MobState.bddDistortion_of_emitRowBound

end Audit

end NormalNumbers.VandeheyS7
