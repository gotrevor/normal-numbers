/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFAeNormal
import NormalNumbers.VandeheyLeafReduction
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Vandehey 2017, §7 Problem 1: quadratic-irrational maps and CF-normality

**The open problem** (Vandehey, *Continued fraction normality is not preserved along arithmetic
progressions*'s companion, Compositio Math. **153** (2017) 274–293, §7 Problem 1): if `x` is
CF-normal and `q, r` are quadratic irrationals with `q ≠ 0`, is `q·x + r` CF-normal?  The two
simplest instances are `x ↦ φ·x` and `x ↦ x + φ`.  Open since 2017; the forward-citation crawl of
2026-08-24 (`papers/vandehey-2017-open-problem-attack-map.md` §6) found it untouched.

Theorem 1.1 of the same paper — the **integer**-matrix case — is proved in this repo
(`VandeheyCapstone.vandehey_matrix_action_holds`).  Its engine is a transducer whose state set is
finite *because* the states are integer matrices of bounded determinant with bounded entries.
Over `ℤ[φ]` that finiteness is destroyed by Dirichlet's unit theorem: `ℤ[φ]ˣ` is infinite, the
conjugate place drifts (measured at 2.354 nats/step, `experiments/PROBE-ROUTE-A.md`), and a
real-place-bounded subset of `ℤ[φ]` need not be finite.  That is the wall.

## What this file freezes

The frozen targets, never to be weakened:

* `AffineCFN q r` — `∀ x`, `Int.fract x` CF-normal ⇒ `Int.fract (q·x + r)` CF-normal;
* `vandeheyS7_mul_phi : Prop := AffineCFN φ 0` and `vandeheyS7_add_phi : Prop := AffineCFN 1 φ`;
* `VandeheyS7Problem1 : Prop` — the general quadratic-irrational form.

## What this file proves (the endgame, ported off ℤ)

The attack map's §3 claims the endgame of Vandehey's argument — his either-or trick — is *free*
for any map, so that the whole problem reduces to "every CF word has a limiting frequency in the
image, and that limit does not depend on which CF-normal `x` was fed in".  **That claim is now a
theorem** (`affineCFN_of_uniformFreq`), for every real `q > 0` and every real `r` whatsoever:

    AffineUniformFreq q r → AffineCFN q r.

Nothing integral survives in the proof.  The integer version
(`Literature.mobiusCFN_of_uniformFreq`) pins the unknown limit with
`exists_cfNormal_with_cfNormal_image`, itself a `Γ`-orbit argument.  Here the pin is the
*measure-theoretic* witness `exists_feasible_cfNormal_affine`: for `q > 0` and
`-q < r < 1` the CF-normal set and its `ψ`-preimage are both `γ`-conull on the feasible window,
so a single `x₀` with `x₀` and `q·x₀ + r` both CF-normal exists.  That argument never sees the
arithmetic of the coefficients, so it is indifferent to the unit group of `ℤ[φ]`.

Consequence, recorded for the attack map: **the ℤ[φ] wall is entirely on the frequency-existence
side.**  No part of the remaining problem needs a limit *value*.

## Guard rule

Content locators (where the content is *not*): `affineUniformFreq_one` (identity map), and
`affineCFN_int_translate` (integer translations are free — `Int.fract` absorbs them).  Degenerate
case: `not_affineCFN_zero` proves the `q = 0` instance **false**, so the hypothesis `q ≠ 0` in
`VandeheyS7` is not decoration.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-! ## The frozen statements -/

/-- **The frozen target, one affine map at a time.**  `x ↦ q·x + r` preserves CF-normality.
Phrased through `Int.fract` exactly as `Literature.MobiusCFN` is, so that the statement depends
on `r` only modulo `1` and on `x` only modulo `1`. -/
def AffineCFN (q r : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → IsCFNormal (Int.fract (q * x + r))

/-- **The uniform-frequency crux for a real affine map.**  For every genuine CF word `v` the
window frequency of `v` in the CF expansion of `q·x + r` converges to a limit `L` that does not
depend on which CF-normal `x` is fed in.  No value of `L` is asserted — that is the whole point
of the either-or endgame.  This is `Literature.MobiusUniformFreq` with real coefficients and no
denominator. -/
def AffineUniformFreq (q r : ℝ) : Prop :=
  ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) →
    ∃ L : ℝ, ∀ x : ℝ, IsCFNormal (Int.fract x) →
      Tendsto
        (fun p => (countOccurrences v ((List.range p).map
            (cfDigit (Int.fract (q * x + r)))) : ℝ) / p)
        atTop (nhds L)

/-- Algebraic of degree at most `2` over `ℚ`: the coefficient class of Vandehey's §7 Problem 1
(quadratic irrationals, together with the rationals so that the instances `r = 0` and `q = 1`
are covered by the general statement). -/
def IsQuadOverRat (z : ℝ) : Prop :=
  ∃ a b c : ℤ, ¬(a = 0 ∧ b = 0) ∧ (a : ℝ) * z ^ 2 + (b : ℝ) * z + (c : ℝ) = 0

/-- **Vandehey 2017 §7 Problem 1, in full.**  OPEN. -/
def VandeheyS7Problem1 : Prop :=
  ∀ q r : ℝ, q ≠ 0 → IsQuadOverRat q → IsQuadOverRat r → AffineCFN q r

/-- **The simplest instance: `x ↦ φ·x`.**  OPEN. -/
def vandeheyS7_mul_phi : Prop := AffineCFN Real.goldenRatio 0

/-- **The second simplest instance: `x ↦ x + φ`.**  OPEN. -/
def vandeheyS7_add_phi : Prop := AffineCFN 1 Real.goldenRatio

/-! ## Faithfulness: the two instances really are instances -/

theorem isQuadOverRat_goldenRatio : IsQuadOverRat Real.goldenRatio := by
  refine ⟨1, -1, -1, by simp, ?_⟩
  have h := Real.goldenRatio_sq
  push_cast
  linarith [h]

theorem isQuadOverRat_zero : IsQuadOverRat 0 := ⟨0, 1, 0, by simp, by norm_num⟩

theorem isQuadOverRat_one : IsQuadOverRat 1 := ⟨0, 1, -1, by simp, by norm_num⟩

theorem goldenRatio_ne_zero : Real.goldenRatio ≠ 0 :=
  ne_of_gt (lt_trans one_pos Real.one_lt_goldenRatio)

/-- `VandeheyS7Problem1` really does contain `x ↦ φ·x`. -/
theorem vandeheyS7_mul_phi_of (h : VandeheyS7Problem1) : vandeheyS7_mul_phi :=
  h _ _ goldenRatio_ne_zero isQuadOverRat_goldenRatio isQuadOverRat_zero

/-- `VandeheyS7Problem1` really does contain `x ↦ x + φ`. -/
theorem vandeheyS7_add_phi_of (h : VandeheyS7Problem1) : vandeheyS7_add_phi :=
  h _ _ one_ne_zero isQuadOverRat_one isQuadOverRat_goldenRatio

/-! ## `Int.fract` absorbs integer translations

Both statements depend on `r` only modulo `1`.  This is what lets the endgame below, which needs
`r < 1`, cover `r = φ > 1`. -/

theorem affineCFN_add_int (q r : ℝ) (n : ℤ) :
    AffineCFN q (r + n) ↔ AffineCFN q r := by
  have key : ∀ x : ℝ, q * x + (r + (n : ℝ)) = (q * x + r) + (n : ℝ) := by
    intro x; ring
  constructor <;> intro h x hx <;> have := h x hx
  · simpa [key, Int.fract_add_intCast] using this
  · simpa [key, Int.fract_add_intCast] using this

theorem affineUniformFreq_add_int (q r : ℝ) (n : ℤ) :
    AffineUniformFreq q (r + n) ↔ AffineUniformFreq q r := by
  constructor <;> intro h v hne hpos <;> obtain ⟨L, hL⟩ := h v hne hpos <;>
    exact ⟨L, fun x hx => by
      have key : ∀ y : ℝ, q * y + (r + (n : ℝ)) = (q * y + r) + (n : ℝ) := by
        intro y; ring
      have := hL x hx
      simpa [key, Int.fract_add_intCast] using this⟩

/-! ## Content locators (guard rule) -/

/-- The identity map: the limit is read straight off the input's own normality.  This is where
the content is *not*. -/
theorem affineUniformFreq_one : AffineUniformFreq 1 0 := by
  intro v hne hpos
  refine ⟨(gaussMeasure (cfCylinder v)).toReal, fun x hx => ?_⟩
  have h : (1 : ℝ) * x + 0 = x := by ring
  rw [h]
  exact hx v hne hpos

/-- Integer translations preserve CF-normality for free. -/
theorem affineCFN_int_translate (n : ℤ) : AffineCFN 1 n := by
  intro x hx
  simpa [Int.fract_intCast_add] using hx

/-! ## Degenerate case: `q = 0` is genuinely false -/

/-- A constant map destroys CF-normality: the word `[1]` never occurs in the junk expansion of
`0`, while `γ(I_[1]) > 0`.  So the hypothesis `q ≠ 0` of `VandeheyS7Problem1` is load-bearing. -/
theorem not_affineCFN_zero : ¬ AffineCFN 0 0 := by
  intro h
  obtain ⟨x₀, hx₀mem, -, hx₀n, -⟩ :=
    exists_feasible_cfNormal_affine (q := 1) one_pos 0 ⟨by norm_num, by norm_num⟩
  have hfr : Int.fract x₀ = x₀ := Int.fract_eq_self.2 ⟨hx₀mem.1.le, hx₀mem.2⟩
  have hbad : IsCFNormal (Int.fract ((0 : ℝ) * x₀ + 0)) := h x₀ (by rw [hfr]; exact hx₀n)
  rw [show (0 : ℝ) * x₀ + 0 = 0 by ring, Int.fract_zero] at hbad
  have hzero : ∀ p : ℕ, countOccurrences [1] ((List.range p).map (cfDigit (0 : ℝ))) = 0 := by
    intro p
    refine Literature.countOccurrences_eq_zero_of_forall_eq_zero (by simp) (by simp) ?_
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    exact Literature.cfDigit_zero_eq_zero i
  have htend := hbad [1] (by simp) (by simp)
  simp only [hzero] at htend
  have hlim : ((0 : ℕ) : ℝ) = (gaussMeasure (cfCylinder [1])).toReal :=
    tendsto_nhds_unique (by simpa using tendsto_const_nhds) htend
  have hpos : 0 < (gaussMeasure (cfCylinder [1])).toReal :=
    gaussMeasure_cfCylinder_toReal_pos [1] (by simp) (by simp)
  rw [← hlim] at hpos
  norm_num at hpos

/-! ## The endgame, off ℤ

`affineCFN_of_uniformFreq` is the theorem of this file. -/

/-- **The either-or endgame for a real affine map, feasible window.**  For `q > 0` and
`-q < r < 1`, an `x`-independent frequency limit already forces the limit to be `γ(I_v)`, hence
CF-normality of the image.  The pin is the measure-theoretic witness, not a `Γ`-orbit argument,
so nothing about the arithmetic of `q` and `r` enters. -/
theorem affineCFN_of_uniformFreq_feasible {q : ℝ} (hq : 0 < q) {r : ℝ}
    (hrL : -q < r) (hrU : r < 1) (h : AffineUniformFreq q r) : AffineCFN q r := by
  intro x hx v hne hpos
  obtain ⟨L, hL⟩ := h v hne hpos
  obtain ⟨x₀, hx₀mem, hψmem, hx₀n, hψn⟩ :=
    exists_feasible_cfNormal_affine hq r ⟨hrL, hrU⟩
  have hfr : Int.fract x₀ = x₀ := Int.fract_eq_self.2 ⟨hx₀mem.1.le, hx₀mem.2⟩
  have hfrψ : Int.fract (q * x₀ + r) = q * x₀ + r :=
    Int.fract_eq_self.2 ⟨hψmem.1.le, hψmem.2⟩
  have hLγ : L = (gaussMeasure (cfCylinder v)).toReal := by
    refine tendsto_nhds_unique (hL x₀ (by rw [hfr]; exact hx₀n)) ?_
    rw [hfrψ]
    exact hψn v hne hpos
  exact hLγ ▸ hL x hx

/-- **The either-or endgame for a real affine map, in full.**  For every `q > 0` and every real
`r`, the uniform-frequency statement implies the frozen target.  The general `r` is reduced to
the feasible window `[0, 1)` by `Int.fract`, which both statements absorb. -/
theorem affineCFN_of_uniformFreq {q : ℝ} (hq : 0 < q) (r : ℝ)
    (h : AffineUniformFreq q r) : AffineCFN q r := by
  have hsplit : r = Int.fract r + (⌊r⌋ : ℤ) := by
    rw [← Int.self_sub_floor]; ring
  rw [hsplit] at h ⊢
  rw [affineUniformFreq_add_int] at h
  rw [affineCFN_add_int]
  exact affineCFN_of_uniformFreq_feasible hq
    (lt_of_lt_of_le (neg_neg_iff_pos.2 hq) (Int.fract_nonneg r)) (Int.fract_lt_one r) h

/-! ## The two instances, reduced -/

/-- `x ↦ φ·x` is CF-normality-preserving **iff** its output word frequencies have an
`x`-independent limit.  One direction; the problem is now entirely about frequency existence. -/
theorem vandeheyS7_mul_phi_of_uniformFreq (h : AffineUniformFreq Real.goldenRatio 0) :
    vandeheyS7_mul_phi :=
  affineCFN_of_uniformFreq (lt_trans one_pos Real.one_lt_goldenRatio) 0 h

/-- `x ↦ x + φ`, likewise. -/
theorem vandeheyS7_add_phi_of_uniformFreq (h : AffineUniformFreq 1 Real.goldenRatio) :
    vandeheyS7_add_phi :=
  affineCFN_of_uniformFreq one_pos _ h

/-! ## Audit surface

The frozen statements are pinned by type here; a change to any of them breaks this block. -/

section Audit

example : VandeheyS7Problem1 =
    (∀ q r : ℝ, q ≠ 0 → IsQuadOverRat q → IsQuadOverRat r →
      ∀ x : ℝ, IsCFNormal (Int.fract x) → IsCFNormal (Int.fract (q * x + r))) := rfl

example : vandeheyS7_mul_phi =
    (∀ x : ℝ, IsCFNormal (Int.fract x) →
      IsCFNormal (Int.fract (Real.goldenRatio * x + 0))) := rfl

example : vandeheyS7_add_phi =
    (∀ x : ℝ, IsCFNormal (Int.fract x) →
      IsCFNormal (Int.fract (1 * x + Real.goldenRatio))) := rfl

#print axioms affineCFN_of_uniformFreq
#print axioms not_affineCFN_zero
#print axioms vandeheyS7_mul_phi_of_uniformFreq
#print axioms vandeheyS7_add_phi_of_uniformFreq

end Audit

end NormalNumbers.VandeheyS7
