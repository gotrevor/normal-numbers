/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The ℤ[φ] wall, as Lean

Companion to `VandeheyS7.lean`.  That file reduced Vandehey's §7 Problem 1 to the single
statement `AffineUniformFreq q r` (frequency EXISTENCE; no value is needed).  This file states
and proves, in the kernel, the two facts that say why the Theorem 1.1 machinery cannot supply
that statement over `ℤ[φ]` — DIRECTION item 2.  Both were established informally in
`papers/vandehey-2017-open-problem-attack-map.md` (§1 and the 2026-08-24 merging trap); here they
are theorems.

## 1.  The finiteness certificate fails

Vandehey's state set is finite because a matrix over **ℤ** with bounded entries has finitely many
possibilities.  That is `finite_intCast_abs_le` below, and it is the *whole* source of the
finiteness: it is a statement about the ring, not about the dynamics.

Over `ℤ[φ]` the same hypothesis is worthless.  `Real.goldenRatio⁻¹ = φ - 1 ∈ ℤ[φ]` lies in
`(0,1)`, so its powers are an infinite set of elements of `ℤ[φ]` of absolute value `≤ 1`
(`infinite_zPhi_abs_le_one`).  Lifting to matrices, the unipotent matrices `![![1, ε ^ n], ![0, 1]]`
are an infinite set of determinant-one matrices over `ℤ[φ]` all of whose entries are bounded by
`1` (`infinite_zPhiMatrix_det_one_bounded`).  This is Dirichlet's unit theorem in its most
concrete form: a bounded real place does not bound the ring, because the *conjugate* place is
free to drift (measured at 2.354 nats/step in `experiments/PROBE-ROUTE-A.md`).

**What this does and does not say.**  It says Vandehey's finiteness LEMMA has no ℤ[φ] analogue —
the certificate is gone.  It does not by itself compute the reachable set of the actual
transducer.  That is the honest scope, and it is the scope that matters: the proof of Theorem 1.1
uses only the certificate.

## 2.  Pathwise merging is impossible

Two transducer states over ℤ[φ] coincide only if the conjugating matrix `M` carries one integer
matrix to another, i.e. `M * N = V * M` with both `V` and `N` integral.  For `M = diag(φ, 1)`
this forces `V` to be **diagonal** (`conj_goldenRatio_integral_forces_diagonal`), i.e. the same
input prefix: there is no distinct pair of prefixes that merges.  So the Saloff-Coste–Zúñiga
finite-chain merging citation of Vandehey §5 cannot be replaced by any coupling or synchronising-
word argument; a substitute must be *distributional* (Birkhoff–Hopf cone contraction), which is
exactly Route A's node 3.

This is a positive statement about a genuine obstruction, so it is stated for the honest reason:
it closes off a route, and the closure is machine-checked rather than asserted.
-/

namespace NormalNumbers.VandeheyS7

open Real

/-! ## `ℤ[φ]` -/

/-- Membership in the ring of integers `ℤ[φ]` of `ℚ(√5)`, as a predicate on `ℝ`. -/
def IsZPhi (x : ℝ) : Prop := ∃ a b : ℤ, x = (a : ℝ) + (b : ℝ) * goldenRatio

theorem isZPhi_intCast (n : ℤ) : IsZPhi (n : ℝ) := ⟨n, 0, by push_cast; ring⟩

theorem isZPhi_one : IsZPhi 1 := ⟨1, 0, by push_cast; ring⟩

theorem isZPhi_zero : IsZPhi 0 := ⟨0, 0, by push_cast; ring⟩

theorem isZPhi_goldenRatio : IsZPhi goldenRatio := ⟨0, 1, by push_cast; ring⟩

theorem IsZPhi.add {x y : ℝ} (hx : IsZPhi x) (hy : IsZPhi y) : IsZPhi (x + y) := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a + c, b + d, by push_cast; ring⟩

/-- Closure under multiplication is where `φ² = φ + 1` enters. -/
theorem IsZPhi.mul {x y : ℝ} (hx : IsZPhi x) (hy : IsZPhi y) : IsZPhi (x * y) := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  refine ⟨a * c + b * d, a * d + b * c + b * d, ?_⟩
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  push_cast
  linear_combination ((b : ℝ) * (d : ℝ)) * hsq

theorem IsZPhi.pow {x : ℝ} (hx : IsZPhi x) : ∀ n : ℕ, IsZPhi (x ^ n)
  | 0 => by simpa using isZPhi_one
  | n + 1 => by rw [pow_succ]; exact (IsZPhi.pow hx n).mul hx

/-- `ε = φ - 1 = φ⁻¹`, the fundamental unit's inverse: in `ℤ[φ]`, and in `(0,1)`. -/
noncomputable def zeta : ℝ := goldenRatio - 1

theorem isZPhi_zeta : IsZPhi zeta := ⟨-1, 1, by simp only [zeta]; push_cast; ring⟩

theorem zeta_pos : 0 < zeta := by
  have := one_lt_goldenRatio
  simp only [zeta]; linarith

theorem zeta_lt_one : zeta < 1 := by
  have := goldenRatio_lt_two
  simp only [zeta]; linarith

/-! ## 1.  The finiteness certificate: holds over ℤ, fails over ℤ[φ] -/

/-- **Where Vandehey's finiteness comes from.**  Over `ℤ`, a bound on the absolute value bounds
the set.  Content locator: this, and nothing about the dynamics, is the certificate. -/
theorem finite_intCast_abs_le (D : ℝ) :
    {x : ℝ | (∃ n : ℤ, x = (n : ℝ)) ∧ |x| ≤ D}.Finite := by
  have hsub : {x : ℝ | (∃ n : ℤ, x = (n : ℝ)) ∧ |x| ≤ D} ⊆
      (fun n : ℤ => (n : ℝ)) '' (Set.Icc ⌈-D⌉ ⌊D⌋) := by
    rintro x ⟨⟨n, rfl⟩, hn⟩
    refine ⟨n, ⟨?_, ?_⟩, rfl⟩
    · exact Int.ceil_le.2 (by simpa using neg_le_of_abs_le hn)
    · exact Int.le_floor.2 (by simpa using le_of_abs_le hn)
  exact Set.Finite.subset ((Set.finite_Icc _ _).image _) hsub

/-- **The certificate fails over `ℤ[φ]`.**  The powers of `ζ = φ − 1` are infinitely many
elements of `ℤ[φ]` of absolute value at most `1`.  This is Dirichlet's unit theorem made
concrete, and it is exactly why the Theorem 1.1 state set is not finite over `ℤ[φ]`. -/
theorem infinite_zPhi_abs_le_one : {x : ℝ | IsZPhi x ∧ |x| ≤ 1}.Infinite := by
  have hanti : StrictAnti (fun n : ℕ => zeta ^ n) := fun _ _ h =>
    pow_lt_pow_right_of_lt_one₀ zeta_pos zeta_lt_one h
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => zeta ^ n)
    hanti.injective (fun n => ⟨isZPhi_zeta.pow n, ?_⟩)
  rw [abs_of_pos (pow_pos zeta_pos n)]
  exact pow_le_one₀ zeta_pos.le zeta_lt_one.le

/-- The matrix form: infinitely many determinant-one matrices over `ℤ[φ]` with every entry
bounded by `1`.  Over `ℤ` the same set is finite by `finite_intCast_abs_le`. -/
theorem infinite_zPhiMatrix_det_one_bounded :
    {M : Matrix (Fin 2) (Fin 2) ℝ |
      (∀ i j, IsZPhi (M i j)) ∧ (∀ i j, |M i j| ≤ 1) ∧ M.det = 1}.Infinite := by
  have hanti : StrictAnti (fun n : ℕ => zeta ^ n) := fun _ _ h =>
    pow_lt_pow_right_of_lt_one₀ zeta_pos zeta_lt_one h
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => !![1, zeta ^ n; 0, 1]) ?_ ?_
  · intro m n hmn
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hmn
    simp only [Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply] at h01
    exact hanti.injective h01
  · intro n
    have hzn : |zeta ^ n| ≤ 1 := by
      rw [abs_of_pos (pow_pos zeta_pos n)]
      exact pow_le_one₀ zeta_pos.le zeta_lt_one.le
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        first
          | exact isZPhi_one
          | exact isZPhi_zero
          | exact isZPhi_zeta.pow n
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [abs_of_pos zeta_pos] <;>
        exact pow_le_one₀ zeta_pos.le zeta_lt_one.le
    · simp [Matrix.det_fin_two]

/-! ## 2.  Pathwise merging is impossible -/

/-- An integer multiple of `φ` is an integer only when the multiplier vanishes. -/
theorem intCast_mul_goldenRatio_eq_intCast_iff {b n : ℤ}
    (h : (b : ℝ) * goldenRatio = (n : ℝ)) : b = 0 := by
  by_contra hb
  have hirr : Irrational ((b : ℝ) * goldenRatio) :=
    goldenRatio_irrational.intCast_mul hb
  rw [h] at hirr
  exact (Int.not_irrational n) hirr

/-- **Pathwise merging is impossible.**  Let `V` be an integer matrix and `N` a real matrix with
`diag(φ,1) * N = V * diag(φ,1)` — i.e. `N = M⁻¹ V M` for the conjugator `M = diag(φ,1)` of the
`x ↦ φx` transducer.  If `N` is again integral then `V` is **diagonal**.

Consequence for the attack: distinct input prefixes never produce coinciding states, so no
coupling / synchronising-word merging argument exists, and Vandehey's §5 finite-chain merging
must be replaced by a distributional statement. -/
theorem conj_goldenRatio_integral_forces_diagonal
    (V N : Matrix (Fin 2) (Fin 2) ℝ)
    (hV : ∀ i j, ∃ m : ℤ, V i j = (m : ℝ))
    (hN : ∀ i j, ∃ m : ℤ, N i j = (m : ℝ))
    (hconj : (Matrix.diagonal ![goldenRatio, 1]) * N
      = V * (Matrix.diagonal ![goldenRatio, 1])) :
    V 0 1 = 0 ∧ V 1 0 = 0 := by
  have hentry : ∀ i j : Fin 2,
      (Matrix.diagonal ![goldenRatio, 1] * N) i j
        = (V * Matrix.diagonal ![goldenRatio, 1]) i j := fun i j => by rw [hconj]
  constructor
  · -- row 0, column 1: `φ * N 0 1 = V 0 1 * 1`
    have h := hentry 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at h
    obtain ⟨m, hm⟩ := hN 0 1
    obtain ⟨k, hk⟩ := hV 0 1
    -- `φ * m = k`, so `m = 0` and hence `V 0 1 = 0`
    rw [hm, hk] at h
    have hm0 : m = 0 := intCast_mul_goldenRatio_eq_intCast_iff (b := m) (n := k) (by linarith)
    have : (k : ℝ) = 0 := by rw [← h, hm0]; push_cast; ring
    rw [hk, this]
  · -- row 1, column 0: `N 1 0 = V 1 0 * φ`
    have h := hentry 1 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at h
    obtain ⟨m, hm⟩ := hN 1 0
    obtain ⟨k, hk⟩ := hV 1 0
    rw [hm, hk] at h
    have hk0 : k = 0 := intCast_mul_goldenRatio_eq_intCast_iff (b := k) (n := m) (by linarith)
    rw [hk, hk0]
    push_cast; ring

section Audit

#print axioms finite_intCast_abs_le
#print axioms infinite_zPhi_abs_le_one
#print axioms infinite_zPhiMatrix_det_one_bounded
#print axioms conj_goldenRatio_integral_forces_diagonal

end Audit

end NormalNumbers.VandeheyS7
