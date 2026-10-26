/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.TripleReturn
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Route 1: the binary Liouville sibling

Degenerate-corner check for `PiOrbitClosureNonTorsion`: for the irrational
`liouvilleNumber 2 = ∑ 2^{-i!}`, every point of the binary orbit closure is a torsion
(dyadic) point.  So "the orbit closure contains a non-torsion point" is a genuine
condition on π, not a consequence of irrationality.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set Filter Topology LiouvilleNumber Nat


/-- Between `k!` and `(k+1)!`, the doubling orbit of `∑ 2^{-i!}` sits just above the dyadic
point `2^{-((k+1)! - n)}` (mod 1), within `2^{-k}`. -/
private theorem liouvilleTwo_orbit_near_dyadic (k n : ℕ) (hk : k ! ≤ n) (hn : n < (k + 1)!) :
    ∃ z : ℤ, 0 ≤ (2:ℝ)^n * liouvilleNumber 2 - z - 1 / 2 ^ ((k+1)! - n) ∧
      (2:ℝ)^n * liouvilleNumber 2 - z - 1 / 2 ^ ((k+1)! - n) < 1 / 2 ^ k := by
  have h2 : (1:ℝ) < 2 := by norm_num
  have hsplit := partialSum_add_remainder h2 k
  have hsplit' := partialSum_add_remainder h2 (k+1)
  have hsucc := partialSum_succ 2 k
  refine ⟨∑ i ∈ Finset.range (k+1), (2:ℤ)^(n - i !), ?_, ?_⟩
  all_goals
    have hz : ((∑ i ∈ Finset.range (k+1), (2:ℤ)^(n - i !) : ℤ) : ℝ) = 2^n * partialSum 2 k := by
      push_cast
      rw [partialSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i ! ≤ n := le_trans (Nat.factorial_le (by simp at hi; omega)) hk
      rw [pow_sub₀ (2:ℝ) two_ne_zero this]; ring
    have hlead : (2:ℝ)^n * (1 / 2 ^ (k+1)!) = 1 / 2 ^ ((k+1)! - n) := by
      rw [pow_sub₀ (2:ℝ) two_ne_zero hn.le]; field_simp
    have hrem : (2:ℝ)^n * liouvilleNumber 2 - (∑ i ∈ Finset.range (k+1), (2:ℤ)^(n - i !) : ℤ)
        - 1 / 2 ^ ((k+1)! - n) = 2^n * remainder 2 (k+1) := by
      rw [hz, ← hlead, ← hsplit']; rw [hsucc]; ring
    rw [hrem]
  · exact mul_nonneg (by positivity) (remainder_pos h2 _).le
  · have hlt := remainder_lt (k+1) (le_refl (2:ℝ))
    calc (2:ℝ)^n * remainder 2 (k+1) < 2^n * (1 / (2 ^ (k+1)!) ^ (k+1)) :=
          mul_lt_mul_of_pos_left hlt (by positivity)
      _ ≤ 1 / 2 ^ k := by
          rw [← pow_mul, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
            ← pow_add]
          apply pow_le_pow_right₀ (by norm_num)
          have : k ≤ k * (k+1)! := Nat.le_mul_of_pos_right k (Nat.factorial_pos _)
          nlinarith

/-- The binary orbit closure of `∑ 2^{-i!}` consists of dyadic points. -/
theorem circleOmegaLimit_liouvilleTwo_subset_dyadic :
    circleOmegaLimit 2 (liouvilleNumber 2) ⊆
      ((↑) : ℝ → UnitAddCircle) '' insert 0 (range fun r : ℕ => (1/2 : ℝ) ^ r) := by
  set C : Set ℝ := insert 0 (range fun r : ℕ => (1/2 : ℝ) ^ r)
  have hC : IsCompact C :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).isCompact_insert_range
  have hS : IsClosed (((↑) : ℝ → UnitAddCircle) '' C) :=
    (hC.image (AddCircle.continuous_mk' 1)).isClosed
  intro y hy
  induction y using QuotientAddGroup.induction_on with
  | H r =>
  rw [mem_circleOmegaLimit_two_iff] at hy
  refine hS.closure_subset_iff.2 subset_rfl (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨K0, hK0⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨n, hNn, hnear⟩ := hy (ε/2) (half_pos hε) (K0 ! )
  have hex : ∃ k, n < (k+1)! := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.self_le_factorial _)⟩
  set k := Nat.find hex with hkdef
  have hkn : n < (k+1)! := Nat.find_spec hex
  have hkle : k ! ≤ n := by
    rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
    · rw [h0]; have := Nat.factorial_pos K0; simp; omega
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [show k - 1 + 1 = k by omega] at this; omega
  have hK0k : K0 ≤ k := by
    by_contra h
    have := Nat.factorial_le (show k + 1 ≤ K0 by omega); omega
  obtain ⟨z, hz0, hz⟩ := liouvilleTwo_orbit_near_dyadic k n hkle hkn
  have h1 : dist (((2:ℝ)^n * liouvilleNumber 2 : ℝ) : UnitAddCircle)
      ((1 / 2 ^ ((k+1)! - n) : ℝ) : UnitAddCircle) < 1 / 2 ^ k := by
    rw [← nearInteger_sub_iff_dist]
    exact ⟨z, by rw [abs_lt]; constructor <;> linarith⟩
  have h2 := (nearInteger_sub_iff_dist _ _ _).1 hnear
  have h3 : (1:ℝ) / 2 ^ k ≤ (1/2) ^ K0 := by
    rw [← one_div_pow]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hK0k
  refine ⟨((1 / 2 ^ ((k+1)! - n) : ℝ) : UnitAddCircle),
    ⟨(1/2:ℝ)^((k+1)! - n), Or.inr ⟨_, rfl⟩, by rw [one_div_pow]⟩, ?_⟩
  calc dist (r : UnitAddCircle) _ ≤ dist (r : UnitAddCircle)
        (((2:ℝ)^n * liouvilleNumber 2 : ℝ) : UnitAddCircle) + dist
        (((2:ℝ)^n * liouvilleNumber 2 : ℝ) : UnitAddCircle)
        ((1 / 2 ^ ((k+1)! - n) : ℝ) : UnitAddCircle) := dist_triangle _ _ _
    _ < ε := by rw [_root_.dist_comm] at h2; linarith

/-- Proved sibling refutation: an irrational real whose binary orbit closure has no
non-torsion point.  Hence the analogue of `PiOrbitClosureNonTorsion` fails for some
irrationals, and that node is not implied by irrationality of π alone. -/
@[blueprint (title := "Binary Liouville number: irrational, orbit closure all torsion")]
theorem liouvilleTwo_irrational_and_orbitClosure_torsion :
    Irrational (liouvilleNumber 2) ∧
      ∀ y ∈ circleOmegaLimit 2 (liouvilleNumber 2), IsOfFinAddOrder y := by
  refine ⟨by exact_mod_cast (liouville_liouvilleNumber (m := 2) le_rfl).irrational, ?_⟩
  intro y hy
  obtain ⟨t, ht, rfl⟩ := circleOmegaLimit_liouvilleTwo_subset_dyadic hy
  rcases ht with rfl | ⟨r, rfl⟩
  · simp
  · refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 ^ r, by positivity, ?_⟩
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    push_cast
    rw [← mul_pow, show (2:ℝ) * (1/2) = 1 by norm_num, one_pow]
    exact AddCircle.coe_period (p := (1:ℝ))

/-- Open node: π is a recurrent point of doubling, i.e. it lies in its own binary orbit
closure (every prefix of π's binary expansion recurs, arbitrarily late).
Costume audit: (a) implied by the sink; (b) strictly weaker in kind, since it supplies no
`×q`-invariance; it is a target of the same shape as `TripleReturn` with multiplier `1`.
Degenerate corner: fails for the irrational `∑ 2^{-i!}`
(`not_selfReturn_liouvilleTwo`).  Confidence true: 99% (π believed normal). -/
def PiSelfReturn : Prop :=
  ((Real.pi : ℝ) : UnitAddCircle) ∈ circleOmegaLimit 2 Real.pi

/-- Proved edge: self-return supplies Furstenberg ingredient (i). -/
theorem piOrbitClosureNonTorsion_of_selfReturn (h : PiSelfReturn) :
    PiOrbitClosureNonTorsion :=
  ⟨_, h, not_isOfFinAddOrder_of_irrational' irrational_pi⟩

/-- Proved: the binary Liouville sibling is not a recurrent point of doubling. -/
theorem not_selfReturn_liouvilleTwo :
    ((liouvilleNumber 2 : ℝ) : UnitAddCircle) ∉ circleOmegaLimit 2 (liouvilleNumber 2) :=
  fun h => not_isOfFinAddOrder_of_irrational'
    liouvilleTwo_irrational_and_orbitClosure_torsion.1
    (liouvilleTwo_irrational_and_orbitClosure_torsion.2 _ h)

/-- Proved: the binary Liouville sibling is not binary disjunctive (its orbit closure is
all torsion, while the circle has non-torsion points). -/
theorem not_isDisjunctive_liouvilleTwo : ¬ IsDisjunctive 2 (liouvilleNumber 2) := by
  intro h
  rw [isDisjunctive_iff_circleOmegaLimit_eq_univ] at h
  exact not_isOfFinAddOrder_of_irrational' liouvilleTwo_irrational_and_orbitClosure_torsion.1
    (liouvilleTwo_irrational_and_orbitClosure_torsion.2 _ (h ▸ mem_univ _))

/-- Proved obstruction for Route 1: ingredient (i) does not bootstrap to ingredient (ii).
There is a closed `×2`-invariant subset of the circle containing a non-torsion point that is
*not* `×3`-invariant (the full binary orbit closure of `∑ 2^{-i!}`).  So any proof of
`PiOrbitClosureOddInvariant` must use arithmetic of π beyond "closed, ×2-invariant,
contains an irrational point". -/
@[blueprint (title := "A ×2-closed set with an irrational point need not be ×3-invariant")]
theorem exists_closed_two_invariant_nonTorsion_not_three_invariant :
    ∃ L : Set UnitAddCircle, IsClosed L ∧
      MapsTo (2 • · : UnitAddCircle → UnitAddCircle) L L ∧
      (∃ y ∈ L, ¬ IsOfFinAddOrder y) ∧
      ¬ MapsTo (3 • · : UnitAddCircle → UnitAddCircle) L L := by
  set x : ℝ := liouvilleNumber 2
  set L := closure (range (circleOrbit 2 x))
  have h2 : MapsTo (2 • · : UnitAddCircle → UnitAddCircle) L L := by
    refine MapsTo.closure ?_ (continuous_nsmul 2)
    rintro _ ⟨n, rfl⟩
    refine ⟨n + 1, ?_⟩
    simp only [circleOrbit, circleFlow_apply, smul_smul, pow_succ, mul_comm]
  have hnt : ¬ IsOfFinAddOrder ((x : ℝ) : UnitAddCircle) :=
    not_isOfFinAddOrder_of_irrational' liouvilleTwo_irrational_and_orbitClosure_torsion.1
  have hxL : ((x : ℝ) : UnitAddCircle) ∈ L :=
    subset_closure ⟨0, by simp [circleOrbit]⟩
  refine ⟨L, isClosed_closure, h2, ⟨_, hxL, hnt⟩, fun h3 => ?_⟩
  rcases Furstenberg.isClosed_invariant_finite_or_univ (by norm_num) (by norm_num)
    Furstenberg.multIndep_two_three isClosed_closure h2 h3 with hf | hu
  · exact (Furstenberg.infinite_of_mem_not_torsion (le_refl 2) h2 hxL hnt).not_finite hf
  · apply not_isDisjunctive_liouvilleTwo
    rw [isDisjunctive_iff_denseRange_circleOrbit]
    exact dense_iff_closure_eq.2 hu

end NormalNumbers.PiDisjunctiveRoutes
