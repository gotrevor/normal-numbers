/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.TripleReturn
import NormalNumbers.MasterConjectures

/-! # Review: infinitude, not a non-torsion point, is the needed ingredient

The full orbit closure contains the starting point.  The ω-limit set need
not, but it is infinite for every irrational starting point.  Consequently
the odd-invariance node alone suffices for π; PiSelfReturn and
PiOrbitClosureNonTorsion are not required intermediate goals.
-/

namespace NormalNumbers.PiDisjunctiveRoutes
open Set Filter Topology MasterConjectures

theorem hasFiniteAttractor_of_finite_circleOmegaLimit (b : ℕ) (x : ℝ)
    (hfin : (circleOmegaLimit b x).Finite) : HasFiniteAttractor (orbit b x) := by
  classical
  choose rep hrep using (fun y : UnitAddCircle => QuotientAddGroup.mk_surjective y)
  let W : Finset ℝ := hfin.toFinset.image rep
  have hne : (circleOmegaLimit b x).Nonempty :=
    nonempty_omegaLimit atTop (circleFlow b) {(x : UnitAddCircle)}
      (singleton_nonempty _)
  refine ⟨W, ?_, fun ε hε => ?_⟩
  · obtain ⟨y, hy⟩ := hne
    exact ⟨rep y, Finset.mem_image.mpr ⟨y, hfin.mem_toFinset.mpr hy, rfl⟩⟩
  · let U : Set UnitAddCircle := ⋃ y ∈ circleOmegaLimit b x, Metric.ball y ε
    have hU : IsOpen U := isOpen_iUnion fun y => isOpen_iUnion fun _ => Metric.isOpen_ball
    have hKU : circleOmegaLimit b x ⊆ U := by
      intro y hy
      exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, by simpa using hε⟩⟩
    have hev := eventually_mapsTo_of_isOpen_of_omegaLimit_subset
      atTop (circleFlow b) {(x : UnitAddCircle)} hU hKU
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun k => ?_⟩
    have hm := hN (N + k) (by omega) (mem_singleton _)
    obtain ⟨y, hy, hd⟩ : ∃ y ∈ circleOmegaLimit b x,
        dist (circleFlow b (N + k) (x : UnitAddCircle)) y < ε := by
      simpa only [U, mem_iUnion, Metric.mem_ball, exists_prop] using hm
    refine ⟨rep y, Finset.mem_image.mpr ⟨y, hfin.mem_toFinset.mpr hy, rfl⟩, ?_⟩
    have hc : circDist (orbit b x (N + k)) (rep y) =
        dist (circleOrbit b x (N + k)) y := by
      calc circDist (orbit b x (N + k)) (rep y) =
          dist ((orbit b x (N + k) : ℝ) : UnitAddCircle) ((rep y : ℝ) : UnitAddCircle) := by
            rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
            rfl
        _ = dist (circleOrbit b x (N + k)) y := by
          rw [circleOrbit_eq_coe_orbit, hrep]
    rw [hc]
    exact hd

@[blueprint (title := "Every irrational integer-base orbit has an infinite omega-limit set")]
theorem circleOmegaLimit_infinite_of_irrational {b : ℕ} (hb : 2 ≤ b)
    {x : ℝ} (hx : Irrational x) : (circleOmegaLimit b x).Infinite := by
  intro hfin
  exact not_irrational_of_hasFiniteAttractor_base b hb x
    (hasFiniteAttractor_of_finite_circleOmegaLimit b x hfin) hx

private theorem multIndep_two_odd {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    Furstenberg.MultIndep 2 q := by
  intro a b hab
  have ha : a = 0 := by
    by_contra ha
    have hdvd : 2 ∣ q ^ b := hab ▸ dvd_pow_self 2 ha
    have h := Nat.odd_iff.mp (hodd.pow (n := b))
    omega
  subst ha
  exact ⟨rfl, (Nat.pow_eq_one.mp hab.symm).resolve_left (by omega)⟩

@[blueprint (title := "Pi needs odd invariance alone, without a self-return premise")]
theorem pi_disjunctive_iff_oddInvariant :
    IsDisjunctive 2 Real.pi ↔ PiOrbitClosureOddInvariant := by
  constructor
  · intro h
    have hK := (isDisjunctive_iff_circleOmegaLimit_eq_univ 2 Real.pi).mp h
    refine ⟨3, by norm_num, by decide, ?_⟩
    rw [hK]
    exact mapsTo_univ _ _
  · rintro ⟨q, hq, hodd, hQ⟩
    have hInf := circleOmegaLimit_infinite_of_irrational (b := 2) (by omega) irrational_pi
    have h2 := mapsTo_circleMap_circleOmegaLimit 2 Real.pi
    rcases Furstenberg.isClosed_invariant_finite_or_univ (by omega) (by omega)
      (multIndep_two_odd hq hodd) (isClosed_circleOmegaLimit 2 Real.pi) h2 hQ with hf | hu
    · exact False.elim (hInf hf)
    · exact (isDisjunctive_iff_circleOmegaLimit_eq_univ 2 Real.pi).mpr hu

#print axioms circleOmegaLimit_infinite_of_irrational
#print axioms pi_disjunctive_iff_oddInvariant

end NormalNumbers.PiDisjunctiveRoutes
