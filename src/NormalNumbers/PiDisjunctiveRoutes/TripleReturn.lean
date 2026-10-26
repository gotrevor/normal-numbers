/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.Disjunctive
import NormalNumbers.Furstenberg
import NormalNumbers.ConditionalDisjunctive

/-!
# Route 1: the triple-return target

Route 1 of three experimental routes to disjunctivity of π.
See `NormalNumbers.PiDisjunctiveRoutes` for the shared framing and evidence tiers.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set Filter Topology

/-- Distance to an integer, expressed without a choice of nearest integer. -/
def NearInteger (x ε : ℝ) : Prop := ∃ z : ℤ, |x - (z : ℝ)| < ε

/-- One prescribed return target, at arbitrarily late positions. -/
def TripleReturn (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ NearInteger (((2 : ℝ) ^ n - 3) * x) ε


/-- `NearInteger` is closeness on the unit circle. -/
theorem nearInteger_sub_iff_dist (a b ε : ℝ) :
    NearInteger (a - b) ε ↔ dist (a : UnitAddCircle) (b : UnitAddCircle) < ε := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  constructor
  · rintro ⟨z, hz⟩; exact lt_of_le_of_lt (round_le _ z) hz
  · intro h; exact ⟨round (a - b), h⟩

/-- Membership in the binary orbit closure, as an arbitrarily-late return. -/
theorem mem_circleOmegaLimit_two_iff (x y : ℝ) : (y : UnitAddCircle) ∈ circleOmegaLimit 2 x ↔
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧ NearInteger ((2:ℝ)^n * x - y) ε := by
  unfold circleOmegaLimit
  rw [mem_omegaLimit_singleton_iff_mapClusterPt,
    Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  simp only [frequently_atTop, Metric.mem_ball, circleFlow_apply, nearInteger_sub_iff_dist]
  have : ∀ n : ℕ, (2 ^ n) • (x : UnitAddCircle) = (((2:ℝ)^n * x : ℝ) : UnitAddCircle) := by
    intro n; rw [← AddCircle.coe_nsmul, nsmul_eq_mul]; congr 1; push_cast; ring
  simp only [this]

private theorem omegaLimit_point_subset {x : ℝ} {z : UnitAddCircle} (hz : z ∈ circleOmegaLimit 2 x) :
    omegaLimit atTop (circleFlow 2) {z} ⊆ circleOmegaLimit 2 x := by
  intro y hy
  have := omegaLimit_subset_closure_image2 atTop (circleFlow 2) {z} univ_mem hy
  refine (closure_minimal ?_ (isClosed_circleOmegaLimit 2 x)) this
  rintro _ ⟨t, -, _, rfl, rfl⟩
  exact isInvariant_circleOmegaLimit 2 x t hz

/-- If `3x` is in the binary orbit closure `K` of `x`, then `K` is `×3`-invariant. -/
theorem mapsTo_three_circleOmegaLimit {x : ℝ} (h3 : ((3 * x : ℝ) : UnitAddCircle) ∈ circleOmegaLimit 2 x) :
    MapsTo (3 • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 x)
      (circleOmegaLimit 2 x) := by
  have hm : MapsTo (3 • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 x)
      (omegaLimit atTop (circleFlow 2) {((3 * x : ℝ) : UnitAddCircle)}) := by
    unfold circleOmegaLimit
    refine mapsTo_omegaLimit _ (ga := (3 • · : UnitAddCircle → UnitAddCircle)) ?_ ?_
      (continuous_nsmul 3)
    · intro a ha; rw [mem_singleton_iff.1 ha, mem_singleton_iff]
      show (3:ℕ) • (x : UnitAddCircle) = _
      rw [← AddCircle.coe_nsmul]
      congr 1; simp [nsmul_eq_mul]
    · intro t y; simp only [circleFlow_apply, smul_smul, mul_comm]
  exact fun y hy => omegaLimit_point_subset h3 (hm hy)

/-- `TripleReturn x` says exactly that `3x` lies in the binary orbit closure of `x`. -/
theorem tripleReturn_iff_mem_circleOmegaLimit (x : ℝ) :
    TripleReturn x ↔ ((3 * x : ℝ) : UnitAddCircle) ∈ circleOmegaLimit 2 x := by
  rw [mem_circleOmegaLimit_two_iff]
  have : ∀ n : ℕ, ((2 : ℝ) ^ n - 3) * x = (2 : ℝ) ^ n * x - 3 * x := fun n => by ring
  simp only [TripleReturn, this]

private theorem not_isOfFinAddOrder_of_irrational' {x : ℝ} (hx : Irrational x) :
    ¬ IsOfFinAddOrder (x : UnitAddCircle) := by
  rw [AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro q hq
  rw [div_one] at hq
  exact hx ⟨q, hq⟩

/-- A deliberately generous quantitative return conjecture for π.
Confidence in truth: 90%, heuristic only; no proof mechanism established.
The bound is exponential in the requested precision, not in a starting index. -/
@[blueprint (title := "π returns near its triple within an exponential precision budget")]
def PiQuantitativeTripleReturn : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ n : ℕ, k ≤ n ∧ n ≤ C * 4 ^ k ∧
      NearInteger (((2 : ℝ) ^ n - 3) * Real.pi) (1 / 2 ^ k)

/-- Proved.  With K the binary ω-limit set `circleOmegaLimit 2 x`:
Let K be the binary orbit closure on the circle.  TripleReturn gives 3x ∈ K.
Since K is ×2-invariant, every 2^m 3x belongs to K.  Continuity gives 3K ⊆ K.
Irrationality makes K infinite; the existing ×2×3 theorem gives K = circle.
Conversely, a dense irrational binary orbit has every tail dense, and hence
approaches 3x.  This equivalence explicitly prevents calling the return
premise weaker than disjunctivity. -/
@[blueprint (title := "A single triple-return target characterizes binary disjunctivity")]
theorem tripleReturn_iff_disjunctive {x : ℝ} (hx : Irrational x) :
    TripleReturn x ↔ IsDisjunctive 2 x := by
  rw [tripleReturn_iff_mem_circleOmegaLimit, isDisjunctive_iff_circleOmegaLimit_eq_univ]
  constructor
  · intro h3
    have h2 : MapsTo (2 • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 x)
        (circleOmegaLimit 2 x) := mapsTo_circleMap_circleOmegaLimit 2 x
    have hnt := not_isOfFinAddOrder_of_irrational'
      (hx.natCast_mul (by norm_num : (3:ℕ) ≠ 0))
    push_cast at hnt
    rcases Furstenberg.isClosed_invariant_finite_or_univ (by norm_num) (by norm_num)
      Furstenberg.multIndep_two_three (isClosed_circleOmegaLimit 2 x) h2
      (mapsTo_three_circleOmegaLimit h3) with hf | hu
    · exact absurd hf (Furstenberg.infinite_of_mem_not_torsion (le_refl 2) h2 h3 hnt).not_finite
    · exact hu
  · intro h; rw [h]; trivial

/-- Proved transfer: take precision k ≥ the requested
starting index, then let k grow; apply the previous bootstrap and π irrational. -/
theorem pi_disjunctive_of_quantitativeTripleReturn
    (h : PiQuantitativeTripleReturn) : IsDisjunctive 2 Real.pi := by
  obtain ⟨C, -, hC⟩ := h
  apply (tripleReturn_iff_disjunctive irrational_pi).1
  intro ε hε N
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  set k := max (max N 1) k₀
  obtain ⟨n, hkn, -, z, hz⟩ := hC k (by omega)
  refine ⟨n, le_trans (by omega) hkn, z, lt_of_lt_of_le hz ?_⟩
  calc (1 : ℝ) / 2 ^ k = (1 / 2) ^ k := by rw [one_div_pow]
    _ ≤ (1 / 2) ^ k₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ ε := hk₀.le

/-- If `qx` is in the binary orbit closure `K` of `x`, then `K` is `×q`-invariant. -/
theorem mapsTo_mul_circleOmegaLimit {x : ℝ} (q : ℕ)
    (hq : ((q * x : ℝ) : UnitAddCircle) ∈ circleOmegaLimit 2 x) :
    MapsTo (q • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 x)
      (circleOmegaLimit 2 x) := by
  have hm : MapsTo (q • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 x)
      (omegaLimit atTop (circleFlow 2) {((q * x : ℝ) : UnitAddCircle)}) := by
    unfold circleOmegaLimit
    refine mapsTo_omegaLimit _ (ga := (q • · : UnitAddCircle → UnitAddCircle)) ?_ ?_
      (continuous_nsmul q)
    · intro a ha; rw [mem_singleton_iff.1 ha, mem_singleton_iff]
      show q • (x : UnitAddCircle) = _
      rw [← AddCircle.coe_nsmul]
      congr 1; simp [nsmul_eq_mul]
    · intro t y; simp only [circleFlow_apply, smul_smul, mul_comm]
  exact fun y hy => omegaLimit_point_subset hq (hm hy)

private theorem multIndep_two_of_odd {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    Furstenberg.MultIndep 2 q := by
  intro a b hab
  have ha : a = 0 := by
    by_contra ha
    have hdvd : 2 ∣ q ^ b := hab ▸ dvd_pow_self 2 ha
    exact (Nat.odd_iff.mp (hodd.pow (n := b))) |> fun h => by omega
  subst ha
  exact ⟨rfl, (Nat.pow_eq_one.mp hab.symm).resolve_left (by omega)⟩

/-- Proved generalisation of `tripleReturn_iff_disjunctive`: any odd multiplier `q ≥ 3`
works.  For irrational `x`, `qx` lies in the binary orbit closure iff `x` is binary
disjunctive.  Costume audit: equivalent to the sink for every such `q`, so the family
"∃ odd q ≥ 3, qx ∈ K" is also the sink in a costume; its value is that a proof may pick
whichever odd `q` the arithmetic of `x` favours. -/
@[blueprint (title := "Any odd multiple of x in its binary orbit closure forces disjunctivity")]
theorem mem_circleOmegaLimit_oddMul_iff_disjunctive {x : ℝ} (hx : Irrational x)
    {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    ((q * x : ℝ) : UnitAddCircle) ∈ circleOmegaLimit 2 x ↔ IsDisjunctive 2 x := by
  rw [isDisjunctive_iff_circleOmegaLimit_eq_univ]
  constructor
  · intro hqK
    have h2 : MapsTo (2 • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 x)
        (circleOmegaLimit 2 x) := mapsTo_circleMap_circleOmegaLimit 2 x
    have hnt := not_isOfFinAddOrder_of_irrational'
      (hx.natCast_mul (by omega : q ≠ 0))
    rcases Furstenberg.isClosed_invariant_finite_or_univ (le_refl 2) (by omega)
      (multIndep_two_of_odd hq hodd) (isClosed_circleOmegaLimit 2 x) h2
      (mapsTo_mul_circleOmegaLimit q hqK) with hf | hu
    · exact absurd hf
        (Furstenberg.infinite_of_mem_not_torsion (le_refl 2) h2 hqK hnt).not_finite
    · exact hu
  · intro h; rw [h]; trivial

/-- Open node, ingredient (i) of the Furstenberg step: the binary orbit closure of π
contains a non-torsion (irrational) point.
Costume audit: (a) implied by the sink (K = 𝕋), so it is not an advance by itself;
(b) strictly weaker than the sink in general: ingredient (ii), ×q-invariance, is what is
missing.  Degenerate corner: for a binary Liouville number such as `∑ 2^{-n!}` the
closure is `{0}` (standard, not yet Lean-checked), so the node is not automatic.
Confidence true for π: 99% (heuristic: π is believed normal). -/
def PiOrbitClosureNonTorsion : Prop :=
  ∃ y ∈ circleOmegaLimit 2 Real.pi, ¬ IsOfFinAddOrder y

/-- Open node, ingredient (ii): the binary orbit closure of π is `×q`-invariant for some
odd `q ≥ 3`.  Costume audit: implied by the sink; together with
`PiOrbitClosureNonTorsion` it gives the sink (`pi_disjunctive_of_nonTorsion_of_oddInvariant`).
Alone it is satisfied by `K = {0}`-type closures, so it is not the sink by itself. -/
def PiOrbitClosureOddInvariant : Prop :=
  ∃ q : ℕ, 3 ≤ q ∧ Odd q ∧
    MapsTo (q • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 Real.pi)
      (circleOmegaLimit 2 Real.pi)

/-- Proved edge: the two Furstenberg ingredients give the sink. -/
theorem pi_disjunctive_of_nonTorsion_of_oddInvariant
    (h1 : PiOrbitClosureNonTorsion) (h2 : PiOrbitClosureOddInvariant) :
    IsDisjunctive 2 Real.pi := by
  obtain ⟨y, hy, hnt⟩ := h1
  obtain ⟨q, hq, hodd, hQ⟩ := h2
  rw [isDisjunctive_iff_circleOmegaLimit_eq_univ]
  have h2' : MapsTo (2 • · : UnitAddCircle → UnitAddCircle) (circleOmegaLimit 2 Real.pi)
      (circleOmegaLimit 2 Real.pi) := mapsTo_circleMap_circleOmegaLimit 2 Real.pi
  rcases Furstenberg.isClosed_invariant_finite_or_univ (le_refl 2) (by omega)
    (multIndep_two_of_odd hq hodd) (isClosed_circleOmegaLimit 2 Real.pi) h2' hQ with hf | hu
  · exact absurd hf (Furstenberg.infinite_of_mem_not_torsion (le_refl 2) h2' hy hnt).not_finite
  · exact hu

end NormalNumbers.PiDisjunctiveRoutes
