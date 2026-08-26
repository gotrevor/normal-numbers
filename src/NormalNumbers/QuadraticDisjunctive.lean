/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ConditionalDisjunctive
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Axiom M and quadratic disjunctivity (Track D3)

This file freezes the documented invariant-set avoidance hypothesis `M_b` as
the named `Prop` `QuadraticHypothesisM`; it does not declare a Lean axiom.
The elementary dynamical assembly is separated from its real geometric cost:
`MissingWordSubshiftDimensionBound b`, the assertion that every nontrivial
base-`b` missing-word subshift has Hausdorff dimension strictly below one.

The endpoint-safe phase space is `DisjunctiveCircle = ℝ ⧸ ℤ`, the circle model
of `[0,1)` already used by Track D0--D2.  Open word cylinders avoid the two
expansion ambiguity at their endpoints.  Their avoidance sets are closed and
forward invariant, and a canonical expansion missing the word lies in the
corresponding set.
-/

namespace NormalNumbers

open Filter Set MeasureTheory
open scoped ENNReal NNReal

/-- A real quadratic irrational: an irrational zero of an integral quadratic
polynomial with nonzero leading coefficient.  Irrationality rules out degree
one, so this is exactly algebraic degree two over `ℚ`. -/
def IsQuadraticIrrational (x : ℝ) : Prop :=
  Irrational x ∧ ∃ a d c : ℤ, a ≠ 0 ∧
    (a : ℝ) * x ^ 2 + (d : ℝ) * x + (c : ℝ) = 0

/-- The image in the endpoint-identified circle of the open b-adic cylinder
determined by `w`. -/
def circleOpenWordCylinder (b : ℕ) (w : List ℕ) : Set DisjunctiveCircle :=
  ((↑) : ℝ → DisjunctiveCircle) '' openWordCylinder b w

theorem isOpen_circleOpenWordCylinder (b : ℕ) (w : List ℕ) :
    IsOpen (circleOpenWordCylinder b w) := by
  exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The circle realization of the subshift in which `w` is missing.  We avoid
the open cylinder; the possible cylinder endpoints form only the usual
base-expansion ambiguity and this choice makes the realization closed. -/
def circleMissingWordSubshift (b : ℕ) (w : List ℕ) : Set DisjunctiveCircle :=
  {y | ∀ n : ℕ, circleFlow b n y ∉ circleOpenWordCylinder b w}

theorem isClosed_circleMissingWordSubshift (b : ℕ) (w : List ℕ) :
    IsClosed (circleMissingWordSubshift b w) := by
  rw [show circleMissingWordSubshift b w = ⋂ n : ℕ,
      (circleFlow b n) ⁻¹' (circleOpenWordCylinder b w)ᶜ by
    ext y
    simp [circleMissingWordSubshift]]
  exact isClosed_iInter fun n =>
    (isOpen_circleOpenWordCylinder b w).isClosed_compl.preimage
      ((circleFlow b).continuous_toFun n)

theorem mapsTo_circleMap_circleMissingWordSubshift (b : ℕ) (w : List ℕ) :
    MapsTo (circleMap b) (circleMissingWordSubshift b w)
      (circleMissingWordSubshift b w) := by
  intro y hy n hn
  apply hy (n + 1)
  rw [(circleFlow b).map_add]
  simpa [circleMap] using hn

/-- If the canonical digit expansion of `x` never contains a valid word `w`,
then its circle point lies in the corresponding missing-word subshift. -/
theorem mem_circleMissingWordSubshift_of_not_occursAt {b : ℕ} (hb : 2 ≤ b)
    {x : ℝ} {w : List ℕ} (hw : ∀ d ∈ w, d < b)
    (havoid : ∀ n, ¬ OccursAt b x w n) :
    (x : DisjunctiveCircle) ∈ circleMissingWordSubshift b w := by
  intro n hn
  rcases hn with ⟨z, hz, hzcoe⟩
  have hval : blockNatVal b w < b ^ w.length := blockNatVal_lt b w hw
  have hpow : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
  have ha0 : (0 : ℝ) ≤ (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by
    positivity
  have hc1 : ((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length ≤ 1 := by
    rw [div_le_one hpow]
    exact_mod_cast Nat.succ_le_of_lt hval
  have hzIco : z ∈ Set.Ico (0 : ℝ) 1 := by
    change z ∈ openWordCylinder b w at hz
    exact ⟨ha0.trans hz.1.le, hz.2.trans_le hc1⟩
  have hcoeeq : (orbit b x n : DisjunctiveCircle) = (z : DisjunctiveCircle) := by
    calc
      (orbit b x n : DisjunctiveCircle) = circleOrbit b x n :=
        (circleOrbit_eq_coe_orbit b x n).symm
      _ = (z : DisjunctiveCircle) := hzcoe.symm
  have hzIco' : z ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using hzIco
  have horbeq : orbit b x n = z :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using orbit_mem_Ico b x n) hzIco').mp hcoeeq
  apply havoid n
  apply (occursAt_iff_orbit_mem b hb x w hw n).2
  change z ∈ openWordCylinder b w at hz
  rw [horbeq]
  exact ⟨hz.1.le, hz.2⟩

/-! ## Hausdorff-cover infrastructure for the missing-word bound -/

/-- A reusable cover criterion tailored to the D3 upper bound.  Finite covers
whose mesh and total `d`-cost both tend to zero force Hausdorff dimension at
most `d`; if `d < 1`, the dimension is strictly below one. -/
theorem dimH_lt_one_of_finite_covers {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (s : Set X) (d : ℝ≥0) (hd : d < 1)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (r : ℕ → ℝ≥0∞) (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (t : ∀ n, ι n → Set X)
    (ht : ∀ᶠ n in Filter.atTop, ∀ i, Metric.ediam (t n i) ≤ r n)
    (hst : ∀ᶠ n in Filter.atTop, s ⊆ ⋃ i, t n i)
    (hcost : Filter.Tendsto
      (fun n => ∑ i, Metric.ediam (t n i) ^ (d : ℝ))
      Filter.atTop (nhds 0)) :
    dimH s < 1 := by
  have hmeasure_le := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
    (d : ℝ) s r hr t ht hst
  have hliminf : Filter.liminf
      (fun n => ∑ i, Metric.ediam (t n i) ^ (d : ℝ)) Filter.atTop = 0 :=
    hcost.liminf_eq
  have hmeasure_zero : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) s = 0 := by
    apply le_antisymm
    · exact hmeasure_le.trans_eq hliminf
    · exact bot_le
  calc
    dimH s ≤ (d : ℝ≥0∞) :=
      dimH_le_of_hausdorffMeasure_ne_top (by simp [hmeasure_zero])
    _ < 1 := by exact_mod_cast hd

/-- The elementary entropy exponent produced by grouping digits into blocks
of length `L`: one of the `b^L` blocks is forbidden. -/
noncomputable def missingWordExponent (b L : ℕ) : ℝ :=
  Real.log (b ^ L - 1 : ℕ) / Real.log (b ^ L : ℕ)

/-- The aligned-block cover has a genuine exponent gap below one. -/
theorem missingWordExponent_lt_one {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) :
    missingWordExponent b L < 1 := by
  have hpow : 2 ≤ b ^ L := hb.trans (Nat.le_self_pow (by omega) b)
  have hsubpos : 0 < b ^ L - 1 := by omega
  have hsub_lt : b ^ L - 1 < b ^ L := by omega
  have hlog_lt : Real.log (b ^ L - 1 : ℕ) < Real.log (b ^ L : ℕ) := by
    apply Real.log_lt_log
    · exact_mod_cast hsubpos
    · exact_mod_cast hsub_lt
  have hlog_pos : 0 < Real.log (b ^ L : ℕ) := by
    apply Real.log_pos
    exact_mod_cast hpow
  exact (div_lt_one hlog_pos).2 hlog_lt

/-- The genuine geometric obligation in D3: every subshift obtained by
forbidding one nonempty valid base-`b` word has Hausdorff dimension below one.
This is the graph-directed self-similar/SFT entropy theorem still to prove. -/
def MissingWordSubshiftDimensionBound (b : ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    dimH (circleMissingWordSubshift b w) < 1

/-- **Axiom `M_b`**, encoded as a named hypothesis rather than a Lean axiom:
no quadratic irrational lies in a closed multiply-by-`b`-forward-invariant
circle set of Hausdorff dimension strictly below one. -/
def QuadraticHypothesisM (b : ℕ) : Prop :=
  ∀ x : ℝ, IsQuadraticIrrational x →
    ∀ K : Set DisjunctiveCircle, IsClosed K → MapsTo (circleMap b) K K →
      (x : DisjunctiveCircle) ∈ K → dimH K < 1 → False

/-- The exact D3 dynamical assembly: `M_b` implies base-`b` disjunctivity of
every quadratic irrational once the independent missing-word SFT dimension
bound is supplied. -/
theorem quadratic_irrationals_disjunctive_of_hypothesisM_of_missingWordDimension
    (b : ℕ) (hb : 2 ≤ b) (hM : QuadraticHypothesisM b)
    (hdim : MissingWordSubshiftDimensionBound b) :
    ∀ x : ℝ, IsQuadraticIrrational x → IsDisjunctive b x := by
  intro x hx
  by_contra hnot
  have hwords : ¬ ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ n, OccursAt b x w n :=
    mt (isDisjunctive_iff_forall_occursAt b hb x).2 hnot
  simp only [not_forall] at hwords
  obtain ⟨w, hw⟩ := hwords
  obtain ⟨hwvalid, hno⟩ := hw
  have havoid : ∀ n, ¬ OccursAt b x w n := not_exists.mp hno
  have hwne : w ≠ [] := by
    intro hw0
    subst w
    exact havoid 0 (by simp [OccursAt])
  exact hM x hx (circleMissingWordSubshift b w)
    (isClosed_circleMissingWordSubshift b w)
    (mapsTo_circleMap_circleMissingWordSubshift b w)
    (mem_circleMissingWordSubshift_of_not_occursAt hb hwvalid havoid)
    (hdim w hwne hwvalid)

end NormalNumbers
