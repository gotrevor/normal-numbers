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

/-- The aligned-block entropy exponent is nonnegative. -/
theorem missingWordExponent_nonneg {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) :
    0 ≤ missingWordExponent b L := by
  have hpow : 2 ≤ b ^ L := hb.trans (Nat.le_self_pow (by omega) b)
  have hsub : 1 ≤ b ^ L - 1 := by omega
  have hnum : 0 ≤ Real.log (b ^ L - 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast hsub)
  have hden : 0 < Real.log (b ^ L : ℕ) :=
    Real.log_pos (by exact_mod_cast hpow)
  exact div_nonneg hnum hden.le

/-! ### The aligned missing-word prefix alphabet

At scale `q * |w|`, the nonexceptional cylinders are indexed by `q`
successive blocks, each chosen from the `b ^ |w| - 1` blocks other than
`w`.  Keeping this as a product of one-block subtypes makes the exact
cardinality a direct `Fintype` calculation; `alignedPrefixWord` flattens an
index back to the ordinary big-endian digit list used by `blockNatVal`.
-/

/-- The valid word `w`, regarded as a `Fin w.length → Fin b` digit block. -/
def wordBlockDigits (b : ℕ) (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    Fin w.length → Fin b := fun i =>
  ⟨w[i], hw w[i] (List.getElem_mem i.isLt)⟩

/-- The one-block alphabet with the single block `w` removed. -/
def AllowedWordBlock (b : ℕ) (w : List ℕ) (hw : ∀ d ∈ w, d < b) :=
  {u : Fin w.length → Fin b // u ≠ wordBlockDigits b w hw}

noncomputable instance instFintypeAllowedWordBlock (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) : Fintype (AllowedWordBlock b w hw) :=
  by
    classical
    exact Subtype.fintype _

/-- An aligned length-`q * |w|` prefix all of whose `|w|`-blocks differ
from `w`. -/
def AlignedMissingWordPrefix (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) (q : ℕ) :=
  Fin q → AllowedWordBlock b w hw

noncomputable instance instFintypeAlignedMissingWordPrefix (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) (q : ℕ) :
    Fintype (AlignedMissingWordPrefix b w hw q) := by
  unfold AlignedMissingWordPrefix
  infer_instance

theorem card_allowedWordBlock (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) :
    Fintype.card (AllowedWordBlock b w hw) = b ^ w.length - 1 := by
  change Fintype.card {u : Fin w.length → Fin b //
    u ≠ wordBlockDigits b w hw} = _
  calc
    Fintype.card {u : Fin w.length → Fin b //
        u ≠ wordBlockDigits b w hw} =
        Fintype.card (Fin w.length → Fin b) - 1 :=
      Set.card_ne_eq (wordBlockDigits b w hw)
    _ = b ^ w.length - 1 := by simp

/-- There are exactly `(b^|w| - 1)^q` aligned prefixes avoiding `w` in
every aligned block. -/
theorem card_alignedMissingWordPrefix (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) (q : ℕ) :
    Fintype.card (AlignedMissingWordPrefix b w hw q) =
      (b ^ w.length - 1) ^ q := by
  simp [AlignedMissingWordPrefix, card_allowedWordBlock]

/-- Flatten an aligned prefix into its ordinary base-`b` digit word. -/
def alignedPrefixWord {b : ℕ} {w : List ℕ} {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (p : AlignedMissingWordPrefix b w hw q) : List ℕ :=
  List.ofFn fun i : Fin (q * w.length) =>
    let jk := finProdFinEquiv.symm i
    ((p jk.1).1 jk.2 : Fin b).val

@[simp] theorem length_alignedPrefixWord {b : ℕ} {w : List ℕ}
    {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (p : AlignedMissingWordPrefix b w hw q) :
    (alignedPrefixWord p).length = q * w.length := by
  simp [alignedPrefixWord]

theorem alignedPrefixWord_digits_lt {b : ℕ} {w : List ℕ}
    {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (p : AlignedMissingWordPrefix b w hw q) :
    ∀ d ∈ alignedPrefixWord p, d < b := by
  intro d hd
  rw [alignedPrefixWord, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  exact ((p (finProdFinEquiv.symm i).1).1 (finProdFinEquiv.symm i).2).isLt

/-- Each aligned block of the flattened prefix really differs from `w`.
The index is written through `finProdFinEquiv` so this lemma is insensitive
to arithmetic reassociation of `j * |w| + k`. -/
theorem alignedPrefixWord_block_ne {b : ℕ} {w : List ℕ}
    {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (p : AlignedMissingWordPrefix b w hw q) (j : Fin q) :
    ∃ k : Fin w.length,
      (alignedPrefixWord p)[(finProdFinEquiv (j, k)).val] ≠ w[k] := by
  by_contra h
  have h : ∀ k : Fin w.length,
      (alignedPrefixWord p)[(finProdFinEquiv (j, k)).val] = w[k] := by
    simpa only [not_exists, not_not] using h
  apply (p j).property
  funext k
  apply Fin.ext
  have hk := h k
  simp only [alignedPrefixWord, List.getElem_ofFn] at hk
  let i : Fin (q * w.length) := finProdFinEquiv (j, k)
  change ((p i.divNat).1 i.modNat).val = w[k] at hk
  have hinv : finProdFinEquiv.symm (finProdFinEquiv (j, k)) = (j, k) :=
    Equiv.symm_apply_apply finProdFinEquiv (j, k)
  have hdiv : i.divNat = j := by
    unfold i
    exact congrArg Prod.fst hinv
  have hmod : i.modNat = k := by
    unfold i
    exact congrArg Prod.snd hinv
  rw [hdiv, hmod] at hk
  simpa [wordBlockDigits] using hk

/-! ### Closed circle cylinders and their mesh -/

/-- The quotient map `ℝ → ℝ ⧸ ℤ` does not increase distances. -/
theorem lipschitzWith_coe_disjunctiveCircle :
    LipschitzWith 1 ((↑) : ℝ → DisjunctiveCircle) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, Real.dist_eq]
  simpa [abs_sub_comm] using
    (QuotientAddGroup.norm_mk_le_norm (M := ℝ)
      (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x - y))

/-- A closed b-adic cylinder on the circle.  Closed endpoints deliberately
absorb the usual two-expansion ambiguity. -/
def circleClosedWordCylinder (b : ℕ) (u : List ℕ) : Set DisjunctiveCircle :=
  ((↑) : ℝ → DisjunctiveCircle) ''
    Set.Icc ((blockNatVal b u : ℝ) / (b : ℝ) ^ u.length)
      (((blockNatVal b u : ℝ) + 1) / (b : ℝ) ^ u.length)

theorem ediam_circleClosedWordCylinder_le {b : ℕ} (hb : 1 ≤ b) (u : List ℕ) :
    Metric.ediam (circleClosedWordCylinder b u) ≤
      ((b : ℝ≥0∞) ^ u.length)⁻¹ := by
  let a : ℝ := (blockNatVal b u : ℝ) / (b : ℝ) ^ u.length
  let c : ℝ := ((blockNatVal b u : ℝ) + 1) / (b : ℝ) ^ u.length
  have hpow : (0 : ℝ) < (b : ℝ) ^ u.length := by positivity
  calc
    Metric.ediam (circleClosedWordCylinder b u) ≤
        Metric.ediam (Set.Icc a c) := by
      simpa [circleClosedWordCylinder, a, c] using
        lipschitzWith_coe_disjunctiveCircle.ediam_image_le (Set.Icc a c)
    _ = ENNReal.ofReal (c - a) := Real.ediam_Icc a c
    _ = ((b : ℝ≥0∞) ^ u.length)⁻¹ := by
      have hca : c - a = ((b : ℝ) ^ u.length)⁻¹ := by
        dsimp [a, c]
        field_simp
        ring
      rw [hca, ENNReal.ofReal_inv_of_pos hpow]
      simp [ENNReal.ofReal_pow]

/-- The closed cylinder indexed by an aligned missing-word prefix. -/
def circleAlignedPrefixCylinder {b : ℕ} {w : List ℕ}
    {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (p : AlignedMissingWordPrefix b w hw q) : Set DisjunctiveCircle :=
  circleClosedWordCylinder b (alignedPrefixWord p)

theorem ediam_circleAlignedPrefixCylinder_le {b : ℕ} (hb : 1 ≤ b)
    {w : List ℕ} {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (p : AlignedMissingWordPrefix b w hw q) :
    Metric.ediam (circleAlignedPrefixCylinder p) ≤
      ((b : ℝ≥0∞) ^ (q * w.length))⁻¹ := by
  simpa [circleAlignedPrefixCylinder] using
    ediam_circleClosedWordCylinder_le hb (alignedPrefixWord p)

/-! ### The nonendpoint part of the cover -/

/-- An occurrence which nevertheless avoids the corresponding open circle
cylinder must sit at its lower endpoint.  This is the precise source of the
b-adic singleton exception in the final cover. -/
theorem orbit_eq_wordCylinder_left_of_occursAt_of_not_mem_open
    {b : ℕ} (hb : 2 ≤ b) {x : ℝ} {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) {n : ℕ} (hocc : OccursAt b x w n)
    (hnot : circleFlow b n (x : DisjunctiveCircle) ∉
      circleOpenWordCylinder b w) :
    orbit b x n = (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length := by
  have hcell := (occursAt_iff_orbit_mem b hb x w hw n).1 hocc
  apply le_antisymm
  · by_contra hle
    have hlo : (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length < orbit b x n :=
      lt_of_not_ge hle
    apply hnot
    refine ⟨orbit b x n, ⟨hlo, hcell.2⟩, ?_⟩
    simpa [circleOrbit] using (circleOrbit_eq_coe_orbit b x n).symm
  · exact hcell.1

/-- Away from aligned hits on the lower open-cylinder boundary, a point in
the missing-word subshift belongs to one of the aligned prefix cylinders.
The remaining branch will be covered by b-adic grid singletons. -/
theorem exists_mem_circleAlignedPrefixCylinder_of_avoids_boundary
    {b : ℕ} (hb : 2 ≤ b) {x : ℝ} {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) {q : ℕ}
    (hsub : (x : DisjunctiveCircle) ∈ circleMissingWordSubshift b w)
    (hboundary : ∀ j : Fin q,
      orbit b x (j.val * w.length) ≠
        (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length) :
    ∃ p : AlignedMissingWordPrefix b w hw q,
      (x : DisjunctiveCircle) ∈ circleAlignedPrefixCylinder p := by
  let block (j : Fin q) : Fin w.length → Fin b := fun k =>
    ⟨digitOf b (Int.fract x) (j.val * w.length + k.val),
      digitOf_lt b hb (Int.fract x) _⟩
  have hblock (j : Fin q) : block j ≠ wordBlockDigits b w hw := by
    intro heq
    have hocc : OccursAt b x w (j.val * w.length) := by
      intro k hk
      let k' : Fin w.length := ⟨k, hk⟩
      have hval := congrArg (fun f => (f k').val) heq
      simpa [block, wordBlockDigits, k'] using hval
    have hlower := orbit_eq_wordCylinder_left_of_occursAt_of_not_mem_open
      hb hw hocc (hsub (j.val * w.length))
    exact hboundary j hlower
  let p : AlignedMissingWordPrefix b w hw q := fun j => ⟨block j, hblock j⟩
  refine ⟨p, ?_⟩
  have hdigits : ∀ i (hi : i < (alignedPrefixWord p).length),
      digitOf b (Int.fract x) i = (alignedPrefixWord p)[i] := by
    intro i hi
    let i' : Fin (q * w.length) :=
      ⟨i, by simpa using hi⟩
    let jk : Fin q × Fin w.length := finProdFinEquiv.symm i'
    have hindex : jk.1.val * w.length + jk.2.val = i := by
      have happly : finProdFinEquiv jk = i' := by
        exact Equiv.apply_symm_apply finProdFinEquiv i'
      have hval := congrArg Fin.val happly
      change jk.2.val + w.length * jk.1.val = i at hval
      calc
        jk.1.val * w.length + jk.2.val =
            jk.2.val + w.length * jk.1.val := by ac_rfl
        _ = i := hval
    rw [show (alignedPrefixWord p)[i] =
        ((p jk.1).1 jk.2).val by
      simp only [alignedPrefixWord, List.getElem_ofFn]
      congr 2]
    simp only [p, block]
    rw [hindex]
  have hfract : Int.fract x ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hprefix := (digits_prefix_iff b hb (Int.fract x) hfract
    (alignedPrefixWord p) (alignedPrefixWord_digits_lt p)).1 hdigits
  refine ⟨Int.fract x, ?_, AddCircle.coe_fract x⟩
  exact ⟨hprefix.1, hprefix.2.le⟩

/-! ### B-adic boundary singletons and the full finite cover -/

/-- The depth-`qL` b-adic grid point with numerator `m`. -/
noncomputable def circleBadicGridPoint (b L q : ℕ) (m : Fin (b ^ (q * L))) :
    DisjunctiveCircle :=
  (((m.val : ℝ) / (b : ℝ) ^ (q * L) : ℝ) : DisjunctiveCircle)

/-- An aligned hit on the lower endpoint is a b-adic grid point at every
later aligned depth. -/
theorem eq_circleBadicGridPoint_of_orbit_eq_wordCylinder_left
    {b : ℕ} (hb : 2 ≤ b) {x : ℝ} {w : List ℕ} {q : ℕ} (j : Fin q)
    (horbit : orbit b x (j.val * w.length) =
      (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length) :
    ∃ m : Fin (b ^ (q * w.length)),
      (x : DisjunctiveCircle) = circleBadicGridPoint b w.length q m := by
  let n := j.val * w.length
  have hbpos : 0 < b := by omega
  have hLpow : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
  have hendpoint : (b ^ w.length) •
      (((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length : ℝ) :
        DisjunctiveCircle) = 0 := by
    have hreal : ((b ^ w.length : ℕ) : ℝ) *
        ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length) =
        (blockNatVal b w : ℝ) := by
      push_cast
      field_simp
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, hreal]
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨(blockNatVal b w : ℤ), by simp [zsmul_eq_mul]⟩
  have horbit_circle : circleFlow b n (x : DisjunctiveCircle) =
      (((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length : ℝ) :
        DisjunctiveCircle) := by
    calc
      circleFlow b n (x : DisjunctiveCircle) = circleOrbit b x n := rfl
      _ = (orbit b x n : DisjunctiveCircle) := circleOrbit_eq_coe_orbit b x n
      _ = (((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length : ℝ) :
          DisjunctiveCircle) := by
        simpa [n] using congrArg (fun z : ℝ => (z : DisjunctiveCircle)) horbit
  have hsmall : (b ^ (n + w.length)) • (x : DisjunctiveCircle) = 0 := by
    calc
      (b ^ (n + w.length)) • (x : DisjunctiveCircle) =
          (b ^ w.length * b ^ n) • (x : DisjunctiveCircle) := by
            rw [pow_add, mul_comm]
      _ = (b ^ w.length) • ((b ^ n) • (x : DisjunctiveCircle)) := by
            rw [smul_smul]
      _ = (b ^ w.length) • circleFlow b n (x : DisjunctiveCircle) := by
            rw [circleFlow_apply]
      _ = (b ^ w.length) •
          (((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length : ℝ) :
            DisjunctiveCircle) := by rw [horbit_circle]
      _ = 0 := hendpoint
  have hnle : n + w.length ≤ q * w.length := by
    dsimp [n]
    have hj : j.val + 1 ≤ q := j.isLt
    nlinarith
  have hbig : (b ^ (q * w.length)) • (x : DisjunctiveCircle) = 0 := by
    have hexp : q * w.length =
        (q * w.length - (n + w.length)) + (n + w.length) := by omega
    have hpowe : b ^ (q * w.length) =
        b ^ (q * w.length - (n + w.length)) * b ^ (n + w.length) := by
      rw [← pow_add, Nat.sub_add_cancel hnle]
    calc
      (b ^ (q * w.length)) • (x : DisjunctiveCircle) =
          (b ^ (q * w.length - (n + w.length)) *
            b ^ (n + w.length)) • (x : DisjunctiveCircle) := by
              rw [hpowe]
      _ = (b ^ (q * w.length - (n + w.length))) •
          ((b ^ (n + w.length)) • (x : DisjunctiveCircle)) := by
            rw [smul_smul]
      _ = 0 := by rw [hsmall, smul_zero]
  have hNpos : 0 < b ^ (q * w.length) := pow_pos hbpos _
  obtain ⟨m, hm, heq⟩ :=
    (AddCircle.nsmul_eq_zero_iff (p := (1 : ℝ)) hNpos).mp hbig
  refine ⟨⟨m, hm⟩, ?_⟩
  simpa [circleBadicGridPoint] using heq.symm

/-- The finite endpoint-safe cover index at aligned depth `q`: ordinary
missing-word prefixes plus all b-adic grid singletons. -/
def MissingWordCoverIndex (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) (q : ℕ) :=
  AlignedMissingWordPrefix b w hw q ⊕ Fin (b ^ (q * w.length))

noncomputable instance instFintypeMissingWordCoverIndex (b : ℕ) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) (q : ℕ) :
    Fintype (MissingWordCoverIndex b w hw q) := by
  unfold MissingWordCoverIndex
  infer_instance

/-- The endpoint-safe cover set associated to an index. -/
def missingWordCoverSet {b : ℕ} {w : List ℕ} {hw : ∀ d ∈ w, d < b} {q : ℕ} :
    MissingWordCoverIndex b w hw q → Set DisjunctiveCircle
  | Sum.inl p => circleAlignedPrefixCylinder p
  | Sum.inr m => {circleBadicGridPoint b w.length q m}

theorem ediam_missingWordCoverSet_le {b : ℕ} (hb : 2 ≤ b)
    {w : List ℕ} {hw : ∀ d ∈ w, d < b} {q : ℕ}
    (i : MissingWordCoverIndex b w hw q) :
    Metric.ediam (missingWordCoverSet i) ≤
      ((b : ℝ≥0∞) ^ (q * w.length))⁻¹ := by
  cases i with
  | inl p => exact ediam_circleAlignedPrefixCylinder_le (by omega) p
  | inr m => simp [missingWordCoverSet]

/-- At every aligned depth, the ordinary prefix cylinders together with the
b-adic boundary singletons cover the closed missing-word subshift. -/
theorem circleMissingWordSubshift_subset_iUnion_missingWordCoverSet
    {b : ℕ} (hb : 2 ≤ b) {w : List ℕ} (hw : ∀ d ∈ w, d < b) (q : ℕ) :
    circleMissingWordSubshift b w ⊆
      ⋃ i : MissingWordCoverIndex b w hw q, missingWordCoverSet i := by
  intro y hy
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  by_cases hboundary : ∀ j : Fin q,
      orbit b x (j.val * w.length) ≠
        (blockNatVal b w : ℝ) / (b : ℝ) ^ w.length
  · obtain ⟨p, hp⟩ :=
      exists_mem_circleAlignedPrefixCylinder_of_avoids_boundary hb hw hy hboundary
    exact Set.mem_iUnion.2 ⟨Sum.inl p, hp⟩
  · simp only [not_forall] at hboundary
    obtain ⟨j, hj⟩ := hboundary
    push Not at hj
    obtain ⟨m, hm⟩ :=
      eq_circleBadicGridPoint_of_orbit_eq_wordCylinder_left hb j hj
    apply Set.mem_iUnion.2
    refine ⟨Sum.inr m, ?_⟩
    simpa [missingWordCoverSet] using hm

/-! ### Hausdorff cost of the endpoint-safe cover -/

/-- The `d`-cost of the endpoint-safe cover is bounded by the number of
aligned prefixes times the `d`-power of the common mesh.  The b-adic grid
half contributes zero because every one of its cover sets is a singleton. -/
theorem missingWordCoverCost_le {b : ℕ} (hb : 2 ≤ b)
    {w : List ℕ} (hw : ∀ a ∈ w, a < b) (d : ℝ≥0) (hd : 0 < d) (q : ℕ) :
    (∑ i : MissingWordCoverIndex b w hw q,
        Metric.ediam (missingWordCoverSet i) ^ (d : ℝ)) ≤
      ((b ^ w.length - 1 : ℕ) : ℝ≥0∞) ^ q *
        (((b : ℝ≥0∞) ^ (q * w.length))⁻¹ ^ (d : ℝ)) := by
  change (∑ i : (AlignedMissingWordPrefix b w hw q ⊕
      Fin (b ^ (q * w.length))),
      Metric.ediam (missingWordCoverSet i) ^ (d : ℝ)) ≤ _
  rw [Fintype.sum_sum_type]
  have hright :
      (∑ m : Fin (b ^ (q * w.length)),
        Metric.ediam (missingWordCoverSet (Sum.inr m :
          MissingWordCoverIndex b w hw q)) ^ (d : ℝ)) = 0 := by
    simp [missingWordCoverSet, hd]
  rw [hright, add_zero]
  calc
    (∑ p : AlignedMissingWordPrefix b w hw q,
        Metric.ediam (missingWordCoverSet (Sum.inl p :
          MissingWordCoverIndex b w hw q)) ^ (d : ℝ)) ≤
        ∑ _p : AlignedMissingWordPrefix b w hw q,
          (((b : ℝ≥0∞) ^ (q * w.length))⁻¹ ^ (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact ENNReal.rpow_le_rpow (ediam_missingWordCoverSet_le hb _) d.2
    _ = ((b ^ w.length - 1 : ℕ) : ℝ≥0∞) ^ q *
        (((b : ℝ≥0∞) ^ (q * w.length))⁻¹ ^ (d : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        show Finset.univ.card =
          Fintype.card (AlignedMissingWordPrefix b w hw q) from rfl,
        card_alignedMissingWordPrefix]
      simp

/-- Rewrite the cover-cost majorant as the `q`-th power of one fixed
geometric ratio. -/
theorem missingWordCoverGeometric_eq (b L q : ℕ) (d : ℝ≥0) :
    ((b ^ L - 1 : ℕ) : ℝ≥0∞) ^ q *
        (((b : ℝ≥0∞) ^ (q * L))⁻¹ ^ (d : ℝ)) =
      (((b ^ L - 1 : ℕ) : ℝ≥0∞) *
        ((((b : ℝ≥0∞) ^ L)⁻¹) ^ (d : ℝ))) ^ q := by
  let A : ℝ≥0∞ := ((b ^ L - 1 : ℕ) : ℝ≥0∞)
  let B : ℝ≥0∞ := (b : ℝ≥0∞) ^ L
  have hpowB : (B ^ q) ^ (d : ℝ) = (B ^ (d : ℝ)) ^ q := by
    calc
      (B ^ q) ^ (d : ℝ) = (B ^ (q : ℝ)) ^ (d : ℝ) := by
        rw [ENNReal.rpow_natCast]
      _ = B ^ ((q : ℝ) * (d : ℝ)) := (ENNReal.rpow_mul B _ _).symm
      _ = B ^ ((d : ℝ) * (q : ℝ)) := by rw [mul_comm]
      _ = (B ^ (d : ℝ)) ^ (q : ℝ) := ENNReal.rpow_mul B _ _
      _ = (B ^ (d : ℝ)) ^ q := ENNReal.rpow_natCast _ _
  change A ^ q * ((((b : ℝ≥0∞) ^ (q * L))⁻¹) ^ (d : ℝ)) =
    (A * B⁻¹ ^ (d : ℝ)) ^ q
  rw [show (b : ℝ≥0∞) ^ (q * L) = B ^ q by
    dsimp [B]
    rw [mul_comm q L, pow_mul]]
  rw [ENNReal.inv_rpow, hpowB, ENNReal.inv_pow, ← mul_pow, ENNReal.inv_rpow]

/-- The common b-adic mesh of the aligned covers tends to zero. -/
theorem missingWordMesh_tendsto {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) :
    Tendsto (fun q : ℕ => ((b : ℝ≥0∞) ^ (q * L))⁻¹) atTop (nhds 0) := by
  have hpow : 1 < b ^ L :=
    lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) b)
  have hbase : ((b : ℝ≥0∞) ^ L)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]
    exact_mod_cast hpow
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase
  convert ht using 1
  funext q
  rw [mul_comm q L, pow_mul, ENNReal.inv_pow]

/-- Any exponent strictly above the aligned-block entropy exponent makes the
one-step cover-cost ratio strictly smaller than one. -/
theorem missingWordCostRatio_lt_one {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L)
    (d : ℝ≥0) (hed : missingWordExponent b L < d) :
    (((b ^ L - 1 : ℕ) : ℝ≥0∞) *
      (((b : ℝ≥0∞) ^ L)⁻¹ ^ (d : ℝ))) < 1 := by
  let e := missingWordExponent b L
  have hed' : e < (d : ℝ) := by simpa [e] using hed
  have hpow : 2 ≤ b ^ L := hb.trans (Nat.le_self_pow (by omega) b)
  have hApos : 0 < ((b ^ L - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < b ^ L - 1 by omega)
  have hBpos : 0 < ((b ^ L : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < b ^ L by omega)
  have hlogB : 0 < Real.log (b ^ L : ℕ) :=
    Real.log_pos (by exact_mod_cast hpow)
  have hlog : Real.log (b ^ L - 1 : ℕ) <
      (d : ℝ) * Real.log (b ^ L : ℕ) := by
    rw [show Real.log (b ^ L - 1 : ℕ) = e * Real.log (b ^ L : ℕ) by
      dsimp [e, missingWordExponent]
      field_simp]
    exact mul_lt_mul_of_pos_right hed' hlogB
  have hArpow : ((b ^ L - 1 : ℕ) : ℝ) <
      ((b ^ L : ℕ) : ℝ) ^ (d : ℝ) :=
    (Real.lt_rpow_iff_log_lt hApos hBpos).2 hlog
  have hbase_ne_top : ((b : ℝ≥0∞) ^ L)⁻¹ ≠ ⊤ := by
    apply (ENNReal.inv_ne_top).2
    simp [show b ≠ 0 by omega]
  have hrpow_ne_top : (((b : ℝ≥0∞) ^ L)⁻¹ ^ (d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg d.2 hbase_ne_top
  have hratio_ne_top : ((b ^ L - 1 : ℕ) : ℝ≥0∞) *
      (((b : ℝ≥0∞) ^ L)⁻¹ ^ (d : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hrpow_ne_top
  apply (ENNReal.toReal_lt_toReal hratio_ne_top (by simp)).mp
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  rw [Real.inv_rpow (by positivity : 0 ≤ (b : ℝ) ^ L),
    mul_inv_lt_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
  simpa using hArpow

/-- The genuine geometric obligation in D3: every subshift obtained by
forbidding one nonempty valid base-`b` word has Hausdorff dimension below one.
The theorem immediately below discharges it using the endpoint-safe aligned
cover. -/
def MissingWordSubshiftDimensionBound (b : ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    dimH (circleMissingWordSubshift b w) < 1

/-- Every nonempty valid missing-word subshift has Hausdorff dimension below
one.  Choose an exponent halfway between its strict aligned-block entropy
exponent and one; the cover cost is then dominated by a geometric sequence. -/
theorem missingWordSubshiftDimensionBound (b : ℕ) (hb : 2 ≤ b) :
    MissingWordSubshiftDimensionBound b := by
  intro w hwne hw
  have hL : 1 ≤ w.length :=
    Nat.one_le_iff_ne_zero.2 (by simpa using hwne)
  let e : ℝ := missingWordExponent b w.length
  have he0 : 0 ≤ e := missingWordExponent_nonneg hb hL
  have he1 : e < 1 := missingWordExponent_lt_one hb hL
  let d : ℝ≥0 := ⟨(e + 1) / 2, by linarith⟩
  have hdpos : 0 < d := by
    change 0 < (e + 1) / 2
    linarith
  have hdlt : d < 1 := by
    change (e + 1) / 2 < 1
    linarith
  have hed : missingWordExponent b w.length < d := by
    change e < (e + 1) / 2
    linarith
  let ρ : ℝ≥0∞ := ((b ^ w.length - 1 : ℕ) : ℝ≥0∞) *
    (((b : ℝ≥0∞) ^ w.length)⁻¹ ^ (d : ℝ))
  have hρ : ρ < 1 := missingWordCostRatio_lt_one hb hL d hed
  have hcostBound : ∀ q : ℕ,
      (∑ i : MissingWordCoverIndex b w hw q,
          Metric.ediam (missingWordCoverSet i) ^ (d : ℝ)) ≤ ρ ^ q := by
    intro q
    calc
      (∑ i : MissingWordCoverIndex b w hw q,
          Metric.ediam (missingWordCoverSet i) ^ (d : ℝ)) ≤
          ((b ^ w.length - 1 : ℕ) : ℝ≥0∞) ^ q *
            (((b : ℝ≥0∞) ^ (q * w.length))⁻¹ ^ (d : ℝ)) :=
        missingWordCoverCost_le hb hw d hdpos q
      _ = ρ ^ q := by
        simpa [ρ] using missingWordCoverGeometric_eq b w.length q d
  have hcost : Tendsto
      (fun q => ∑ i : MissingWordCoverIndex b w hw q,
        Metric.ediam (missingWordCoverSet i) ^ (d : ℝ))
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) ?_ ?_
    · exact Filter.Eventually.of_forall fun q => bot_le
    · exact Filter.Eventually.of_forall hcostBound
  exact dimH_lt_one_of_finite_covers
    (circleMissingWordSubshift b w) d hdlt
    (fun q => MissingWordCoverIndex b w hw q)
    (fun q => ((b : ℝ≥0∞) ^ (q * w.length))⁻¹)
    (missingWordMesh_tendsto hb hL)
    (fun _ i => missingWordCoverSet i)
    (Filter.Eventually.of_forall fun q i => ediam_missingWordCoverSet_le hb i)
    (Filter.Eventually.of_forall fun q =>
      circleMissingWordSubshift_subset_iUnion_missingWordCoverSet hb hw q)
    hcost

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

/-- **Exact D3 conclusion.**  Axiom `M_b` alone implies that every quadratic
irrational is disjunctive in base `b`; the independent missing-word subshift
dimension theorem is discharged internally by the endpoint-safe covers above. -/
theorem quadratic_irrationals_disjunctive_of_hypothesisM
    (b : ℕ) (hb : 2 ≤ b) (hM : QuadraticHypothesisM b) :
    ∀ x : ℝ, IsQuadraticIrrational x → IsDisjunctive b x :=
  quadratic_irrationals_disjunctive_of_hypothesisM_of_missingWordDimension
    b hb hM (missingWordSubshiftDimensionBound b hb)

end NormalNumbers
