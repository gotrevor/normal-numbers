/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SC: `BlockCoupling` is vacuous — and the repair

A defect in this lap's own S7-TD, found by asking whether `BlockCoupling` can be satisfied for free.
**It can** (`blockCoupling_trivial`): take `S n j = univ` when the output slot hits the target and
`∅` when it misses.  Nothing in `BlockCoupling` ties `S n j` to the transducer state, so the
existential `TransducerData` is satisfiable *whenever the crux itself holds* — it is a faithful
restatement of `OrbitWordBound`, not a reduction of it.  `blockAverageBound_trivial_iff` makes that
precise: with the trivial `S`, `BlockAverageBound` unwinds to the clock-tick form of the conclusion.

The decomposition (BD) itself is unaffected — `blockCount_clock_eq` is a true and useful identity,
and `integral_blockHitCount_le` is a true and useful measure bound.  What was wrong was treating the
*bundle* as a hypothesis with content.

## The repair

`StateCoupling` pins the sets: `S n j` must be the actual state pullback
`stateBlockSet (s n) w j = (s n).mob⁻¹(G^{-j} I_w ∩ (0,1)) ∩ (0,1)` for a family of `MobState`s.
That is not satisfiable for free — the sets are determined by `s`, and their `γ`-masses are then
pinned by `MobState.gaussMeasure_preimage_tower_le`.  `orbitWordBound_of_stateData` re-derives the
crux from the repaired bundle, and `StateData` is the honest statement of what the Raney transducer
must supply.

So the lap's headline stands in corrected form: the §7 front is `GaussACRigidity` (cited) +
`ImageTight` + `StateData`, where `StateData`'s only non-bookkeeping component is
`BlockAverageBound` **for the pinned pullback sets** — and *that* is fact (α), because the sets now
carry the `γ`-mass bound that makes the empirical-vs-expected comparison the whole question.
-/
import NormalNumbers.VandeheyS7ConjRow

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-! ## The defect, certified -/

/-- **`BlockCoupling` is satisfiable for free.**  Nothing in it ties `S` to the transducer. -/
theorem blockCoupling_trivial (A : Set ℝ) (x y : ℝ) {N : ℕ → ℕ} (hN0 : N 0 = 0)
    (hs : StrictMono N) :
    BlockCoupling A x y N (fun n j => {_t : ℝ | gaussMap^[N n + j] y ∈ A}) where
  base := hN0
  strictMono := hs
  couple := by
    intro n j _
    exact Iff.rfl

/-- With the trivial `S`, the in-block hit count is just the output-side count, so
`BlockAverageBound` degenerates to the conclusion at the clock ticks. -/
theorem blockHitCount_trivial (A : Set ℝ) (y : ℝ) (N : ℕ → ℕ) (n L : ℕ) (t : ℝ) :
    blockHitCount (fun j => {_t : ℝ | gaussMap^[N n + j] y ∈ A}) L t
      = ∑ j ∈ Finset.range L, blockIndic A (gaussMap^[N n + j] y) := by
  unfold blockHitCount
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold blockIndic
  by_cases h : gaussMap^[N n + j] y ∈ A
  · rw [Set.indicator_of_mem (by exact h), Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem (by exact h), Set.indicator_of_notMem h]

/-- The precise statement of the defect: with the trivial `S`, `BlockAverageBound` *is* the
clock-tick form of the crux's conclusion.  So the S7-TD bundle carried no content. -/
theorem blockAverageBound_trivial_iff {A : Set ℝ} {B : ℝ} {x y : ℝ} {N : ℕ → ℕ}
    (hN0 : N 0 = 0) (hmono : Monotone N) :
    BlockAverageBound B x N (fun n j => {_t : ℝ | gaussMap^[N n + j] y ∈ A})
      ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, blockCount A (N p) y ≤ (B + ε) * N p := by
  unfold BlockAverageBound
  constructor <;> intro h ε hε <;> filter_upwards [h ε hε] with p hp
  · rw [blockCount_eq_sum_blocks A hN0 hmono p y]
    refine le_trans (le_of_eq ?_) hp
    exact Finset.sum_congr rfl fun n _ =>
      (blockHitCount_trivial A y N n (N (n + 1) - N n) (gaussMap^[n] x)).symm
  · refine le_trans (le_of_eq ?_) hp
    rw [blockCount_eq_sum_blocks A hN0 hmono p y]
    exact Finset.sum_congr rfl fun n _ =>
      blockHitCount_trivial A y N n (N (n + 1) - N n) (gaussMap^[n] x)

/-! ## The repair: pin the sets to the states -/

/-- **The repaired coupling.**  `S n j` must be the actual pullback of the `j`-th slot of the block
emitted by the state `s n`.  Unlike `BlockCoupling` this is not satisfiable for free: the sets are
determined by `s`, and their `γ`-masses are pinned by
`MobState.gaussMeasure_preimage_tower_le`. -/
structure StateCoupling (w : List ℕ) (x y : ℝ) (N : ℕ → ℕ) (s : ℕ → MobState) : Prop where
  base : N 0 = 0
  strictMono : StrictMono N
  couple : ∀ n j, j < N (n + 1) - N n →
    (gaussMap^[N n + j] y ∈ cfCylinder w ↔ gaussMap^[n] x ∈ stateBlockSet (s n) w j)

/-- A `StateCoupling` is in particular a `BlockCoupling`, with the sets exposed. -/
theorem StateCoupling.toBlockCoupling {w : List ℕ} {x y : ℝ} {N : ℕ → ℕ} {s : ℕ → MobState}
    (h : StateCoupling w x y N s) :
    BlockCoupling (cfCylinder w) x y N (fun n j => stateBlockSet (s n) w j) where
  base := h.base
  strictMono := h.strictMono
  couple := h.couple

/-- **What the Raney transducer must supply, honestly.**  The sets are pinned to a state family. -/
def StateData (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    ∃ (N : ℕ → ℕ) (s : ℕ → MobState),
      StateCoupling w (Int.fract x) (Int.fract (q * x + r₀)) N s ∧
      Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1) ∧
      BlockAverageBound (C * (gaussMeasure (cfCylinder w)).toReal) (Int.fract x) N
        (fun n j => stateBlockSet (s n) w j)

/-- **S7-SC.**  The repaired bundle still gives the crux. -/
theorem orbitWordBound_of_stateData {q r₀ C : ℝ} (hC : 0 ≤ C)
    (h : StateData q r₀ C) : OrbitWordBound q r₀ C := by
  intro x hx w hw ε hε
  obtain ⟨N, s, hcouple, hratio, hBA⟩ := h x hx w hw
  have hB : 0 ≤ C * (gaussMeasure (cfCylinder w)).toReal :=
    mul_nonneg hC ENNReal.toReal_nonneg
  exact freq_le_of_blockAverage hcouple.toBlockCoupling hratio hB hBA ε hε

/-- **`x ↦ φ·x` from the repaired bundle.** -/
theorem vandeheyS7_mul_phi_of_stateData {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (Real.goldenRatio * x + 0)))
    (hSD : StateData Real.goldenRatio 0 C) : vandeheyS7_mul_phi :=
  vandeheyS7_mul_phi_of_orbitWordBound hC hrig htight (orbitWordBound_of_stateData hC hSD)

/-- **`x ↦ x + φ`, likewise.** -/
theorem vandeheyS7_add_phi_of_stateData {C : ℝ} (hC : 0 ≤ C)
    (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (htight : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ImageTight (Int.fract (1 * x + Real.goldenRatio)))
    (hSD : StateData 1 Real.goldenRatio C) : vandeheyS7_add_phi :=
  vandeheyS7_add_phi_of_orbitWordBound hC hrig htight (orbitWordBound_of_stateData hC hSD)

section Audit

#print axioms blockCoupling_trivial
#print axioms blockAverageBound_trivial_iff
#print axioms orbitWordBound_of_stateData
#print axioms vandeheyS7_mul_phi_of_stateData
#print axioms vandeheyS7_add_phi_of_stateData

end Audit

end NormalNumbers.VandeheyS7
