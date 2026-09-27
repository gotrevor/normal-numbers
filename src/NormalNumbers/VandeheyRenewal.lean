/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyMixing

/-!
# The class transition kernel is doubly stochastic

The crux left by `VandeheyCocycle.lean` is that the class cocycle equidistributes.  Since the
class walk is *not* an independent-increment chain (the CF digits are only ψ-mixing), the usual
Markov machinery is unavailable; but two structural facts make the remaining work a pure
contraction estimate with no stationary-vector computation at all.

**Every digit acts bijectively.**  `classStep D · a` is a bijection of `ℙ¹(ℤ/D)`: it sends
`∞ ↦ a`, `0 ↦ ∞`, and `s ↦ a + s⁻¹` injectively on `s ≠ 0` (this is just `GL₂` invertibility,
seen in slope coordinates).  Hence `σ_w` is a bijection for every word `w`.

**Therefore the kernel is doubly stochastic.**  For a fixed length `m`, the word sets
`classWords D m d d'` — the length-`m` genuine words carrying the class from `d` to `d'` —
partition the *whole* set of length-`m` genuine words as `d` varies (each `w` belongs to exactly
one, namely `d = σ_w⁻¹ d'`).  So the column sums of `ν_m(d,d') = γ(classEvent)` all equal the
same total, and the uniform distribution on `ℙ¹(ℤ/D)` is **exactly** stationary, with nothing
to compute.  What remains for the crux is purely a contraction, `ν_m → 1/|X|`.

Everything is phrased through `VandeheyMix.familySetC`, so the class events are *by definition*
countable unions of cylinders: no measurability of `cfDigit` is ever needed, and
`gaussMeasure_familySetC_psi_mixing` applies to them directly.
-/

namespace NormalNumbers

namespace VandeheyRenewal

open MeasureTheory VandeheyAut VandeheyClass VandeheyMix

/-! ## Every digit acts bijectively on the class space -/

variable {D : ℕ}

theorem classStep_injective [Fact (Nat.Prime D)] (a : ℕ) :
    Function.Injective (fun c : ClassSpace D => classStep D c a) := by
  intro u v huv
  simp only at huv
  match u, v with
  | none, none => rfl
  | none, some t =>
    by_cases ht : t = 0
    · rw [ht] at huv; simp at huv
    · rw [classStep_none, classStep_some_of_ne D ht] at huv
      have : (t : ZMod D)⁻¹ = 0 := by
        have := Option.some_injective _ huv
        linear_combination -this
      exact absurd this (inv_ne_zero ht)
  | some s, none =>
    by_cases hs : s = 0
    · rw [hs] at huv; simp at huv
    · rw [classStep_none, classStep_some_of_ne D hs] at huv
      have : (s : ZMod D)⁻¹ = 0 := by
        have := Option.some_injective _ huv
        linear_combination this
      exact absurd this (inv_ne_zero hs)
  | some s, some t =>
    by_cases hs : s = 0 <;> by_cases ht : t = 0
    · rw [hs, ht]
    · rw [hs, classStep_zero, classStep_some_of_ne D ht] at huv; simp at huv
    · rw [ht, classStep_zero, classStep_some_of_ne D hs] at huv; simp at huv
    · rw [classStep_some_of_ne D hs, classStep_some_of_ne D ht] at huv
      have hinv : (s : ZMod D)⁻¹ = (t : ZMod D)⁻¹ := by
        have := Option.some_injective _ huv
        linear_combination this
      rw [inv_inj] at hinv
      rw [hinv]

theorem classStep_bijective [Fact (Nat.Prime D)] (a : ℕ) :
    Function.Bijective (fun c : ClassSpace D => classStep D c a) :=
  Finite.injective_iff_bijective.mp (classStep_injective a)

/-- The class transition of a whole word. -/
def classSigma (D : ℕ) (w : List ℕ) : ClassSpace D → ClassSpace D :=
  fun d => runState (classStep D) d w

@[simp] lemma classSigma_nil (D : ℕ) : classSigma D ([] : List ℕ) = id := rfl

lemma classSigma_cons (D : ℕ) (a : ℕ) (w : List ℕ) (d : ClassSpace D) :
    classSigma D (a :: w) d = classSigma D w (classStep D d a) := rfl

/-- `σ_w` is a bijection for every word: a composition of bijections. -/
theorem classSigma_bijective [Fact (Nat.Prime D)] (w : List ℕ) :
    Function.Bijective (classSigma D w) := by
  induction w with
  | nil => simpa using Function.bijective_id
  | cons a w ih =>
    have : classSigma D (a :: w) = (classSigma D w) ∘ (fun c => classStep D c a) := by
      funext d; exact classSigma_cons D a w d
    rw [this]
    exact Function.Bijective.comp ih (classStep_bijective a)

theorem classSigma_injective [Fact (Nat.Prime D)] (w : List ℕ) :
    Function.Injective (classSigma D w) := (classSigma_bijective w).1

theorem classSigma_surjective [Fact (Nat.Prime D)] (w : List ℕ) :
    Function.Surjective (classSigma D w) := (classSigma_bijective w).2

/-! ## The class events, as countable unions of cylinders -/

/-- The genuine length-`m` words carrying the class from `d` to `d'`. -/
def classWords (D m : ℕ) (d d' : ClassSpace D) : Set (List ℕ) :=
  {w | w.length = m ∧ (∀ a ∈ w, 1 ≤ a) ∧ classSigma D w d = d'}

/-- All genuine length-`m` words. -/
def allWords (m : ℕ) : Set (List ℕ) := {w | w.length = m ∧ ∀ a ∈ w, 1 ≤ a}

lemma classWords_subset (D m : ℕ) (d d' : ClassSpace D) :
    classWords D m d d' ⊆ allWords m := fun w hw => ⟨hw.1, hw.2.1⟩

/-- `List ℕ` is a countable type, so every word set is countable — no work needed. -/
lemma countable_wordSet (S : Set (List ℕ)) : S.Countable := S.to_countable

/-- The class-transition event: the points of `(0,1)` whose first `m` digits carry `d` to `d'`,
presented as a union of cylinders. -/
noncomputable def classEvent (D m : ℕ) (d d' : ClassSpace D) : Set ℝ :=
  familySetC (classWords D m d d')

/-- The event that the first `m` digits are genuine: the union of all length-`m` cylinders. -/
noncomputable def allWordsEvent (m : ℕ) : Set ℝ := familySetC (allWords m)

/-- The transition kernel of the class walk. -/
noncomputable def classKernel (D m : ℕ) (d d' : ClassSpace D) : ℝ :=
  (gaussMeasure (classEvent D m d d')).toReal

lemma classKernel_nonneg (D m : ℕ) (d d' : ClassSpace D) : 0 ≤ classKernel D m d d' :=
  ENNReal.toReal_nonneg

/-! ## The partition, and double stochasticity -/

/-- **The key partition.**  A genuine length-`m` word lies in `classWords D m d d'` for exactly
one `d`, namely `σ_w⁻¹ d'`.  This is where bijectivity of the class action is used. -/
theorem exists_unique_source [Fact (Nat.Prime D)] {m : ℕ} {w : List ℕ} (hw : w ∈ allWords m)
    (d' : ClassSpace D) : ∃! d, w ∈ classWords D m d d' := by
  obtain ⟨d, hd⟩ := classSigma_surjective (D := D) w d'
  refine ⟨d, ⟨hw.1, hw.2, hd⟩, fun e he => ?_⟩
  exact classSigma_injective (D := D) w (he.2.2.trans hd.symm)

/-- The class events for distinct sources are disjoint. -/
theorem classEvent_disjoint [Fact (Nat.Prime D)] {m : ℕ} {d e d' : ClassSpace D}
    (hde : d ≠ e) : Disjoint (classEvent D m d d') (classEvent D m e d') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [classEvent, familySetC, Set.mem_iUnion₂] at hx hx'
  obtain ⟨w, hw, hxw⟩ := hx
  obtain ⟨w', hw', hxw'⟩ := hx'
  by_cases hww : w = w'
  · subst hww
    exact hde (classSigma_injective (D := D) w (hw.2.2.trans hw'.2.2.symm))
  · exact (Set.disjoint_left.mp
      (cfCylinder_disjoint (by rw [hw.1, hw'.1]) hww) hxw) hxw'

/-- The class events over all sources cover the whole length-`m` cylinder family. -/
theorem iUnion_classEvent [Fact (Nat.Prime D)] (m : ℕ) (d' : ClassSpace D) :
    (⋃ d : ClassSpace D, classEvent D m d d') = allWordsEvent m := by
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun d => ?_
    refine Set.iUnion₂_subset fun w hw => ?_
    exact Set.subset_biUnion_of_mem (u := fun w => cfCylinder w) (classWords_subset D m d d' hw)
  · refine Set.iUnion₂_subset fun w hw => ?_
    obtain ⟨d, hd, -⟩ := exists_unique_source (D := D) hw d'
    refine le_trans ?_ (Set.subset_iUnion _ d)
    exact Set.subset_biUnion_of_mem (u := fun w => cfCylinder w) hd

/-- **Double stochasticity.**  Every column of the class kernel sums to the total mass of the
length-`m` cylinders — in particular all columns sum to the *same* value, so the uniform
distribution on `ℙ¹(ℤ/D)` is exactly stationary and never has to be computed. -/
theorem sum_classKernel_col [Fact (Nat.Prime D)] (m : ℕ) (d' : ClassSpace D) :
    ∑ d : ClassSpace D, classKernel D m d d' = (gaussMeasure (allWordsEvent m)).toReal := by
  classical
  have hdisj : (↑(Finset.univ : Finset (ClassSpace D)) : Set (ClassSpace D)).PairwiseDisjoint
      (fun d => classEvent D m d d') := fun d _ e _ hde => classEvent_disjoint hde
  have hmeas : ∀ d ∈ (Finset.univ : Finset (ClassSpace D)),
      MeasurableSet (classEvent D m d d') :=
    fun d _ => measurableSet_familySetC (countable_wordSet _)
  have hbi := measure_biUnion_finset hdisj hmeas (μ := gaussMeasure)
  have hcover : (⋃ d ∈ (Finset.univ : Finset (ClassSpace D)), classEvent D m d d')
      = allWordsEvent m := by
    rw [← iUnion_classEvent (D := D) m d']
    simp
  simp only [classKernel]
  rw [← ENNReal.toReal_sum (fun d _ => measure_ne_top _ _), ← hbi, hcover]

end VandeheyRenewal

end NormalNumbers
