/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelRadicalState
import NormalNumbers.PrimeModelRadicalMoment

/-!
# The graded retained box: one threshold per shift

Lap 5 of `KICKOFF-2026-09-22-multicutoff-lean.md` (Fable §2, Astra §5).  The ungraded theory
(`PrimeModelRadicalTail`, `PrimeModelRadicalState`) retains states whose radical size is at most
a **single** `T` at every shift.  The multicutoff argument needs a **per-shift** threshold
`T : Fin k → ℝ` (shift `j` is sieved to the cutoff `y_j`, so its radical is allowed to be
larger), and correspondingly a per-shift Markov exponent `α : Fin k → ℝ`.

* `retainedBoxG` — `{s : ∀ j, d_j(s) ≤ T j}`;
* `retainedBoxG_card_le` — `#(retainedBoxG) ≤ ∏_j ⌊T j⌋₊` (again independent of `#ι`);
* `radical_box_tailG` — `∑_{s ∉ box} weight ≤ ∑_j exp (A j) / (T j) ^ (α j)`;
* `radical_box_tailG_exp20` — the same with the arithmetic budget discharged at
  `α j = 1 / (2 log (y j))` (`radical_moment_budget`), so no moment hypothesis remains.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.RadicalState

open NormalNumbers.PrimeModel.Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

open scoped Classical in
/-- The **graded** retained box: at shift `j` the radical size is at most `T j`. -/
noncomputable def retainedBoxG (k : ℕ) (p : ι → ℕ) (T : Fin k → ℝ) :
    Finset (ι → Option (Fin k)) :=
  Finset.univ.filter (fun s => ∀ j : Fin k, radSize p j s ≤ T j)

open scoped Classical in
lemma mem_retainedBoxG {p : ι → ℕ} {T : Fin k → ℝ} {s : ι → Option (Fin k)} :
    s ∈ retainedBoxG k p T ↔ ∀ j : Fin k, radSize p j s ≤ T j := by
  simp [retainedBoxG]

/-- **Graded retained-box cardinality**: at most `∏_j ⌊T j⌋₊` states have every radical size
`d_j(s)` below its own threshold.  As in the ungraded case the bound is independent of the
number of primes: the state is determined by its tuple of radical sizes. -/
theorem retainedBoxG_card_le {p : ι → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) {T : Fin k → ℝ} (hT : ∀ j, 1 ≤ T j) :
    ((retainedBoxG k p T).card : ℝ) ≤ ∏ j : Fin k, (Nat.floor (T j) : ℝ) := by
  classical
  have hp1 : ∀ i, 1 ≤ p i := fun i => (hp i).one_lt.le.trans' (by norm_num)
  have himg : (retainedBoxG k p T).image (fun s => fun j : Fin k => natRadSize p j s)
      ⊆ Fintype.piFinset (fun j : Fin k => Finset.Icc 1 (Nat.floor (T j))) := by
    intro f hf
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hf
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    refine ⟨one_le_natRadSize hp1 j s, Nat.le_floor ?_⟩
    rw [natRadSize_cast]
    exact (mem_retainedBoxG.mp hs) j
  have hcard : (retainedBoxG k p T).card ≤ ∏ j : Fin k, Nat.floor (T j) := by
    have h2 := Finset.card_le_card himg
    rw [Finset.card_image_of_injective _ (natRadTuple_injective hp hinj)] at h2
    refine h2.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    simp
  calc ((retainedBoxG k p T).card : ℝ) ≤ ((∏ j : Fin k, Nat.floor (T j) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ∏ j : Fin k, (Nat.floor (T j) : ℝ) := by push_cast; rfl

open scoped Classical in
/-- Union bound over the shifts for the graded box. -/
theorem sum_compl_retainedBoxG_le {p : ι → ℕ} {T : Fin k → ℝ}
    (g : (ι → Option (Fin k)) → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ s ∈ (retainedBoxG k p T)ᶜ, g s
      ≤ ∑ j : Fin k, ∑ s ∈ Finset.univ.filter (fun s => ¬ radSize p j s ≤ T j), g s := by
  classical
  have hpt : ∀ s ∈ (retainedBoxG k p T)ᶜ,
      g s ≤ ∑ j : Fin k, (if ¬ radSize p j s ≤ T j then g s else 0) := by
    intro s hs
    have hs' : ¬ ∀ j : Fin k, radSize p j s ≤ T j := by
      simpa [mem_retainedBoxG] using Finset.mem_compl.mp hs
    obtain ⟨j₀, hj₀⟩ := not_forall.mp hs'
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun j => if ¬ radSize p j s ≤ T j then g s else 0)
        (fun j _ => by by_cases h : ¬ radSize p j s ≤ T j <;> simp [h, hg s])
        (Finset.mem_univ j₀))
    simp [hj₀]
  refine (Finset.sum_le_sum hpt).trans ?_
  have hext : ∑ s ∈ (retainedBoxG k p T)ᶜ,
      ∑ j : Fin k, (if ¬ radSize p j s ≤ T j then g s else 0)
      ≤ ∑ s : ι → Option (Fin k),
          ∑ j : Fin k, (if ¬ radSize p j s ≤ T j then g s else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro s _ _
    exact Finset.sum_nonneg fun j _ => by by_cases h : ¬ radSize p j s ≤ T j <;> simp [h, hg s]
  refine hext.trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]

open scoped Classical in
/-- **The graded retained-box tail**: a per-shift Markov bound, one exponent and one budget
per shift. -/
theorem radical_box_tailG (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ} {T α A : Fin k → ℝ}
    (hkp : ∀ i, k ≤ p i) (hp : ∀ i, 1 ≤ p i) (hT : ∀ j, 1 ≤ T j) (hα : ∀ j, 0 < α j)
    (hA : ∀ j, ∑ i, (((p i : ℝ) ^ (α j) - 1) / (p i : ℝ)) ≤ A j) :
    ∑ s ∈ (retainedBoxG k p T)ᶜ, weight k (primeRecip p) s
      ≤ ∑ j : Fin k, Real.exp (A j) / (T j) ^ (α j) := by
  classical
  have hppos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hp i)
  refine (sum_compl_retainedBoxG_le (p := p) (T := T) _
    (fun s => radical_weight_nonneg_prime hppos hkp s)).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  exact radical_shift_markov hkp hp (lt_of_lt_of_le zero_lt_one (hT j)) (hα j) (hA j) j

open scoped Classical in
/-- **The graded retained-box tail, unconditionally**: at shift `j` the Markov exponent is
`1 / (2 log y_j)` and the arithmetic budget is discharged by `radical_moment_budget`, so the
tail is `∑_j e^{20} / T_j^{1/(2 log y_j)}` with no moment hypothesis. -/
theorem radical_box_tailG_exp20 (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ} {T y : Fin k → ℝ}
    (hinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hkp : ∀ i, k ≤ p i) (hy0 : ∀ j, 0 < y j) (hy : ∀ j, 2 ≤ Real.log (y j))
    (hle : ∀ j, ∀ i, (p i : ℝ) ≤ y j) (hT : ∀ j, 1 ≤ T j) :
    ∑ s ∈ (retainedBoxG k p T)ᶜ, weight k (primeRecip p) s
      ≤ ∑ j : Fin k, Real.exp 20 / (T j) ^ (1 / (2 * Real.log (y j))) := by
  refine radical_box_tailG k hkp (fun i => (hprime i).one_lt.le.trans' (by norm_num)) hT
    (fun j => by have := hy j; positivity) (fun j => ?_)
  exact radical_moment_budget hinj hprime (hy0 j) (hy j) (hle j)

end NormalNumbers.PrimeModel.RadicalState
