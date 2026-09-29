/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Orbit
import NormalNumbers.GaussKB

/-!
# The crux, word-shaped: `OrbitACBound` from a bound on *cells*

`VandeheyS7Orbit.affineCFN_of_orbitACBound` reduced §7 Problem 1 to the one-sided
`OrbitACBound q r₀ C`: the image orbit visits every subinterval of `(0,1)` with frequency at most
`C` times its length.  That statement quantifies over **arbitrary intervals**, and nothing in the
repo's transducer layer (`VandeheyS7Word`, `cfCount`, `VandeheyS7Approx`) speaks about intervals:
the whole Vandehey pipeline computes frequencies of **finite words** in the image expansion.  This
module bridges that gap.

## The cell family

The right family is *not* the cylinders alone.  An interval is a countable, never a finite, union
of cylinders, and truncating the union leaves a remainder of small Gauss mass whose visit
frequency is exactly what we are trying to bound — the argument would be circular.  The fix is to
close the family under "the first digit that is large":

`cellSet w T = cfCylinder w ∩ {y | T ≤ cfDigit y w.length}`.

* `T = 1` gives back `cfCylinder w` along irrational points (`mem_cellSet_one_iff`), so every cylinder is a cell;
* `T ≥ 2` gives the **tail cell** "the word `w`, then a digit at least `T`" — an interval of
  diameter `O(diam (cfCylinder w) / T)`, not a finite union of cylinders.

With the tail cells available, `(0,1)` has a *finite* partition into cells at every resolution:
split on `a₁ ≤ T` versus `a₁ ≥ T+1`, recurse on the first alternative down to depth `n`, and stop
on the second.  Every piece is an interval, and all pieces are short once `n` and `T` are large.
That is `CellCover`, and it is the only thing left unproved here.

## What this buys

`orbitACBound_of_orbitCellBound` turns the crux into `OrbitCellBound q r₀ C`:

> for every word `w` and every threshold `T`, the image orbit visits `cellSet w T` with frequency
> at most `C · γ(cellSet w T) + ε`.

This is a statement about the frequency of a **finite word** (and of "word then large digit") in
the continued fraction of `q x + r₀` — precisely the shape the transducer layer produces.  It is
still one-sided, still has an absolute constant, and still never mentions `x`-independence.

## Guard rule

Content locator: `mem_cellSet_one_iff` — the family contains every cylinder, so `OrbitCellBound` really
does subsume the word-frequency upper bounds; `cellSet_nil_subset_Ioc` — the `w = []` tail cell is
the interval `(0, 1/T]`, so the family also contains the small-digit tails that make the cover
finite.  Degenerate cases: `one_le_of_orbitCellBound` — the constant is forced to be `≥ 1` (take
`w = []`, `T = 1`, where the cell is all of `(0,1)`), so a bound with `C < 1` is unattainable
rather than merely strong; `cellSet_mono_threshold` and `cellSet_eq_empty_of_not_mem` pin the two
monotonicity/emptiness conventions.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-! ## The cell family -/

/-- The cell of the word `w` at threshold `T`: the reals of `(0,1)` whose first `w.length` CF
digits spell `w` and whose next digit is at least `T`.  `T = 1` is the plain cylinder. -/
noncomputable def cellSet (w : List ℕ) (T : ℕ) : Set ℝ :=
  cfCylinder w ∩ {y | T ≤ cfDigit y w.length}

lemma cellSet_subset_cylinder (w : List ℕ) (T : ℕ) : cellSet w T ⊆ cfCylinder w :=
  Set.inter_subset_left

/-- **Content locator.**  At threshold `1` the cell is exactly the cylinder along irrational
points: every digit of an irrational of `(0,1)` is `≥ 1`.  (For rationals the orbit hits `0` and
the junk digit `0` breaks the equality, which is why the cells are the right family only along
the irrational orbits the route actually uses.) -/
lemma mem_cellSet_one_iff {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (w : List ℕ) : y ∈ cellSet w 1 ↔ y ∈ cfCylinder w := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact one_le_cfDigit y hy hmem w.length

/-- Raising the threshold shrinks the cell. -/
lemma cellSet_mono_threshold (w : List ℕ) {T T' : ℕ} (h : T ≤ T') :
    cellSet w T' ⊆ cellSet w T :=
  Set.inter_subset_inter_right _ fun _ hy => le_trans h hy

/-- The empty word's cell at threshold `T` is inside the interval `(0, 1/T]` — a genuine small
interval, not a finite union of cylinders.  This is what makes the finite cover possible. -/
lemma cellSet_nil_subset_Ioc {T : ℕ} (hT : 1 ≤ T) :
    cellSet [] T ⊆ Set.Ioc (0:ℝ) (1 / T) := by
  rintro y ⟨hy, hd⟩
  have hy01 : y ∈ Set.Ioo (0:ℝ) 1 := hy.1
  have hT0 : (0:ℝ) < T := by exact_mod_cast hT
  refine ⟨hy01.1, ?_⟩
  have hTd : (T : ℝ) ≤ (cfDigit y 0 : ℝ) := by exact_mod_cast hd
  have hfl : ((cfDigit y 0 : ℕ) : ℝ) ≤ y⁻¹ := by
    rw [cfDigit]
    simpa using Nat.floor_le (le_of_lt (by
      simpa using inv_pos.2 hy01.1 : (0:ℝ) < (gaussMap^[0] y)⁻¹))
  have hTy : (T:ℝ) ≤ y⁻¹ := le_trans hTd hfl
  rw [le_div_iff₀ hT0]
  have hinv : y⁻¹ * y = 1 := inv_mul_cancel₀ (ne_of_gt hy01.1)
  nlinarith [hy01.1]

/-- `cellSet [] 1` is all of `(0,1)`. -/
lemma cellSet_nil_one : cellSet [] 1 = Set.Ioo (0:ℝ) 1 := by
  ext y
  constructor
  · intro h; exact h.1.1
  · intro h
    refine ⟨⟨h, by simp⟩, ?_⟩
    show 1 ≤ cfDigit y 0
    rw [cfDigit, Function.iterate_zero_apply]
    refine Nat.le_floor ?_
    rw [Nat.cast_one, le_inv_comm₀ one_pos h.1]
    simpa using h.2.le

lemma gaussMeasure_cellSet_nil_one : (gaussMeasure (cellSet [] 1)).toReal = 1 := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [cellSet_nil_one, gaussMeasure_Ioo le_rfl zero_le_one le_rfl,
    show (1:ℝ) + 1 = 2 by norm_num, show (1:ℝ) + 0 = 1 by norm_num,
    Real.log_one, sub_zero, div_self hlog.ne', ENNReal.toReal_ofReal zero_le_one]

/-! ## Counting lemmas -/

/-- Monotonicity of the orbit count, needed only along irrational orbit points: the cover may miss
the rationals and the interval endpoints. -/
lemma blockCount_le_of_irrational_subset {y : ℝ} (hy : Irrational y)
    (hmem : y ∈ Set.Ioo (0:ℝ) 1) {A B : Set ℝ}
    (h : ∀ t : ℝ, Irrational t → t ∈ Set.Ioo (0:ℝ) 1 → t ∈ A → t ∈ B) (p : ℕ) :
    blockCount A p y ≤ blockCount B p y := by
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_le_sum fun k _ => ?_
  obtain ⟨hk, hk01⟩ := irrational_orbit y hy hmem k
  rw [blockIndic, blockIndic]
  by_cases hA : gaussMap^[k] y ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (h _ hk hk01 hA)]
  · rw [Set.indicator_of_notMem hA]
    exact blockIndic_nonneg B _

/-- Subadditivity of the orbit count over a finite union. -/
lemma blockCount_biUnion_le {ι : Type*} [DecidableEq ι] (F : Finset ι) (A : ι → Set ℝ)
    (p : ℕ) (y : ℝ) :
    blockCount (⋃ i ∈ F, A i) p y ≤ ∑ i ∈ F, blockCount (A i) p y := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [blockCount_apply, blockIndic]
  | @insert i F hi ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact le_trans (blockCount_union_le _ _ _ _) (by linarith)

/-! ## The two hypotheses -/

/-- **The word-shaped crux.**  The image orbit visits every cell with frequency at most `C` times
its Gauss mass, up to `ε`.  For `T = 1` this is a word-frequency upper bound; for `T ≥ 2` it also
covers "the word `w`, then a large digit". -/
def OrbitCellBound (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ (w : List ℕ) (T : ℕ), (∀ e ∈ w, 1 ≤ e) → 1 ≤ T →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop,
      blockCount (cellSet w T) p (Int.fract (q * x + r₀)) / p
        ≤ C * (gaussMeasure (cellSet w T)).toReal + ε

/-- **The geometric input.**  Every subinterval of `(0,1)` is covered, along irrational points, by
a finite family of cells whose total Gauss mass exceeds `C₀ (b − a)` by at most `δ`. -/
def CellCover (C₀ : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ δ : ℝ, 0 < δ →
    ∃ F : Finset (List ℕ × ℕ),
      (∀ c ∈ F, (∀ e ∈ c.1, 1 ≤ e) ∧ 1 ≤ c.2) ∧
      (∀ t : ℝ, Irrational t → t ∈ Set.Ioo (0:ℝ) 1 → t ∈ Set.Ioo a b →
        ∃ c ∈ F, t ∈ cellSet c.1 c.2) ∧
      ∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal ≤ C₀ * (b - a) + δ

/-! ## The reduction -/

/-- **The bridge.**  A cell bound plus a finite cover gives the interval bound: the crux of the
ergodic route becomes a statement about finite words. -/
theorem orbitACBound_of_orbitCellBound {q r₀ C C₀ : ℝ} (hC : 0 ≤ C)
    (hcov : CellCover C₀) (hirr : AffineImageIrrational q r₀)
    (hcell : OrbitCellBound q r₀ C) : OrbitACBound q r₀ (C * C₀) := by
  classical
  intro x hx a b ha hab hb1 ε hε
  obtain ⟨hfz, hmem⟩ := irrational_fract_mem (hirr x hx)
  set y : ℝ := Int.fract (q * x + r₀) with hy
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨F, hFpos, hFcov, hFsum⟩ := hcov a b ha hab hb1 δ hδ0
  set ε' : ℝ := ε / (2 * (F.card + 1)) with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hall : ∀ᶠ p : ℕ in atTop, ∀ c ∈ F,
      blockCount (cellSet c.1 c.2) p y / p
        ≤ C * (gaussMeasure (cellSet c.1 c.2)).toReal + ε' := by
    rw [Filter.eventually_all_finset]
    intro c hc
    exact hcell x hx c.1 c.2 (hFpos c hc).1 (hFpos c hc).2 ε' hε'0
  filter_upwards [hall, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < p := by exact_mod_cast hp0
  -- step 1: the interval count is at most the union count
  have h1 : blockCount (Set.Ioo a b) p y ≤ blockCount (⋃ c ∈ F, cellSet c.1 c.2) p y := by
    refine blockCount_le_of_irrational_subset hfz hmem (fun t ht ht01 htab => ?_) p
    obtain ⟨c, hc, htc⟩ := hFcov t ht ht01 htab
    exact Set.mem_biUnion hc htc
  -- step 2: subadditivity
  have h2 := blockCount_biUnion_le F (fun c : List ℕ × ℕ => cellSet c.1 c.2) p y
  -- step 3: divide and use the cell bounds
  have hsum := le_trans h1 h2
  have h3 : blockCount (Set.Ioo a b) p y / p
      ≤ ∑ c ∈ F, blockCount (cellSet c.1 c.2) p y / p := by
    rw [← Finset.sum_div]
    gcongr
  have h4 : ∑ c ∈ F, blockCount (cellSet c.1 c.2) p y / p
      ≤ ∑ c ∈ F, (C * (gaussMeasure (cellSet c.1 c.2)).toReal + ε') :=
    Finset.sum_le_sum fun c hc => hp c hc
  have h5 : ∑ c ∈ F, (C * (gaussMeasure (cellSet c.1 c.2)).toReal + ε')
      = C * (∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal) + F.card * ε' := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have h6 : C * (∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal)
      ≤ C * (C₀ * (b - a) + δ) := by
    exact mul_le_mul_of_nonneg_left hFsum hC
  have hCδ : C * δ ≤ ε / 2 := by
    rw [hδ]
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have hcard : (F.card : ℝ) * ε' ≤ ε / 2 := by
    rw [hε', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) F.card, hε.le]
  calc blockCount (Set.Ioo a b) p y / p
      ≤ ∑ c ∈ F, blockCount (cellSet c.1 c.2) p y / p := h3
    _ ≤ ∑ c ∈ F, (C * (gaussMeasure (cellSet c.1 c.2)).toReal + ε') := h4
    _ = C * (∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal) + F.card * ε' := h5
    _ ≤ C * (C₀ * (b - a) + δ) + F.card * ε' := by linarith
    _ = C * C₀ * (b - a) + (C * δ + F.card * ε') := by ring
    _ ≤ C * C₀ * (b - a) + ε := by linarith

/-- **The named geometric sub-goal.**  The finite cover exists with `C₀ = 1/log 2`, the sup of the
Gauss density.  Construction: fix `n` and `T` with `2 · 2^{-n} ≤ δ'` and `4/T ≤ δ'`, and take the
finite partition of `(0,1)` generated by "digit `≤ T` or digit `≥ T+1`", refined to depth `n` along
the first alternative: the cells are `cfCylinder w` for `|w| = n` with entries in `[1,T]`, together
with `cellSet w (T+1)` for `|w| < n` with entries in `[1,T]`.  Each cell is an interval of
diameter `≤ δ'` (`cfCylinder_subset_Icc_length` for the first kind, the same bound scaled by
`1/T` for the second), so the cells meeting `(a,b)` all lie inside `(a − δ', b + δ')`; they are
pairwise disjoint, so their Gauss masses sum to at most `γ(a − δ', b + δ') ≤
(b − a + 2δ')/log 2`.

TODO(crux): prove.  Needs (i) the finite partition as a `Finset (List ℕ × ℕ)` with a membership
lemma, (ii) the diameter bound for tail cells, (iii) additivity of `gaussMeasure` over the
disjoint family.  None of the three is deep; all three are bookkeeping against
`CFCylinder.lean`. -/
theorem cellCover_inv_log_two : CellCover (1 / Real.log 2) := by
  sorry

/-! ## The chain to the frozen target -/

/-- The ergodic route, now resting on a **word-shaped** crux. -/
theorem affineCFN_of_orbitCellBound {q r₀ C C₀ : ℝ} (hC : 0 ≤ C)
    (hcov : CellCover C₀) (hirr : AffineImageIrrational q r₀)
    (hrig : GaussACRigidity (C * C₀)) (hcell : OrbitCellBound q r₀ C) : AffineCFN q r₀ :=
  affineCFN_of_orbitACBound hirr hrig (orbitACBound_of_orbitCellBound hC hcov hirr hcell)

/-! ## Guard rule: degenerate cases -/

/-- **Degenerate case.**  `w = []`, `T = 1` makes the cell all of `(0,1)`, where the frequency is
identically `1`, so `OrbitCellBound C` forces `1 ≤ C`. -/
theorem one_le_of_orbitCellBound {q r₀ C : ℝ} (hirr : AffineImageIrrational q r₀)
    (hcell : OrbitCellBound q r₀ C) (h : ∃ x : ℝ, IsCFNormal (Int.fract x)) : 1 ≤ C := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨hfz, hmem⟩ := irrational_fract_mem (hirr x hx)
  by_contra hC
  push_neg at hC
  set ε : ℝ := (1 - C) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨p, hp, hp1⟩ := ((hcell x hx [] 1 (by simp) le_rfl ε hε0).and
    (eventually_gt_atTop 0)).exists
  have hpr : (0:ℝ) < p := by exact_mod_cast hp1
  rw [gaussMeasure_cellSet_nil_one, cellSet_nil_one,
    blockCount_Ioo_zero_one hfz hmem p, div_self hpr.ne'] at hp
  rw [hε] at hp
  linarith

/-- The cell family is not vacuous in the other direction either: a threshold above every digit of
a point excludes it. -/
theorem cellSet_eq_empty_of_not_mem {w : List ℕ} {T : ℕ} {y : ℝ}
    (hy : cfDigit y w.length < T) : y ∉ cellSet w T :=
  fun hmem => absurd hmem.2 (Nat.not_le.mpr hy)

section Audit

#print axioms mem_cellSet_one_iff
#print axioms gaussMeasure_cellSet_nil_one
#print axioms cellSet_nil_one
#print axioms cellSet_mono_threshold
#print axioms cellSet_nil_subset_Ioc
#print axioms blockCount_le_of_irrational_subset
#print axioms blockCount_biUnion_le
#print axioms orbitACBound_of_orbitCellBound
#print axioms affineCFN_of_orbitCellBound
#print axioms one_le_of_orbitCellBound
#print axioms cellSet_eq_empty_of_not_mem

end Audit

end NormalNumbers.VandeheyS7
