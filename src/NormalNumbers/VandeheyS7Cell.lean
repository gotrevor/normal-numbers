/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Orbit
import NormalNumbers.GaussKB
import NormalNumbers.CFPin

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
That is `CellCover`, and `cellCover_inv_log_two` proves it.

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

/-! ## The finite cover: the index family -/

/-- Words of length `m` with every entry in `[1,T]`. -/
def wordsFinset : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | (m + 1), T => ((Finset.Icc 1 T) ×ˢ wordsFinset m T).image (fun p => p.1 :: p.2)

lemma mem_wordsFinset {m T : ℕ} {w : List ℕ} :
    w ∈ wordsFinset m T ↔ w.length = m ∧ ∀ e ∈ w, 1 ≤ e ∧ e ≤ T := by
  induction m generalizing w with
  | zero =>
      simp only [wordsFinset, Finset.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩
        exact List.eq_nil_of_length_eq_zero h
  | succ m ih =>
      simp only [wordsFinset, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨c, u⟩, ⟨⟨hc1, hcT⟩, hu⟩, rfl⟩
        obtain ⟨hlen, hpos⟩ := ih.1 hu
        refine ⟨by simp [hlen], fun e he => ?_⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact ⟨hc1, hcT⟩
        · exact hpos e he
      · rintro ⟨hlen, hpos⟩
        cases w with
        | nil => simp at hlen
        | cons c u =>
            refine ⟨(c, u), ⟨⟨(hpos c (by simp)).1, (hpos c (by simp)).2⟩, ?_⟩, rfl⟩
            exact ih.2 ⟨by simpa using hlen, fun e he => hpos e (by simp [he])⟩

lemma wordsFinset_disjoint {m m' T : ℕ} (h : m ≠ m') :
    Disjoint (wordsFinset m T) (wordsFinset m' T) := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  exact h (by rw [← (mem_wordsFinset.1 hw).1, (mem_wordsFinset.1 hw').1])

/-! ## Disjointness and measurability of cells -/

/-- Distinct words of the same length have disjoint cylinders. -/
lemma cfCylinder_disjoint_of_length_eq {w w' : List ℕ} (hlen : w.length = w'.length)
    (hne : w ≠ w') : Disjoint (cfCylinder w) (cfCylinder w') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  refine hne (List.ext_getElem hlen fun i h1 h2 => ?_)
  have e1 := hy.2 i h1
  have e2 := hy'.2 i h2
  rw [List.getD_eq_getElem _ _ h1] at e1
  rw [List.getD_eq_getElem _ _ h2] at e2
  rw [← e1, ← e2]

lemma pairwiseDisjoint_cellSet (m T S : ℕ) :
    (↑(wordsFinset m T) : Set (List ℕ)).PairwiseDisjoint (fun w => cellSet w S) := by
  intro w hw w' hw' hne
  have h1 := (mem_wordsFinset.1 (Finset.mem_coe.1 hw)).1
  have h2 := (mem_wordsFinset.1 (Finset.mem_coe.1 hw')).1
  exact (cfCylinder_disjoint_of_length_eq (by rw [h1, h2]) hne).mono
    (cellSet_subset_cylinder _ _) (cellSet_subset_cylinder _ _)

lemma measurableSet_cellSet (w : List ℕ) (T : ℕ) : MeasurableSet (cellSet w T) := by
  refine (measurableSet_cfCylinder w).inter ?_
  exact measurable_cfDigit w.length measurableSet_Ici

/-! ## The two mass estimates -/

/-- **The tail-cell mass at one level.**  All the level-`m` tail cells together sit inside
`(gaussMapᵐ)⁻¹ (0, 1/T)`, and `γ` is `gaussMap`-invariant, so their total mass is at most
`γ(0, 1/T) ≤ 1/(T log 2)`. -/
lemma sum_gaussMeasure_cellSet_tail_le {m T : ℕ} (hT : 1 ≤ T) :
    ∑ w ∈ wordsFinset m T, gaussMeasure (cellSet w (T + 1))
      ≤ gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) := by
  have hT0 : (0:ℝ) < T := by exact_mod_cast hT
  have hsub : (⋃ w ∈ wordsFinset m T, cellSet w (T + 1))
      ⊆ gaussMap^[m] ⁻¹' Set.Ioo (0:ℝ) (1 / T) := by
    intro y hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨w, hw, hmem⟩ := hy
    have hlen : w.length = m := (mem_wordsFinset.1 hw).1
    have hd : T + 1 ≤ cfDigit y m := by rw [← hlen]; exact hmem.2
    set z : ℝ := gaussMap^[m] y with hz
    have hdz : T + 1 ≤ ⌊z⁻¹⌋₊ := by rw [hz]; simpa [cfDigit] using hd
    have hz0 : 0 ≤ z⁻¹ := by
      by_contra hcon
      push_neg at hcon
      rw [Nat.floor_of_nonpos hcon.le] at hdz
      omega
    have hzT : ((T:ℝ) + 1) ≤ z⁻¹ := by
      have := (Nat.le_floor_iff hz0).1 hdz
      push_cast at this
      linarith
    have hzpos : 0 < z := inv_pos.1 (lt_of_lt_of_le (by linarith) hzT)
    have hinv : z * z⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hzpos)
    refine ⟨hzpos, ?_⟩
    rw [lt_div_iff₀ hT0]
    nlinarith
  calc ∑ w ∈ wordsFinset m T, gaussMeasure (cellSet w (T + 1))
      = gaussMeasure (⋃ w ∈ wordsFinset m T, cellSet w (T + 1)) :=
        (measure_biUnion_finset (pairwiseDisjoint_cellSet m T (T + 1))
          (fun w _ => measurableSet_cellSet w (T + 1))).symm
    _ ≤ gaussMeasure (gaussMap^[m] ⁻¹' Set.Ioo (0:ℝ) (1 / T)) := measure_mono hsub
    _ = gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) := gaussMeasure_preimage_iterate measurableSet_Ioo m

/-- `γ(u,v) ≤ (v − u)/log 2`: the Gauss density is at most `1/log 2`. -/
lemma gaussMeasure_Ioo_toReal_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (gaussMeasure (Set.Ioo u v)).toReal ≤ (v - u) / Real.log 2 := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hu1 : (0:ℝ) < 1 + u := by linarith
  have hv1 : (0:ℝ) < 1 + v := by linarith
  have hlogle : Real.log (1 + v) - Real.log (1 + u) ≤ v - u := by
    have h := Real.log_le_sub_one_of_pos (div_pos hv1 hu1)
    rw [Real.log_div hv1.ne' hu1.ne'] at h
    have heq : (1 + v) / (1 + u) - 1 = (v - u) / (1 + u) := by field_simp; ring
    rw [heq] at h
    have h2 : (v - u) / (1 + u) ≤ v - u := by
      rw [div_le_iff₀ hu1]
      nlinarith
    linarith
  have hmono : Real.log (1 + u) ≤ Real.log (1 + v) := Real.log_le_log hu1 (by linarith)
  rw [gaussMeasure_Ioo hu huv hv,
    ENNReal.toReal_ofReal (div_nonneg (by linarith) hlog.le)]
  gcongr

/-- The depth-`n` words whose cylinder meets `(a,b)`. -/
noncomputable def meetingWords (n T : ℕ) (a b : ℝ) : Finset (List ℕ) := by
  classical
  exact (wordsFinset n T).filter (fun w => (cfCylinder w ∩ Set.Ioo a b).Nonempty)

lemma mem_meetingWords {n T : ℕ} {a b : ℝ} {w : List ℕ} :
    w ∈ meetingWords n T a b ↔
      w ∈ wordsFinset n T ∧ (cfCylinder w ∩ Set.Ioo a b).Nonempty := by
  classical
  unfold meetingWords
  exact Finset.mem_filter

/-- **The depth-`n` cell mass.**  The depth-`n` cylinders that meet `(a,b)` all sit inside a
`2/2ⁿ`-neighbourhood of `(a,b)` and are pairwise disjoint, so their total Gauss mass is at most
that of the neighbourhood. -/
lemma sum_gaussMeasure_cfCylinder_meeting_le {n T : ℕ} (hn : 0 < n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∑ w ∈ meetingWords n T a b, gaussMeasure (cfCylinder w)
      ≤ gaussMeasure (Set.Ioo (max 0 (a - 4 / 2 ^ n)) (min 1 (b + 4 / 2 ^ n))) := by
  classical
  set d : ℝ := 2 / 2 ^ n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  set F₁ := meetingWords n T a b with hF₁
  have hsub : (⋃ w ∈ F₁, cfCylinder w)
      ⊆ Set.Ioo (max 0 (a - 2 * d)) (min 1 (b + 2 * d)) := by
    intro y hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    rw [hF₁, mem_meetingWords] at hw
    obtain ⟨hwmem, t, htc, htab⟩ := hw
    obtain ⟨hlen, hent⟩ := mem_wordsFinset.1 hwmem
    have hwne : w ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have hpos : ∀ e ∈ w, 1 ≤ e := fun e he => (hent e he).1
    obtain ⟨c₁, c₂, hIcc, hlenIcc⟩ := cfCylinder_subset_Icc_length w hwne hpos
    have hvol : c₂ - c₁ ≤ d := by
      rw [hlenIcc, hd, ← hlen]
      exact volume_cfCylinder_le_two_div w hwne hpos
    have hy1 := hIcc hyw
    have ht1 := hIcc htc
    have hy01 : y ∈ Set.Ioo (0:ℝ) 1 := hyw.1
    constructor
    · rcases max_cases (0:ℝ) (a - 2 * d) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he]; exact hy01.1
      · rw [he]
        have := htab.1
        have := hy1.1
        have := hy1.2
        have := ht1.1
        have := ht1.2
        linarith
    · rcases min_cases (1:ℝ) (b + 2 * d) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he]; exact hy01.2
      · rw [he]
        have := htab.2
        have := hy1.1
        have := hy1.2
        have := ht1.1
        have := ht1.2
        linarith
  have hdisj : (↑F₁ : Set (List ℕ)).PairwiseDisjoint cfCylinder := by
    intro w hw w' hw' hne
    have h1 := (mem_wordsFinset.1 (mem_meetingWords.1 (Finset.mem_coe.1 hw)).1).1
    have h2 := (mem_wordsFinset.1 (mem_meetingWords.1 (Finset.mem_coe.1 hw')).1).1
    exact cfCylinder_disjoint_of_length_eq (by rw [h1, h2]) hne
  calc ∑ w ∈ F₁, gaussMeasure (cfCylinder w)
      = gaussMeasure (⋃ w ∈ F₁, cfCylinder w) :=
        (measure_biUnion_finset hdisj (fun w _ => measurableSet_cfCylinder w)).symm
    _ ≤ gaussMeasure (Set.Ioo (max 0 (a - 2 * d)) (min 1 (b + 2 * d))) := measure_mono hsub
    _ = gaussMeasure (Set.Ioo (max 0 (a - 4 / 2 ^ n)) (min 1 (b + 4 / 2 ^ n))) := by
        rw [hd]; norm_num; ring_nf

/-- **The named geometric sub-goal.**  The finite cover exists with `C₀ = 1/log 2`, the sup of the
Gauss density.  Construction: fix `n` and `T` with `2 · 2^{-n} ≤ δ'` and `4/T ≤ δ'`, and take the
finite partition of `(0,1)` generated by "digit `≤ T` or digit `≥ T+1`", refined to depth `n` along
the first alternative: the cells are `cfCylinder w` for `|w| = n` with entries in `[1,T]`, together
with `cellSet w (T+1)` for `|w| < n` with entries in `[1,T]`.  Each cell is an interval of
diameter `≤ δ'` (`cfCylinder_subset_Icc_length` for the first kind, the same bound scaled by
`1/T` for the second), so the cells meeting `(a,b)` all lie inside `(a − δ', b + δ')`; they are
pairwise disjoint, so their Gauss masses sum to at most `γ(a − δ', b + δ') ≤
(b − a + 2δ')/log 2`.

PROVED.  One simplification made it cheap: the tail cells need no diameter bound at all.  Only the
depth-`n` cylinders have to be short (to be trapped in the neighbourhood); the tail cells are
handled by MASS, since all the level-`m` tail cells together sit inside `(gaussMapᵐ)⁻¹(0,1/T)`,
whose `γ`-mass is `γ(0,1/T) ≤ 1/(T log 2)` by invariance of `γ` — no geometry of the Möbius branch
maps, and `n` levels contribute only `n/(T log 2)`.  See `sum_gaussMeasure_cellSet_tail_le`. -/
theorem cellCover_inv_log_two : CellCover (1 / Real.log 2) := by
  classical
  intro a b ha hab hb1 δ hδ
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the depth
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (64 / (δ * Real.log 2))
  set n : ℕ := n₀ + 1 with hn
  have hnpos : 0 < n := Nat.succ_pos _
  have h2n : ((n₀ : ℝ)) < 2 ^ n := by
    have h1 : n₀ < 2 ^ n₀ := Nat.lt_two_pow_self
    have h2 : (2:ℕ) ^ n₀ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (n₀ : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le h1 h2
    simpa using this
  have hpow0 : (0:ℝ) < 2 ^ n := by positivity
  have hdepth : 8 / (2 ^ n * Real.log 2) ≤ δ / 2 := by
    have h64 : 64 / (δ * Real.log 2) < 2 ^ n := lt_trans hn₀ h2n
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    rw [div_lt_iff₀ (by positivity)] at h64
    nlinarith
  -- the threshold
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (8 * n / (δ * Real.log 2))
  set T : ℕ := T₀ + 1 with hT
  have hT1 : 1 ≤ T := Nat.succ_le_succ (Nat.zero_le _)
  have hTR : (0:ℝ) < T := by exact_mod_cast hT1
  have hTgt : 8 * (n:ℝ) / (δ * Real.log 2) < T := by
    have : (T₀ : ℝ) < T := by rw [hT]; push_cast; linarith
    linarith
  have hthresh : (n:ℝ) * (1 / T) / Real.log 2 ≤ δ / 2 := by
    rw [div_lt_iff₀ (by positivity)] at hTgt
    rw [div_le_div_iff₀ hlog (by norm_num : (0:ℝ) < 2)]
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    rw [mul_one_div]
    rw [div_mul_eq_mul_div, div_le_iff₀ hTR]
    nlinarith
  -- the family
  set FA : Finset (List ℕ × ℕ) := (meetingWords n T a b).image (fun w => (w, 1)) with hFA
  set FB : Finset (List ℕ × ℕ) :=
    (Finset.range n).biUnion (fun m => (wordsFinset m T).image (fun w => (w, T + 1))) with hFB
  refine ⟨FA ∪ FB, ?_, ?_, ?_⟩
  · -- every index is a genuine word with a threshold ≥ 1
    intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (hFA ▸ h)
      exact ⟨fun e he => ((mem_wordsFinset.1 (mem_meetingWords.1 hw).1).2 e he).1, le_rfl⟩
    · obtain ⟨m, -, h'⟩ := Finset.mem_biUnion.1 (hFB ▸ h)
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h'
      exact ⟨fun e he => ((mem_wordsFinset.1 hw).2 e he).1, by omega⟩
  · -- the cover
    intro t ht ht01 htab
    by_cases hall : ∀ i < n, cfDigit t i ≤ T
    · refine ⟨(digitWord t n, 1), Finset.mem_union_left _ ?_, ?_⟩
      · refine (hFA ▸ Finset.mem_image.2 ⟨digitWord t n, mem_meetingWords.2 ⟨?_, ?_⟩, rfl⟩)
        · refine mem_wordsFinset.2 ⟨digitWord_length t n, fun e he => ?_⟩
          obtain ⟨i, hi, rfl⟩ : ∃ i < n, cfDigit t i = e := by simpa [digitWord] using he
          exact ⟨one_le_cfDigit t ht ht01 i, hall i hi⟩
        · exact ⟨t, mem_cfCylinder_digitWord ht01 n, htab⟩
      · exact (mem_cellSet_one_iff ht ht01 _).2 (mem_cfCylinder_digitWord ht01 n)
    · push_neg at hall
      have hex : ∃ i, i < n ∧ T < cfDigit t i := by
        obtain ⟨i, hi, hgt⟩ := hall
        exact ⟨i, hi, hgt⟩
      set m : ℕ := Nat.find hex with hm
      obtain ⟨hmn, hmgt⟩ : m < n ∧ T < cfDigit t m := Nat.find_spec hex
      have hmin : ∀ j < m, cfDigit t j ≤ T := by
        intro j hj
        have := Nat.find_min hex (m := j) (by rw [hm] at hj; exact hj)
        by_contra hcon
        exact this ⟨lt_trans hj hmn, not_le.1 hcon⟩
      refine ⟨(digitWord t m, T + 1), Finset.mem_union_right _ ?_, ?_⟩
      · refine (hFB ▸ Finset.mem_biUnion.2 ⟨m, Finset.mem_range.2 hmn, ?_⟩)
        refine Finset.mem_image.2 ⟨digitWord t m, mem_wordsFinset.2 ⟨digitWord_length t m, ?_⟩, rfl⟩
        intro e he
        obtain ⟨i, hi, rfl⟩ : ∃ i < m, cfDigit t i = e := by simpa [digitWord] using he
        exact ⟨one_le_cfDigit t ht ht01 i, hmin i hi⟩
      · refine ⟨mem_cfCylinder_digitWord ht01 m, ?_⟩
        show T + 1 ≤ cfDigit t (digitWord t m).length
        rw [digitWord_length]
        omega
  · -- the mass bound
    set u : ℝ := max 0 (a - 4 / 2 ^ n) with hu
    set v : ℝ := min 1 (b + 4 / 2 ^ n) with hv
    have hd0 : (0:ℝ) < 4 / 2 ^ n := by positivity
    have hu0 : 0 ≤ u := le_max_left _ _
    have huv : u ≤ v := by
      rw [hu, hv]
      refine max_le (le_min zero_le_one (by linarith)) (le_min (by linarith) (by linarith))
    have hv1 : v ≤ 1 := min_le_left _ _
    have hvu : v - u ≤ (b - a) + 8 / 2 ^ n := by
      have h1 : v ≤ b + 4 / 2 ^ n := min_le_right _ _
      have h2 : a - 4 / 2 ^ n ≤ u := le_max_right _ _
      have : (4:ℝ) / 2 ^ n + 4 / 2 ^ n = 8 / 2 ^ n := by ring
      linarith
    -- ENNReal bound
    have hAB : ∑ c ∈ FA ∪ FB, gaussMeasure (cellSet c.1 c.2)
        ≤ (∑ c ∈ FA, gaussMeasure (cellSet c.1 c.2))
          + ∑ c ∈ FB, gaussMeasure (cellSet c.1 c.2) := by
      have h := Finset.sum_union_inter (s₁ := FA) (s₂ := FB)
        (f := fun c : List ℕ × ℕ => gaussMeasure (cellSet c.1 c.2))
      calc ∑ c ∈ FA ∪ FB, gaussMeasure (cellSet c.1 c.2)
          ≤ (∑ c ∈ FA ∪ FB, gaussMeasure (cellSet c.1 c.2))
            + ∑ c ∈ FA ∩ FB, gaussMeasure (cellSet c.1 c.2) := le_self_add
        _ = _ := h
    have hinjA : Set.InjOn (fun w : List ℕ => (w, 1)) (meetingWords n T a b) := by
      intro w _ w' _ h
      exact (Prod.ext_iff.mp h).1
    have hA : ∑ c ∈ FA, gaussMeasure (cellSet c.1 c.2) ≤ gaussMeasure (Set.Ioo u v) := by
      rw [hFA, Finset.sum_image hinjA]
      refine le_trans (Finset.sum_le_sum fun w _ =>
        measure_mono (cellSet_subset_cylinder w 1)) ?_
      exact sum_gaussMeasure_cfCylinder_meeting_le hnpos ha hab hb1
    have hdisjB : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
        (fun m => (wordsFinset m T).image (fun w : List ℕ => (w, T + 1))) := by
      intro m _ m' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro c hc hc'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨w', hw', heq⟩ := Finset.mem_image.1 hc'
      have hww : w' = w := (Prod.ext_iff.mp heq).1
      have hl1 := (mem_wordsFinset.1 hw).1
      have hl2 := (mem_wordsFinset.1 hw').1
      rw [hww] at hl2
      exact hne (by rw [← hl1, hl2])
    have hB : ∑ c ∈ FB, gaussMeasure (cellSet c.1 c.2)
        ≤ n * gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) := by
      rw [hFB, Finset.sum_biUnion hdisjB]
      have hstep : ∀ m ∈ Finset.range n,
          ∑ c ∈ (wordsFinset m T).image (fun w : List ℕ => (w, T + 1)),
              gaussMeasure (cellSet c.1 c.2)
            ≤ gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) := by
        intro m _
        rw [Finset.sum_image (fun w _ w' _ h => (Prod.ext_iff.mp h).1)]
        exact sum_gaussMeasure_cellSet_tail_le hT1
      calc ∑ m ∈ Finset.range n, ∑ c ∈ (wordsFinset m T).image (fun w : List ℕ => (w, T + 1)),
              gaussMeasure (cellSet c.1 c.2)
          ≤ ∑ _m ∈ Finset.range n, gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) :=
            Finset.sum_le_sum hstep
        _ = n * gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hkey : ∑ c ∈ FA ∪ FB, gaussMeasure (cellSet c.1 c.2)
        ≤ gaussMeasure (Set.Ioo u v) + n * gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) :=
      le_trans hAB (add_le_add hA hB)
    have hne1 : gaussMeasure (Set.Ioo u v) ≠ ⊤ := measure_ne_top _ _
    have hne2 : (n : ENNReal) * gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have hneR : gaussMeasure (Set.Ioo u v) + n * gaussMeasure (Set.Ioo (0:ℝ) (1 / T)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hne1, hne2⟩
    have hsumToReal : ∑ c ∈ FA ∪ FB, (gaussMeasure (cellSet c.1 c.2)).toReal
        = (∑ c ∈ FA ∪ FB, gaussMeasure (cellSet c.1 c.2)).toReal :=
      (ENNReal.toReal_sum (fun c _ => measure_ne_top _ _)).symm
    have hTinv : (1:ℝ) / T ≤ 1 := by
      rw [div_le_one hTR]; exact_mod_cast hT1
    calc ∑ c ∈ FA ∪ FB, (gaussMeasure (cellSet c.1 c.2)).toReal
        = (∑ c ∈ FA ∪ FB, gaussMeasure (cellSet c.1 c.2)).toReal := hsumToReal
      _ ≤ (gaussMeasure (Set.Ioo u v) + n * gaussMeasure (Set.Ioo (0:ℝ) (1 / T))).toReal :=
          ENNReal.toReal_mono hneR hkey
      _ = (gaussMeasure (Set.Ioo u v)).toReal
            + n * (gaussMeasure (Set.Ioo (0:ℝ) (1 / T))).toReal := by
          rw [ENNReal.toReal_add hne1 hne2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
      _ ≤ (v - u) / Real.log 2 + n * ((1 / T - 0) / Real.log 2) := by
          have h1 := gaussMeasure_Ioo_toReal_le hu0 huv hv1
          have h2 := gaussMeasure_Ioo_toReal_le (le_refl (0:ℝ)) (by positivity) hTinv
          have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
          have := mul_le_mul_of_nonneg_left h2 hn0
          linarith
      _ ≤ 1 / Real.log 2 * (b - a) + δ := by
          have e1 : (v - u) / Real.log 2
              ≤ ((b - a) + 8 / 2 ^ n) / Real.log 2 := by gcongr
          have e2 : ((b - a) + 8 / 2 ^ n) / Real.log 2
              = 1 / Real.log 2 * (b - a) + 8 / (2 ^ n * Real.log 2) := by
            field_simp
          have e3 : (n:ℝ) * ((1 / T - 0) / Real.log 2) = (n:ℝ) * (1 / T) / Real.log 2 := by
            rw [sub_zero]; ring
          rw [e3]
          have := hdepth
          have := hthresh
          linarith [e1, e2.le, e2.ge]

/-! ## The chain to the frozen target -/

/-- The ergodic route, now resting on a **word-shaped** crux. -/
theorem affineCFN_of_orbitCellBound {q r₀ C C₀ : ℝ} (hC : 0 ≤ C)
    (hcov : CellCover C₀) (hirr : AffineImageIrrational q r₀)
    (hrig : GaussACRigidity (C * C₀)) (hcell : OrbitCellBound q r₀ C) : AffineCFN q r₀ :=
  affineCFN_of_orbitACBound hirr hrig (orbitACBound_of_orbitCellBound hC hcov hirr hcell)

/-- **The ergodic route, with the geometry discharged.**  Only two hypotheses remain: the cited
`GaussACRigidity` and the word-shaped crux `OrbitCellBound`.  (Plus irrationality of the image.) -/
theorem affineCFN_of_orbitCellBound_log {q r₀ C : ℝ} (hC : 0 ≤ C)
    (hirr : AffineImageIrrational q r₀) (hrig : GaussACRigidity (C * (1 / Real.log 2)))
    (hcell : OrbitCellBound q r₀ C) : AffineCFN q r₀ :=
  affineCFN_of_orbitCellBound hC cellCover_inv_log_two hirr hrig hcell

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
#print axioms cellCover_inv_log_two
#print axioms sum_gaussMeasure_cellSet_tail_le
#print axioms sum_gaussMeasure_cfCylinder_meeting_le
#print axioms gaussMeasure_Ioo_toReal_le
#print axioms affineCFN_of_orbitCellBound
#print axioms affineCFN_of_orbitCellBound_log
#print axioms one_le_of_orbitCellBound
#print axioms cellSet_eq_empty_of_not_mem

end Audit

end NormalNumbers.VandeheyS7
