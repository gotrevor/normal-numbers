/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.GaussErgodic
import NormalNumbers.CFOrbitFreq

/-!
# Krylov–Bogolyubov without compactness: the empirical CDF along an ultrafilter

Step (iii) of the `VandeheyS7.GaussACRigidity` discharge.  The textbook route takes a weak-∗
limit point of the empirical measures (Prokhorov) and then needs the portmanteau theorem and a
mapping theorem for a.e.-continuous functions, because the Gauss map is discontinuous at every
`1/k`.  That is a great deal of machinery.

This module takes a cheaper route, available **because the hypothesis is a uniform absolute
continuity bound**:

* fix one ultrafilter `𝒰 ≤ atTop` and let `limCDF y t := lim_𝒰 (#{j < p : Tʲy < t} / p)`.  The
  values lie in the compact `[0,1]`, so the limit exists — no Prokhorov;
* the AC bound makes `limCDF` **`C`-Lipschitz**, hence monotone and continuous.  So the limit
  object is a `StieltjesFunction`, its measure `ν` is absolutely continuous, and there are no
  continuity-point caveats anywhere — the portmanteau theorem is not needed;
* `T^{-1}(a,b) ∩ (0,1) = ⋃ₖ (1/(k+b), 1/(k+a))` is an **explicit** countable union of intervals,
  whose tail sits in `(0,1/K)` and so has mass `≤ C/K` uniformly in `p`.  That makes
  `ν(T^{-1}(a,b)) = ν((a,b))` an honest limit interchange, with no mapping theorem;
* then `ν` is an a.c. invariant probability, so `ν = γ` by `eq_gaussMeasure_of_ac_invariant`, and
  since *every* ultrafilter limit is `γ`, the whole sequence converges.

## Status

The Lipschitz limit object and its basic theory are proved here.  The remaining steps are named
`sorry`s, each a self-contained statement (see `PENDING_WORK.md`).
-/

namespace NormalNumbers

open MeasureTheory Filter Topology Set

/-- The empirical CDF of the first `p` Gauss iterates of `y`. -/
noncomputable def empCDF (y : ℝ) (p : ℕ) (t : ℝ) : ℝ := blockCount (Ioo 0 t) p y / p

/-- The uniform absolute-continuity hypothesis on the orbit of `y`, with constant `C`. -/
def OrbitACHyp (y C : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ p : ℕ in atTop, blockCount (Ioo a b) p y / p ≤ C * (b - a) + ε

/-! ## Elementary bounds on `blockCount` -/

lemma blockIndic_nonneg (A : Set ℝ) (x : ℝ) : 0 ≤ blockIndic A x := by
  rw [blockIndic]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma blockIndic_le_one (A : Set ℝ) (x : ℝ) : blockIndic A x ≤ 1 := by
  rw [blockIndic]
  by_cases h : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma blockCount_nonneg (A : Set ℝ) (p : ℕ) (y : ℝ) : 0 ≤ blockCount A p y := by
  rw [blockCount_apply]
  exact Finset.sum_nonneg fun k _ => blockIndic_nonneg A _

lemma blockCount_le_card (A : Set ℝ) (p : ℕ) (y : ℝ) : blockCount A p y ≤ p := by
  rw [blockCount_apply]
  calc ∑ k ∈ Finset.range p, blockIndic A (gaussMap^[k] y)
      ≤ ∑ _k ∈ Finset.range p, (1:ℝ) := Finset.sum_le_sum fun k _ => blockIndic_le_one A _
    _ = p := by simp

lemma blockCount_mono {A B : Set ℝ} (hAB : A ⊆ B) (p : ℕ) (y : ℝ) :
    blockCount A p y ≤ blockCount B p y := by
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [blockIndic, blockIndic]
  by_cases h : gaussMap^[k] y ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hAB h)]
  · rw [Set.indicator_of_notMem h]
    exact blockIndic_nonneg B _

lemma empCDF_mem_Icc (y : ℝ) (p : ℕ) (t : ℝ) : empCDF y p t ∈ Icc (0:ℝ) 1 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [empCDF]
  · have hpR : (0:ℝ) < p := by exact_mod_cast hp
    rw [empCDF]
    refine ⟨div_nonneg (blockCount_nonneg _ _ _) hpR.le, ?_⟩
    rw [div_le_one hpR]
    exact blockCount_le_card _ _ _

lemma empCDF_mono (y : ℝ) (p : ℕ) : Monotone (empCDF y p) := by
  intro s t hst
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [empCDF]
  · have hpR : (0:ℝ) < p := by exact_mod_cast hp
    rw [empCDF, empCDF, div_le_div_iff_of_pos_right hpR]
    exact blockCount_mono (Ioo_subset_Ioo le_rfl hst) p y

/-! ## The ultrafilter limit -/

/-- One fixed ultrafilter refining `atTop`; all limits below are taken along it. -/
noncomputable def orbitUF : Ultrafilter ℕ := Ultrafilter.of atTop

lemma orbitUF_le_atTop : (orbitUF : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop

/-- The limit CDF along the ultrafilter. -/
noncomputable def limCDF (y t : ℝ) : ℝ := limUnder (orbitUF : Filter ℕ) (fun p => empCDF y p t)

lemma tendsto_empCDF_limCDF (y t : ℝ) :
    Tendsto (fun p => empCDF y p t) (orbitUF : Filter ℕ) (nhds (limCDF y t)) := by
  obtain ⟨a, _, ha⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).ultrafilter_le_nhds
    (orbitUF.map (fun p => empCDF y p t))
    (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact Filter.Eventually.of_forall fun p => empCDF_mem_Icc y p t)
  have h : Tendsto (fun p => empCDF y p t) (orbitUF : Filter ℕ) (nhds a) := ha
  rw [limCDF, h.limUnder_eq]
  exact h

lemma limCDF_mem_Icc (y t : ℝ) : limCDF y t ∈ Icc (0:ℝ) 1 :=
  ⟨ge_of_tendsto' (tendsto_empCDF_limCDF y t) (fun p => (empCDF_mem_Icc y p t).1),
    le_of_tendsto' (tendsto_empCDF_limCDF y t) (fun p => (empCDF_mem_Icc y p t).2)⟩

/-! ## The limit CDF is Lipschitz -/

/-- A difference of two initial-segment counts is a count over the gap interval, whenever the gap
interval really absorbs the difference set. -/
lemma empCDF_sub_le {a b a' : ℝ} (y : ℝ) (p : ℕ) (hab : a ≤ b)
    (hsub : ∀ x : ℝ, x ∈ Ioo (0:ℝ) b → x ∉ Ioo (0:ℝ) a → x ∈ Ioo a' b) :
    empCDF y p b - empCDF y p a ≤ blockCount (Ioo a' b) p y / p := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [empCDF]
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  rw [empCDF, empCDF, div_sub_div_same, div_le_div_iff_of_pos_right hpR,
    blockCount_apply, blockCount_apply, blockCount_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  set x := gaussMap^[k] y
  rw [blockIndic, blockIndic, blockIndic]
  by_cases hb : x ∈ Ioo (0:ℝ) b
  · by_cases ha : x ∈ Ioo (0:ℝ) a
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem ha]
      have : (1:ℝ → ℝ) x - (1:ℝ → ℝ) x = 0 := by simp
      rw [this]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    · rw [Set.indicator_of_mem hb, Set.indicator_of_notMem ha,
        Set.indicator_of_mem (hsub x hb ha)]
      simp
  · have ha : x ∉ Ioo (0:ℝ) a := fun hx => hb ⟨hx.1, lt_of_lt_of_le hx.2 hab⟩
    rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem ha, sub_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

@[simp] lemma empCDF_zero (y : ℝ) (p : ℕ) : empCDF y p 0 = 0 := by
  simp [empCDF, blockCount_apply, blockIndic]

@[simp] lemma limCDF_zero (y : ℝ) : limCDF y 0 = 0 :=
  tendsto_nhds_unique (tendsto_empCDF_limCDF y 0) (by simpa using tendsto_const_nhds)

/-- **The limit CDF is `C`-Lipschitz on `[0,1]`**, directly from the absolute-continuity
hypothesis.  This is what replaces Prokhorov + portmanteau: the limit object is continuous by
construction, so no continuity-point caveats arise later. -/
theorem limCDF_sub_le {y C : ℝ} (hC : 0 ≤ C) (hAC : OrbitACHyp y C) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    limCDF y b - limCDF y a ≤ C * (b - a) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a gap interval `(a', b)` with `a' ≤ a`, short enough that `C·(a − a')` is negligible
  obtain ⟨a', ha'0, ha'a, hgap, hsub⟩ :
      ∃ a' : ℝ, 0 ≤ a' ∧ a' ≤ a ∧ C * (a - a') ≤ ε / 2 ∧
        ∀ x : ℝ, x ∈ Ioo (0:ℝ) b → x ∉ Ioo (0:ℝ) a → x ∈ Ioo a' b := by
    rcases eq_or_lt_of_le ha with h0 | h0
    · refine ⟨0, le_rfl, ha, by rw [← h0]; simp; positivity, ?_⟩
      intro x hxb hxa
      exact ⟨hxb.1, hxb.2⟩
    · set δ : ℝ := min a (ε / (2 * (C + 1))) with hδ
      have hδ0 : 0 < δ := lt_min h0 (by positivity)
      have hδa : δ ≤ a := min_le_left _ _
      refine ⟨a - δ, by linarith, by linarith, ?_, ?_⟩
      · have : δ ≤ ε / (2 * (C + 1)) := min_le_right _ _
        have hC1 : (0:ℝ) < C + 1 := by linarith
        have : C * δ ≤ (C + 1) * (ε / (2 * (C + 1))) := by
          apply mul_le_mul (by linarith) this hδ0.le (by linarith)
        calc C * (a - (a - δ)) = C * δ := by ring
          _ ≤ (C + 1) * (ε / (2 * (C + 1))) := this
          _ = ε / 2 := by field_simp
      · intro x hxb hxa
        refine ⟨?_, hxb.2⟩
        have : a ≤ x := by
          by_contra hcon
          exact hxa ⟨hxb.1, lt_of_not_ge hcon⟩
        linarith
  have hev : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ),
      empCDF y p b - empCDF y p a ≤ C * (b - a') + ε / 2 := by
    have h0 : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ),
        blockCount (Ioo a' b) p y / p ≤ C * (b - a') + ε / 2 :=
      orbitUF_le_atTop (hAC a' b ha'0 (ha'a.trans hab) hb (ε/2) (by linarith))
    filter_upwards [h0] with p hp
    exact (empCDF_sub_le y p hab hsub).trans hp
  have hlim : limCDF y b - limCDF y a ≤ C * (b - a') + ε / 2 :=
    le_of_tendsto ((tendsto_empCDF_limCDF y b).sub (tendsto_empCDF_limCDF y a)) hev
  have : C * (b - a') = C * (b - a) + C * (a - a') := by ring
  linarith

lemma empCDF_one {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) {p : ℕ} (hp : 0 < p) :
    empCDF y p 1 = 1 := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  rw [empCDF, blockCount_apply]
  have : ∀ k ∈ Finset.range p, blockIndic (Ioo (0:ℝ) 1) (gaussMap^[k] y) = 1 := by
    intro k _
    rw [blockIndic, Set.indicator_of_mem (horb k)]
    rfl
  rw [Finset.sum_congr rfl this]
  simp [hpR.ne']

/-- The limit CDF is a genuine probability CDF on `[0,1]`: no mass escapes. -/
lemma limCDF_one {y : ℝ} (horb : ∀ k : ℕ, gaussMap^[k] y ∈ Ioo (0:ℝ) 1) : limCDF y 1 = 1 := by
  refine tendsto_nhds_unique (tendsto_empCDF_limCDF y 1) ?_
  have h0 : ∀ᶠ p : ℕ in (orbitUF : Filter ℕ), 0 < p :=
    orbitUF_le_atTop (eventually_gt_atTop 0)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h0] with p hp
  exact (empCDF_one horb hp).symm

lemma limCDF_mono (y : ℝ) : Monotone (limCDF y) := by
  intro s t hst
  exact le_of_tendsto_of_tendsto (tendsto_empCDF_limCDF y s) (tendsto_empCDF_limCDF y t)
    (Eventually.of_forall fun p => empCDF_mono y p hst)

section Audit

#print axioms limCDF_sub_le
#print axioms limCDF_one
#print axioms limCDF_mono

end Audit

end NormalNumbers
