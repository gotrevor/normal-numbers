/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyInfo

/-!
# Gibbs' inequality and generalized entropy subadditivity for `FinLaw`

The entropy expedition proved (`entropy_E1`) that the joint sampled vector `Z^{G₄}_K` carries
almost all of the entropy its alphabet allows.  Turning that into a statement about the
*frequency* of a fixed binary word inside the sampled windows needs exactly two pieces of
finite information theory, and this module supplies the first.

* `FinLaw.map L f` — the pushforward of a law along a map of finite types.
* `FinLaw.gibbs` — **Gibbs' inequality**: for any sub-probability vector `q` whose support
  contains that of `L`,

      `H₂ L ≤ − ∑ ω, L.p ω · log₂ (q ω)`.

  The proof is one application of `log t ≤ t − 1`, pointwise, with the `p ω = 0` atoms handled
  by inspection (no `−log 0` is ever formed).
* `FinLaw.H₂_le_sum_H₂_map` — **generalized subadditivity**: if a family of coordinate maps
  `f : ι → Ω → Ω'` is *jointly injective* (`ω ↦ fun i => f i ω` is injective), then

      `H₂ L ≤ ∑ i, H₂ (L.map (f i))`.

  This is Gibbs at `q ω = ∏ i, (L.map (f i)).p (f i ω)`: joint injectivity is exactly what makes
  `∑_ω q ω ≤ ∑_{v : ι → Ω'} ∏ i, (L.map (f i)).p (v i) = 1`.

Both statements are about an arbitrary `FinLaw`, so they apply verbatim to the empirical law
`jointLaw` of the schedule.  Downstream (`G4EntropyWord`) the coordinates are the `ℓ`-bit
aligned blocks of each sampled window, whose joint injectivity is the statement that a window
is determined by its blocks.
-/

open Finset

namespace NormalNumbers.G4Entropy

namespace FinLaw

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

/-! ### `H₂` in `logb` form -/

/-- The entropy written with `logb` instead of `negMulLog`.  Valid at zero-mass atoms because
`Real.logb 2 0 = 0` and the mass factor kills the term anyway. -/
lemma H₂_eq_neg_sum_logb (L : FinLaw Ω) :
    L.H₂ = - ∑ ω, L.p ω * Real.logb 2 (L.p ω) := by
  rw [FinLaw.H₂]
  rw [eq_comm, neg_eq_iff_eq_neg, ← neg_div, eq_div_iff (Real.log_pos (by norm_num)).ne']
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Real.negMulLog, Real.logb]
  field_simp

/-! ### Gibbs' inequality -/

/-- **Gibbs' inequality.**  For any nonnegative `q` with total mass at most `1` that is positive
wherever `L` is, the entropy of `L` is at most the cross entropy against `q`.

The pointwise step is `p·log(q/p) ≤ p·(q/p − 1) = q − p`, which at `p = 0` reads `0 ≤ q`. -/
theorem gibbs (L : FinLaw Ω) {q : Ω → ℝ} (hq0 : ∀ ω, 0 ≤ q ω)
    (hq1 : ∑ ω, q ω ≤ 1) (hsupp : ∀ ω, 0 < L.p ω → 0 < q ω) :
    L.H₂ ≤ - ∑ ω, L.p ω * Real.logb 2 (q ω) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the pointwise `log t ≤ t − 1` step
  have key : ∀ ω, L.p ω * Real.log (q ω) - L.p ω * Real.log (L.p ω) ≤ q ω - L.p ω := by
    intro ω
    rcases eq_or_lt_of_le (L.nonneg ω) with h | h
    · rw [← h]; simpa using hq0 ω
    · have hqpos := hsupp ω h
      have hle : Real.log (q ω / L.p ω) ≤ q ω / L.p ω - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hqpos.ne' h.ne'] at hle
      have hmul := mul_le_mul_of_nonneg_left hle h.le
      have hfin : L.p ω * (q ω / L.p ω - 1) = q ω - L.p ω := by field_simp
      calc L.p ω * Real.log (q ω) - L.p ω * Real.log (L.p ω)
          = L.p ω * (Real.log (q ω) - Real.log (L.p ω)) := by ring
        _ ≤ L.p ω * (q ω / L.p ω - 1) := hmul
        _ = q ω - L.p ω := hfin
  set A : ℝ := ∑ ω, L.p ω * Real.log (L.p ω) with hA
  set B : ℝ := ∑ ω, L.p ω * Real.log (q ω) with hB
  have hBA : B - A ≤ 0 := by
    have h1 : B - A = ∑ ω, (L.p ω * Real.log (q ω) - L.p ω * Real.log (L.p ω)) := by
      rw [hA, hB, ← Finset.sum_sub_distrib]
    have h2 : ∑ ω, (L.p ω * Real.log (q ω) - L.p ω * Real.log (L.p ω))
        ≤ ∑ ω, (q ω - L.p ω) := Finset.sum_le_sum fun ω _ => key ω
    have h3 : ∑ ω, (q ω - L.p ω) = (∑ ω, q ω) - 1 := by
      rw [Finset.sum_sub_distrib, L.sum_p]
    rw [h1]; linarith [h2, h3.le, h3.ge]
  -- the entropy sum in terms of `A`
  have hrw1 : (∑ ω, Real.negMulLog (L.p ω)) + A = 0 := by
    rw [hA, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [Real.negMulLog]; ring
  -- the cross-entropy sum in terms of `B`
  have hR : (- ∑ ω, L.p ω * Real.logb 2 (q ω)) = (- B) / Real.log 2 := by
    rw [hB, neg_div]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Real.logb]; ring
  rw [FinLaw.H₂, hR, div_le_div_iff_of_pos_right hlog2]
  linarith [hrw1, hBA]

/-! ### Pushforward laws -/

variable [DecidableEq Ω']

/-- The pushforward of a law along a map of finite types. -/
noncomputable def map (L : FinLaw Ω) (f : Ω → Ω') : FinLaw Ω' where
  p ω' := ∑ ω ∈ Finset.univ.filter (fun ω => f ω = ω'), L.p ω
  nonneg _ := Finset.sum_nonneg fun ω _ => L.nonneg ω
  sum_p := by
    rw [Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ Finset.univ) => Finset.mem_univ (f i))]
    exact L.sum_p

@[simp] lemma map_p (L : FinLaw Ω) (f : Ω → Ω') (ω' : Ω') :
    (L.map f).p ω' = ∑ ω ∈ Finset.univ.filter (fun ω => f ω = ω'), L.p ω := rfl

/-- Every atom's mass is at most that of its image. -/
lemma le_map_p (L : FinLaw Ω) (f : Ω → Ω') (ω : Ω) : L.p ω ≤ (L.map f).p (f ω) := by
  rw [map_p]
  refine Finset.single_le_sum (f := L.p) (fun i _ => L.nonneg i) ?_
  simp

/-- **Change of variables**: an expectation of a function of `f ω` is an expectation under the
pushforward. -/
lemma sum_mul_comp (L : FinLaw Ω) (f : Ω → Ω') (g : Ω' → ℝ) :
    ∑ ω, L.p ω * g (f ω) = ∑ ω', (L.map f).p ω' * g ω' := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun i (_ : i ∈ Finset.univ) => Finset.mem_univ (f i)) (fun ω => L.p ω * g (f ω))]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [map_p, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.1 hω).2]

/-! ### Generalized subadditivity -/

/-- **Generalized subadditivity of Shannon entropy.**  If the coordinate maps `f i` jointly
determine the atom, the entropy is at most the sum of the coordinate entropies.

This is Gibbs' inequality at the product of the coordinate marginals; joint injectivity is
exactly what bounds that product's total mass by `1`. -/
theorem H₂_le_sum_H₂_map {ι : Type*} [Fintype ι] (L : FinLaw Ω) (f : ι → Ω → Ω')
    (hinj : Function.Injective (fun ω => fun i => f i ω)) :
    L.H₂ ≤ ∑ i, (L.map (f i)).H₂ := by
  classical
  set q : Ω → ℝ := fun ω => ∏ i, (L.map (f i)).p (f i ω) with hq
  have hq0 : ∀ ω, 0 ≤ q ω := fun ω =>
    Finset.prod_nonneg fun i _ => (L.map (f i)).nonneg _
  -- total mass of `q` is at most one
  have hq1 : ∑ ω, q ω ≤ 1 := by
    set F : (ι → Ω') → ℝ := fun v => ∏ i, (L.map (f i)).p (v i) with hF
    have hFnn : ∀ v : ι → Ω', 0 ≤ F v := fun v =>
      Finset.prod_nonneg fun i _ => (L.map (f i)).nonneg _
    have himg : ∑ v ∈ Finset.univ.image (fun ω => fun i => f i ω), F v = ∑ ω, q ω :=
      Finset.sum_image fun x _ y _ h => hinj h
    have hsub : ∑ v ∈ Finset.univ.image (fun ω => fun i => f i ω), F v ≤ ∑ v, F v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ => hFnn v
    have hfull : ∑ v : ι → Ω', F v = 1 := by
      have := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Ω'))
        (fun i ω' => (L.map (f i)).p ω')
      rw [Fintype.piFinset_univ] at this
      rw [hF, ← this]
      exact Finset.prod_eq_one fun i _ => (L.map (f i)).sum_p
    rw [← himg]
    exact hsub.trans hfull.le
  have hsupp : ∀ ω, 0 < L.p ω → 0 < q ω := by
    intro ω hω
    refine Finset.prod_pos fun i _ => lt_of_lt_of_le hω (le_map_p L (f i) ω)
  have hgibbs := L.gibbs hq0 hq1 hsupp
  refine hgibbs.trans_eq ?_
  -- split the logarithm of the product
  have hsplit : ∀ ω, L.p ω * Real.logb 2 (q ω)
      = ∑ i, L.p ω * Real.logb 2 ((L.map (f i)).p (f i ω)) := by
    intro ω
    rcases eq_or_lt_of_le (L.nonneg ω) with h | h
    · simp [← h]
    · have hne : ∀ i ∈ (Finset.univ : Finset ι), (L.map (f i)).p (f i ω) ≠ 0 := by
        intro i _
        exact (lt_of_lt_of_le h (le_map_p L (f i) ω)).ne'
      rw [← Finset.mul_sum]
      congr 1
      have hqω : q ω = ∏ i, (L.map (f i)).p (f i ω) := rfl
      rw [hqω, Real.logb, Real.log_prod hne, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => rfl
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => hsplit ω, Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(L.map (f i)).H₂_eq_neg_sum_logb]
  congr 1
  exact sum_mul_comp L (f i) (fun ω' => Real.logb 2 ((L.map (f i)).p ω'))

end FinLaw

end NormalNumbers.G4Entropy
