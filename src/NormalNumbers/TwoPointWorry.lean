import NormalNumbers.PairDecoupleTwoPoint

/-!
# Deciding the quantifier worry about `TwoPointWeightedAvg`

`TwoPointWeightedAvg b t` reads

    ∀ ε > 0, ∀ᶠ w, ∀ᶠ N,  π(w)⁻² Σ_{p ≠ q ≤ w} ‖E_{n<N} …‖ < ε.

The worry recorded in `KICKOFF-2026-09-24-twopoint-bet.md` is that, because `w` is quantified
*before* `N`, the average runs over a FIXED finite set of pairs, so the statement ought to be
equivalent to (or no weaker than) per-pair natural-density decorrelation — which is open.

This file settles that.  The quantifier order is `w`, then `N`, then the **average is taken
before the limsup in `N`**.  For a finite pair set the limsup of an average of nonnegative
sequences is *not* controlled from below by the individual limsups: if the near-extremal times
of different pairs are **asynchronous**, every single pair can correlate fully (limsup `= 1`)
while the average still has limsup `≤ π(w)⁻²`, which tends to `0`.

`avgShape_not_imply_pairwise` proves exactly that, at the level of the quantifier shape: there is
a table `G` of pair correlations, with values in `[0,1]`, satisfying the `TwoPointWeightedAvg`
shape verbatim, for which *no* pair decorrelates.  Hence

  **the worry is refuted**: `TwoPointWeightedAvg` does not formally entail natural-density
  two-point Elliott for any pair, not even for one pair, and so is not an equivalent repackaging
  of the open pointwise statement.

What survives of the worry is the honest residue recorded in `avgShape_of_forall_tendsto`: the
pointwise statement *implies* the averaged one, so the averaged leaf is genuinely the weaker of
the two, and the only room a proof has is exactly the asynchrony exploited here.

**Scope of the refutation, stated honestly.**  `badTable` is an arbitrary `[0,1]`-valued table,
not an arithmetic one; the real table `G p q N = ‖E_{n<N} ζ^{ω(pn+1)} conj ζ^{ω(qn+1)} W(n)‖` is
constrained (Cesàro means of a fixed unimodular sequence).  So what is refuted is the *argument*
of the worry — "`w` before `N` makes the average a fixed finite average, hence pointwise" — which
is a purely quantifier-level claim and is false.  Whether the arithmetic table can actually be
asynchronous is the next question, and it is the question a proof of the leaf must answer.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The abstract shape -/

/-- The pair average of an abstract correlation table `G p q N`, normalised exactly as
`twoPointAvgSum` is. -/
noncomputable def avgTable (G : ℕ → ℕ → ℕ → ℝ) (w N : ℕ) : ℝ :=
  (∑ p ∈ primesLe w, ∑ q ∈ primesLe w, if p = q then 0 else G p q N)
    / ((primesLe w).card : ℝ) ^ 2

/-- The quantifier shape of `TwoPointWeightedAvg`, on an abstract table. -/
def AvgShape (G : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, ∀ᶠ N : ℕ in atTop, avgTable G w N < ε

/-- The bet's leaf *is* an instance of the abstract shape. -/
lemma twoPointWeightedAvg_iff_avgShape (b : ℕ) (t : ℝ) :
    TwoPointWeightedAvg b t ↔
      AvgShape (fun p q N =>
        ‖fullMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) N‖) :=
  Iff.rfl

/-! ### The residue of the worry: pointwise ⟹ averaged -/

/-- If every pair decorrelates then the averaged shape holds.  So the averaged leaf is at most as
strong as the pointwise one. -/
theorem avgShape_of_forall_tendsto (G : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ p q : ℕ, Tendsto (fun N => G p q N) atTop (𝓝 0)) : AvgShape G := by
  classical
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop 2] with w _
  have hsum : Tendsto (fun N => ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      if p = q then (0 : ℝ) else G p q N) atTop (𝓝 0) := by
    have hterm : ∀ p ∈ primesLe w, Tendsto (fun N => ∑ q ∈ primesLe w,
        if p = q then (0 : ℝ) else G p q N) atTop (𝓝 0) := by
      intro p _
      have : Tendsto (fun N => ∑ q ∈ primesLe w, if p = q then (0 : ℝ) else G p q N) atTop
          (𝓝 (∑ _q ∈ primesLe w, (0 : ℝ))) := by
        refine tendsto_finsetSum _ fun q _ => ?_
        by_cases hpq : p = q
        · simp [hpq]
        · simpa [hpq] using h p q
      simpa using this
    simpa using tendsto_finsetSum (primesLe w) hterm
  have hdiv := hsum.div_const (((primesLe w).card : ℝ) ^ 2)
  rw [zero_div] at hdiv
  exact (hdiv.eventually (gt_mem_nhds hε)).mono fun N hN => hN

/-! ### The asynchronous table: refuting the worry

At time `N` exactly one pair `(p, q)` is "switched on", namely the one with
`Nat.pair p q = (Nat.unpair N).1`.  Every pair is switched on for arbitrarily large `N`, yet at
each single `N` the double sum is at most `1`. -/

/-- The asynchronous correlation table. -/
noncomputable def badTable (p q N : ℕ) : ℝ :=
  if (Nat.unpair N).1 = Nat.pair p q then 1 else 0

lemma badTable_nonneg (p q N : ℕ) : 0 ≤ badTable p q N := by
  unfold badTable; split <;> norm_num

lemma badTable_le_one (p q N : ℕ) : badTable p q N ≤ 1 := by
  unfold badTable; split <;> norm_num

/-- At every time at most one pair is on: the double sum is at most `1`. -/
lemma sum_badTable_le_one (w N : ℕ) :
    ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p = q then (0 : ℝ) else badTable p q N) ≤ 1 := by
  classical
  have hle : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p = q then (0 : ℝ) else badTable p q N)
      ≤ ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, badTable p q N := by
    refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
    by_cases hpq : p = q
    · simpa [hpq] using badTable_nonneg p q N
    · simp [hpq]
  refine hle.trans ?_
  rw [← Finset.sum_product']
  have : ∑ x ∈ (primesLe w) ×ˢ (primesLe w), badTable x.1 x.2 N
      = (((primesLe w) ×ˢ (primesLe w)).filter
          fun x => (Nat.unpair N).1 = Nat.pair x.1 x.2).card := by
    rw [← Finset.sum_boole]
    rfl
  rw [this]
  have hcard : (((primesLe w) ×ˢ (primesLe w)).filter
      fun x => (Nat.unpair N).1 = Nat.pair x.1 x.2).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have : Nat.pair x.1 x.2 = Nat.pair y.1 y.2 := by rw [← hx', ← hy']
    have := Nat.pair_eq_pair.mp this
    exact Prod.ext this.1 this.2
  exact_mod_cast hcard

/-- Every pair is on at arbitrarily late times. -/
lemma badTable_eq_one_frequently (p q M : ℕ) : ∃ N, M ≤ N ∧ badTable p q N = 1 := by
  refine ⟨Nat.pair (Nat.pair p q) M, ?_, ?_⟩
  · exact Nat.right_le_pair _ _
  · simp [badTable, Nat.unpair_pair]

/-- No pair decorrelates. -/
lemma not_tendsto_badTable (p q : ℕ) : ¬ Tendsto (fun N => badTable p q N) atTop (𝓝 0) := by
  intro h
  have := (h.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))).exists_forall_of_atTop
  obtain ⟨M, hM⟩ := this
  obtain ⟨N, hN, hN1⟩ := badTable_eq_one_frequently p q M
  have := hM N hN
  rw [hN1] at this
  norm_num at this

/-- The asynchronous table satisfies the averaged shape. -/
theorem avgShape_badTable : AvgShape badTable := by
  classical
  intro ε hε
  have hbig : Tendsto (fun w => ((primesLe w).card : ℝ) ^ 2) atTop atTop :=
    by simpa [pow_two] using tendsto_card_primesLe.atTop_mul_atTop₀ tendsto_card_primesLe
  have h1 : ∀ᶠ w : ℕ in atTop, 1 / ε < ((primesLe w).card : ℝ) ^ 2 :=
    hbig.eventually_gt_atTop _
  filter_upwards [h1, Filter.eventually_ge_atTop 2] with w hw hw2
  have hcpos : (0 : ℝ) < ((primesLe w).card : ℝ) := by
    exact_mod_cast card_primesLe_pos hw2
  have hsq : (0 : ℝ) < ((primesLe w).card : ℝ) ^ 2 := by positivity
  refine Filter.Eventually.of_forall fun N => ?_
  have := sum_badTable_le_one w N
  rw [avgTable, div_lt_iff₀ hsq]
  have : 1 < ε * ((primesLe w).card : ℝ) ^ 2 := by
    rw [div_lt_iff₀ hε] at hw
    linarith [hw]
  linarith [sum_badTable_le_one w N]

/-- **THE WORRY, REFUTED.**  The `TwoPointWeightedAvg` quantifier shape — average over a fixed
finite pair set, then `limsup` in `N` — does NOT entail decorrelation for a single pair.  There
is a `[0,1]`-valued correlation table satisfying the shape for which every pair correlates fully
at arbitrarily late times.  So the averaged leaf is not a repackaging of natural-density
two-point Elliott: the asynchrony of near-extremal times is genuine room. -/
theorem avgShape_not_imply_pairwise :
    ∃ G : ℕ → ℕ → ℕ → ℝ,
      (∀ p q N, 0 ≤ G p q N ∧ G p q N ≤ 1) ∧ AvgShape G ∧
      (∀ p q : ℕ, ¬ Tendsto (fun N => G p q N) atTop (𝓝 0)) :=
  ⟨badTable, fun p q N => ⟨badTable_nonneg p q N, badTable_le_one p q N⟩,
    avgShape_badTable, not_tendsto_badTable⟩

end NormalNumbers.CastingOut
