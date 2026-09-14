/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Entropy expedition §2/§4: finite Shannon entropy and the information-set lemma

This module is pure finite probability: no arithmetic, no geometry.  It supplies the
"information threshold set" step of the entropy budget (brief §4).

A `FinLaw Ω` is a probability vector on a `Fintype`.  Its base-two Shannon entropy is

  `H₂ L = (∑ ω, negMulLog (L.p ω)) / log 2`,

using `Real.negMulLog x = -x * log x`, which is **definitionally `0` at `x = 0`**: that is the
explicit zero-mass convention the brief asks for, inherited from mathlib rather than reinvented.

The **information set at threshold `θ`** is

  `infoSet L θ = {ω : 2 ^ (-θ) ≤ L.p ω}`,

the atoms carrying at least `2^{-θ}` mass, i.e. of information content `-log₂ p ω ≤ θ`.  Two
facts, both elementary and both proved here unconditionally:

* `card_infoSet_le` : `|infoSet L θ| ≤ 2 ^ θ` (each atom carries `≥ 2^{-θ}` of a total `1`);
* `prob_infoSet_ge` : if `H₂ L ≤ (1 - δ) M` with `0 < δ < 1` and `0 < M`, then at the
  threshold `θ = (1 - δ/2) M` the information set carries mass `≥ δ / (2 - δ)`.

The second is Markov's inequality applied to the nonnegative quantity `-log₂ p ω`, but it is
proved here *without* ever forming that quantity at a zero-mass atom: the pointwise inequality
`θ * q ≤ negMulLog q / log 2` for `0 ≤ q ≤ 2^{-θ}` holds at `q = 0` by inspection.  So no
`∞` arithmetic and no `ℝ≥0∞` detour is needed.

Combining the two with `M = m_K H_K`: a law whose entropy falls short of the maximum
`m_K H_K` by a factor `(1-δ)` must put mass `≥ δ/(2-δ)` on a set of at most
`2^{(1-δ/2) m_K H_K` atoms — a genuinely small collection of joint boxes, which is exactly
the input the cover bound (G) and the capture inequality (C) are contradicted against.
-/

open Finset Real

namespace NormalNumbers.G4Entropy

variable {Ω : Type*} [Fintype Ω]

/-- A probability vector on a finite type. -/
structure FinLaw (Ω : Type*) [Fintype Ω] where
  /-- the mass function -/
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_p : ∑ ω, p ω = 1

namespace FinLaw

variable (L : FinLaw Ω)

/-- The mass of a finite set of atoms. -/
def prob (B : Finset Ω) : ℝ := ∑ ω ∈ B, L.p ω

/-- Base-two Shannon entropy, with `negMulLog`'s built-in zero-mass convention. -/
noncomputable def H₂ : ℝ := (∑ ω, Real.negMulLog (L.p ω)) / Real.log 2

lemma p_le_one (ω : Ω) : L.p ω ≤ 1 := by
  rw [← L.sum_p]
  exact Finset.single_le_sum (f := L.p) (fun i _ => L.nonneg i) (Finset.mem_univ ω)

lemma prob_nonneg (B : Finset Ω) : 0 ≤ L.prob B :=
  Finset.sum_nonneg fun ω _ => L.nonneg ω

lemma prob_add_prob_compl [DecidableEq Ω] (B : Finset Ω) :
    L.prob B + L.prob Bᶜ = 1 := by
  rw [prob, prob, Finset.sum_add_sum_compl, L.sum_p]

lemma H₂_nonneg : 0 ≤ L.H₂ := by
  refine div_nonneg (Finset.sum_nonneg fun ω _ => ?_) (Real.log_nonneg (by norm_num))
  exact Real.negMulLog_nonneg (L.nonneg ω) (L.p_le_one ω)

open Classical in
/-- The **information set** at threshold `θ`: the atoms of mass at least `2^{-θ}`, i.e. of
information content at most `θ` bits. -/
noncomputable def infoSet (θ : ℝ) : Finset Ω :=
  Finset.univ.filter (fun ω => (2 : ℝ) ^ (-θ) ≤ L.p ω)

open Classical in
lemma mem_infoSet {θ : ℝ} {ω : Ω} : ω ∈ L.infoSet θ ↔ (2 : ℝ) ^ (-θ) ≤ L.p ω := by
  simp [infoSet]

/-- **Size of the information set**: at most `2^θ` atoms can each carry `2^{-θ}` of a unit mass. -/
theorem card_infoSet_le (θ : ℝ) : ((L.infoSet θ).card : ℝ) ≤ (2 : ℝ) ^ θ := by
  classical
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-θ) := Real.rpow_pos_of_pos (by norm_num) _
  have hsum : ((L.infoSet θ).card : ℝ) * (2 : ℝ) ^ (-θ) ≤ L.prob (L.infoSet θ) := by
    rw [prob, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun ω hω => (L.mem_infoSet).1 hω
  have hle1 : L.prob (L.infoSet θ) ≤ 1 := by
    rw [← L.sum_p, prob]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun ω _ _ => L.nonneg ω)
  have h : ((L.infoSet θ).card : ℝ) * (2 : ℝ) ^ (-θ) ≤ 1 := hsum.trans hle1
  have hmul : (2 : ℝ) ^ θ * (2 : ℝ) ^ (-θ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  nlinarith [hpos, h, hmul]

/-- The pointwise Markov step: below the threshold, `θ · q` is dominated by the entropy
contribution of `q`.  At `q = 0` both sides vanish, so no `-log 0` ever appears. -/
lemma mul_le_negMulLog_div {θ q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ (2 : ℝ) ^ (-θ)) :
    θ * q ≤ Real.negMulLog q / Real.log 2 := by
  rcases eq_or_lt_of_le hq0 with h | h
  · simp [← h]
  · have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlq : Real.log q ≤ -θ * Real.log 2 := by
      have h1 : Real.log q ≤ Real.log ((2 : ℝ) ^ (-θ)) := Real.log_le_log h hq
      rwa [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at h1
    rw [Real.negMulLog, le_div_iff₀ hlog2]
    nlinarith [h, hlq]

/-- **Markov on the information content.**  The mass outside the information set at threshold
is at most `H₂ / θ`, in the form `θ · Pr[outside] ≤ H₂`. -/
theorem mul_prob_compl_infoSet_le [DecidableEq Ω] (θ : ℝ) :
    θ * L.prob (L.infoSet θ)ᶜ ≤ L.H₂ := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have step : θ * L.prob (L.infoSet θ)ᶜ
      ≤ ∑ ω ∈ (L.infoSet θ)ᶜ, Real.negMulLog (L.p ω) / Real.log 2 := by
    rw [prob, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    have : ¬ ((2 : ℝ) ^ (-θ) ≤ L.p ω) := by
      intro h
      exact (Finset.mem_compl.1 hω) ((L.mem_infoSet).2 h)
    exact mul_le_negMulLog_div (L.nonneg ω) (le_of_lt (not_le.1 this))
  refine step.trans ?_
  rw [H₂, Finset.sum_div]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun ω _ _ => ?_
  exact div_nonneg (Real.negMulLog_nonneg (L.nonneg ω) (L.p_le_one ω)) hlog2.le

/-- **The information-set lemma** (brief §4).  If the entropy of `L` falls short of `M` by a
factor `1 - δ`, then the information set at threshold `(1 - δ/2) M` carries mass at least
`δ / (2 - δ)` while containing at most `2^{(1-δ/2)M}` atoms (`card_infoSet_le`). -/
theorem prob_infoSet_ge [DecidableEq Ω] {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM : 0 < M)
    (hH : L.H₂ ≤ (1 - δ) * M) :
    δ / (2 - δ) ≤ L.prob (L.infoSet ((1 - δ / 2) * M)) := by
  set θ : ℝ := (1 - δ / 2) * M with hθdef
  have hθpos : 0 < θ := by
    have : 0 < 1 - δ / 2 := by linarith
    exact mul_pos this hM
  have hmark := L.mul_prob_compl_infoSet_le θ
  have hsum := L.prob_add_prob_compl (L.infoSet θ)
  have hcompl : θ * L.prob (L.infoSet θ)ᶜ ≤ (1 - δ) * M := hmark.trans hH
  have h2δ : 0 < 2 - δ := by linarith
  rw [div_le_iff₀ h2δ]
  nlinarith [hcompl, hsum, hθpos, hM, L.prob_nonneg (L.infoSet θ)ᶜ]

/-! ### Maximum entropy: the sanity bound `H₂ ≤ log₂ N` -/

/-- The pointwise form of the maximum-entropy inequality, from `negMulLog s ≤ 1 - s` at
`s = q·N`.  Valid at `q = 0` as well. -/
lemma negMulLog_le_of_card {N : ℝ} (hN : 0 < N) {q : ℝ} (hq : 0 ≤ q) :
    Real.negMulLog q ≤ q * Real.log N + (1 / N - q) := by
  have h := Real.negMulLog_le_one_sub_self (x := q * N) (by positivity)
  rw [Real.negMulLog_mul] at h
  have hNlog : Real.negMulLog N = -N * Real.log N := rfl
  rw [hNlog] at h
  have key : N * Real.negMulLog q ≤ N * (q * Real.log N + (1 / N - q)) := by
    have hexp : N * (q * Real.log N + (1 / N - q)) = q * N * Real.log N + 1 - q * N := by
      field_simp
      ring
    rw [hexp]
    nlinarith [h]
  exact le_of_mul_le_mul_left key hN

/-- **Maximum entropy.**  If all the mass sits on at most `N` atoms then `H₂ L ≤ log₂ N`. -/
theorem H₂_le_logb [DecidableEq Ω] {N : ℕ} (hN : 0 < N) (T : Finset Ω)
    (hT : ∀ ω, L.p ω ≠ 0 → ω ∈ T) (hcard : T.card ≤ N) :
    L.H₂ ≤ Real.logb 2 N := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hzero : ∀ ω ∈ Tᶜ, Real.negMulLog (L.p ω) = 0 := by
    intro ω hω
    have : L.p ω = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hω) (hT ω h)
    simp [this]
  have hmassT : ∑ ω ∈ T, L.p ω = 1 := by
    have hz : ∀ ω ∈ Tᶜ, L.p ω = 0 := by
      intro ω hω
      by_contra h
      exact (Finset.mem_compl.1 hω) (hT ω h)
    have := Finset.sum_add_sum_compl T L.p
    rw [L.sum_p] at this
    rw [Finset.sum_eq_zero hz] at this
    linarith
  have hsplit : ∑ ω, Real.negMulLog (L.p ω) = ∑ ω ∈ T, Real.negMulLog (L.p ω) := by
    have := Finset.sum_add_sum_compl T (fun ω => Real.negMulLog (L.p ω))
    rw [Finset.sum_eq_zero hzero] at this
    linarith
  have hbound : ∑ ω ∈ T, Real.negMulLog (L.p ω)
      ≤ ∑ ω ∈ T, (L.p ω * Real.log N + (1 / (N : ℝ) - L.p ω)) :=
    Finset.sum_le_sum fun ω _ => negMulLog_le_of_card hNR (L.nonneg ω)
  have hrhs : ∑ ω ∈ T, (L.p ω * Real.log N + (1 / (N : ℝ) - L.p ω))
      = Real.log N + (T.card / (N : ℝ) - 1) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmassT, Finset.sum_sub_distrib, hmassT,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hcardR : (T.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  have hfin : ∑ ω, Real.negMulLog (L.p ω) ≤ Real.log N := by
    rw [hsplit]
    refine hbound.trans ?_
    rw [hrhs]
    have : (T.card : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNR]; exact hcardR
    linarith
  rw [H₂, Real.logb, div_le_div_iff_of_pos_right hlog2]
  exact hfin

/-- Maximum entropy against the ambient alphabet. -/
theorem H₂_le_logb_card [DecidableEq Ω] (h : 0 < Fintype.card Ω) :
    L.H₂ ≤ Real.logb 2 (Fintype.card Ω) :=
  L.H₂_le_logb h Finset.univ (fun ω _ => Finset.mem_univ ω) (by simp)

end FinLaw

/-! ### Empirical laws: the pushforward of a uniform point of a finite sample -/

open Classical in
/-- The law of `f i` for `i` uniform in the nonempty finite sample `S`.  This is the
pushforward of **one** uniform choice, which is what the joint entropy sample needs. -/
noncomputable def empirical {ι Ω : Type*} [Fintype Ω] (S : Finset ι) (hS : S.Nonempty)
    (f : ι → Ω) : FinLaw Ω where
  p ω := ((S.filter fun i => f i = ω).card : ℝ) / S.card
  nonneg ω := by positivity
  sum_p := by
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 hS
    rw [← Finset.sum_div]
    rw [div_eq_one_iff_eq hcard.ne']
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := Finset.univ)
      (fun i _ => Finset.mem_univ (f i))
    exact_mod_cast this.symm

open Classical in
lemma empirical_p {ι Ω : Type*} [Fintype Ω] {S : Finset ι} (hS : S.Nonempty) (f : ι → Ω)
    (ω : Ω) :
    (empirical S hS f).p ω = ((S.filter fun i => f i = ω).card : ℝ) / S.card := rfl

open Classical in
/-- The empirical law is supported on the image, so its entropy is at most `log₂ |S|`. -/
theorem H₂_empirical_le {ι Ω : Type*} [Fintype Ω] {S : Finset ι} (hS : S.Nonempty)
    (f : ι → Ω) : (empirical S hS f).H₂ ≤ Real.logb 2 S.card := by
  classical
  refine (empirical S hS f).H₂_le_logb (Finset.card_pos.2 hS) (S.image f) ?_ Finset.card_image_le
  intro ω hω
  rw [empirical_p] at hω
  have hne : (S.filter fun i => f i = ω).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h
    push_neg at h
    have : (S.filter fun i => f i = ω).card = 0 := by omega
    rw [this] at hω
    simp at hω
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_filter] at hi
  exact Finset.mem_image.2 ⟨i, hi.1, hi.2⟩

end NormalNumbers.G4Entropy
