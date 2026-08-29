/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ConditionalDisjunctive

/-!
# The positive-rate rung of the ln-two ladder (Track D, the frequency hypothesis)

`LnTwo.lean` welds full equidistribution of the Bailey–Crandall surrogate
orbit to normality of `ln 2`; `ConditionalDisjunctive.lean` welds the
topological cluster hypotheses `Λ` and `D_w` to disjunctivity.  This file
adds the rung strictly between them: a **recurrence-rate** hypothesis.

**`LnTwoHypothesisFreq w`**: the surrogate orbit visits a compact
sub-interval of the open binary cylinder of `w` with positive lower
frequency.  This asks for a *rate*, not a limit — it is implied by
equidistribution (`hypothesisFreq_of_equidistributed`) but demands none of
the frequency limits Wall's theorem needs, and it implies the cluster
hypothesis `D_w` is not needed either: the digit conclusion is proved
directly and is *quantitative* — the word `w` occurs in the binary
expansion of `ln 2` with positive lower frequency
(`freq_occursAt_log_two_of_hypothesisFreq`), not merely infinitely often.

The engine is a one-sided counting transfer
(`le_visitCount_fract_perturb_add`): a nonnegative vanishing perturbation
can only push finitely many visits of a compact sub-interval out of the
enclosing target interval, so visit *counts* survive up to an additive
constant — which a positive rate absorbs.
-/

namespace NormalNumbers

open Filter Set

/-! ### The one-sided counting transfer -/

private lemma card_filter_le_card_filter_add {P Q : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] (N : ℕ)
    (h : ∀ k, N ≤ k → P k → Q k) (n : ℕ) :
    ((Finset.range n).filter P).card ≤ ((Finset.range n).filter Q).card + N := by
  have hsub : (Finset.range n).filter P ⊆ (Finset.range n).filter Q ∪ Finset.range N := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hk ⊢
    rcases le_or_gt N k with hNk | hNk
    · exact Or.inl ⟨hk.1, h k hNk hk.2⟩
    · exact Or.inr hNk
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.range n).filter Q) (Finset.range N)
  have h3 := Finset.card_range N
  omega

/-- **One-sided counting transfer.**  Visits of `u` to an inner interval
`[a', c')` become visits of the perturbed sequence `n ↦ (u n + δ n) mod 1`
to any enclosing `[a, c)` with room `c' < c ≤ 1` on the right, up to an
additive constant: once `δ n < c − c'` the perturbation cannot push a
visit out (no wraparound is possible below `1`). -/
theorem le_visitCount_fract_perturb_add (u δ : ℕ → ℝ) {a c a' c' : ℝ}
    (ha : a ≤ a') (hcc : c' < c) (hc1 : c ≤ 1)
    (hu0 : ∀ n, 0 ≤ u n)
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (nhds 0)) :
    ∃ N₀ : ℕ, ∀ n, visitCount u a' c' n
      ≤ visitCount (fun k => Int.fract (u k + δ k)) a c n + N₀ := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hδ.eventually_lt_const (show (0 : ℝ) < c - c' by linarith))
  refine ⟨N₀, fun n => ?_⟩
  unfold visitCount
  refine card_filter_le_card_filter_add N₀ (fun k hk hP => ?_) n
  have hδk := hN₀ k hk
  have h0 : 0 ≤ u k + δ k := add_nonneg (hu0 k) (hδ0 k)
  have h1 : u k + δ k < 1 := by
    have := hP.2
    linarith [hc1]
  show Int.fract (u k + δ k) ∈ Set.Ico a c
  rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]
  exact ⟨le_trans ha (le_trans hP.1 (le_add_of_nonneg_right (hδ0 k))),
    by linarith [hP.2]⟩

/-! ### The frequency hypothesis and its digit conclusion -/

/-- **The recurrence-rate hypothesis `Freq_w` for `ln 2`**, encoded as a
named hypothesis rather than a Lean axiom: the explicit rational surrogate
orbit visits some compact sub-interval `[a', c')` of the open binary
cylinder of `w` with positive lower frequency.

Strictly weaker than `Equidistributed lnTwoOrbit`
(`hypothesisFreq_of_equidistributed`): it asks for a positive *rate* of
visits, but no frequency limit for any interval. -/
def LnTwoHypothesisFreq (w : List ℕ) : Prop :=
  ∃ a' c' ρ : ℝ, 0 < ρ ∧
    (blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length < a' ∧
    c' < ((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length ∧
    ∀ᶠ N in atTop, ρ * N ≤ (visitCount lnTwoOrbit a' c' N : ℝ)

/-- **The quantitative digit conclusion**: under `Freq_w`, the doubling
orbit of `ln 2` itself visits the closed-form cylinder interval of `w`
with positive lower frequency. -/
theorem freq_visits_log_two_of_hypothesisFreq (w : List ℕ)
    (hw : ∀ d ∈ w, d < 2) (h : LnTwoHypothesisFreq w) :
    ∃ ρ > (0 : ℝ), ∀ᶠ N in atTop,
      ρ * N ≤ (visitCount (orbit 2 (Real.log 2))
        ((blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length)
        (((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length) N : ℝ) := by
  obtain ⟨a', c', ρ, hρ, ha', hc', hfreq⟩ := h
  set a : ℝ := (blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length with ha_def
  set c : ℝ := ((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length with hc_def
  have hval : blockNatVal 2 w < 2 ^ w.length := blockNatVal_lt 2 w hw
  have hpow : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc_def, div_le_one hpow]
    exact_mod_cast Nat.succ_le_of_lt hval
  -- transfer the surrogate's visits to the true orbit
  obtain ⟨N₀, hN₀⟩ := le_visitCount_fract_perturb_add lnTwoOrbit
    (fun n => 2 ^ n * lnTwoTail n) (le_of_lt ha') hc' hc1
    (fun n => (lnTwoOrbit_mem_Ico n).1)
    pow_mul_lnTwoTail_nonneg tendsto_pow_mul_lnTwoTail
  have horb : (fun k => Int.fract (lnTwoOrbit k + 2 ^ k * lnTwoTail k))
      = orbit 2 (Real.log 2) := funext fun n => (orbit_log_two_eq n).symm
  rw [horb] at hN₀
  refine ⟨ρ / 2, by positivity, ?_⟩
  have hbig : ∀ᶠ N : ℕ in atTop, (N₀ : ℝ) ≤ (ρ / 2) * N := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    filter_upwards [Filter.eventually_ge_atTop (⌈(2 * N₀ : ℝ) / ρ⌉₊)] with N hN
    have h1 : (2 * N₀ : ℝ) / ρ ≤ (N : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    rw [div_le_iff₀ hρ] at h1
    linarith
  filter_upwards [hfreq, hbig] with N h1 h2
  have h3 := hN₀ N
  have h4 : (visitCount lnTwoOrbit a' c' N : ℝ)
      ≤ (visitCount (orbit 2 (Real.log 2)) a c N : ℝ) + N₀ := by
    exact_mod_cast h3
  linarith

/-- Under `Freq_w`, the word `w` occurs at a set of positions of positive
lower frequency in the canonical binary expansion of `ln 2` — the
quantitative strengthening of `D_w`'s "infinitely often". -/
theorem freq_occursAt_log_two_of_hypothesisFreq (w : List ℕ)
    (hw : ∀ d ∈ w, d < 2) (h : LnTwoHypothesisFreq w) :
    ∃ ρ > (0 : ℝ), ∀ᶠ N in atTop,
      ρ * N ≤ (((Finset.range N).filter
        (fun n => orbit 2 (Real.log 2) n ∈ Set.Ico
          ((blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length)
          (((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length))).card : ℝ) :=
  freq_visits_log_two_of_hypothesisFreq w hw h

/-- In particular `Freq_w` recovers `D_w`'s conclusion: `w` occurs
arbitrarily late in the binary expansion of `ln 2`. -/
theorem frequently_occursAt_log_two_of_hypothesisFreq (w : List ℕ)
    (hw : ∀ d ∈ w, d < 2) (h : LnTwoHypothesisFreq w) :
    ∃ᶠ n in atTop, OccursAt 2 (Real.log 2) w n := by
  obtain ⟨ρ, hρ, hfreq⟩ := freq_visits_log_two_of_hypothesisFreq w hw h
  rw [Filter.frequently_atTop]
  intro m
  -- if no occurrence past `m`, the visit count is bounded by `m`,
  -- contradicting linear growth
  by_contra hnone
  push Not at hnone
  have hbound : ∀ N, visitCount (orbit 2 (Real.log 2))
      ((blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length)
      (((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length) N ≤ m := by
    intro N
    unfold visitCount
    classical
    have hsub : ((Finset.range N).filter fun k => orbit 2 (Real.log 2) k ∈ Set.Ico
        ((blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length)
        (((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length)) ⊆ Finset.range m := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      by_contra hkm
      push Not at hkm
      exact hnone k hkm ((occursAt_iff_orbit_mem 2 (by omega) (Real.log 2) w hw k).2 hk.2)
    simpa using Finset.card_le_card hsub
  obtain ⟨N, hN⟩ := (hfreq.and (Filter.eventually_ge_atTop
    (⌈(m + 1 : ℝ) / ρ⌉₊))).exists
  have h1 : (m + 1 : ℝ) / ρ ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN.2)
  rw [div_le_iff₀ hρ] at h1
  have h2 := hbound N
  have h3 : (visitCount (orbit 2 (Real.log 2))
      ((blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length)
      (((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length) N : ℝ) ≤ m := by
    exact_mod_cast h2
  nlinarith [hN.1]

/-! ### Position in the weakening lattice -/

/-- **Equidistribution sits strictly above `Freq_w`**: full equidistribution
of the surrogate orbit yields the recurrence-rate hypothesis for every
valid word, by aiming at the middle half of the cylinder. -/
theorem hypothesisFreq_of_equidistributed (hE : Equidistributed lnTwoOrbit)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 2) : LnTwoHypothesisFreq w := by
  set a : ℝ := (blockNatVal 2 w : ℝ) / (2 : ℝ) ^ w.length with ha_def
  set c : ℝ := ((blockNatVal 2 w : ℝ) + 1) / (2 : ℝ) ^ w.length with hc_def
  have hval : blockNatVal 2 w < 2 ^ w.length := blockNatVal_lt 2 w hw
  have hpow : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hac : a < c := by
    rw [ha_def, hc_def, div_lt_div_iff_of_pos_right hpow]
    linarith
  have hc1 : c ≤ 1 := by
    rw [hc_def, div_le_one hpow]
    exact_mod_cast Nat.succ_le_of_lt hval
  -- the middle half `[a + L/4, c − L/4)`, `L = c − a`
  set L : ℝ := c - a with hL_def
  have hL : 0 < L := by simp only [hL_def]; linarith
  refine ⟨a + L / 4, c - L / 4, L / 4, by positivity, by linarith, by linarith, ?_⟩
  have hlim := hE (a + L / 4) (c - L / 4) (by linarith) (by linarith) (by linarith)
  have hgap : (c - L / 4) - (a + L / 4) = L / 2 := by ring
  rw [hgap] at hlim
  have hev := (tendsto_order.1 hlim).1 (L / 4) (by linarith)
  filter_upwards [hev, Filter.eventually_gt_atTop 0] with N h1 h2
  have hN : (0 : ℝ) < N := by exact_mod_cast h2
  rw [lt_div_iff₀ hN] at h1
  linarith
