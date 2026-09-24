import NormalNumbers.TwoPointGramBudget

/-!
# What the leaf says pair-by-pair: a Markov step, and what it does NOT say

Lap 13 showed the leaf `twoPointGramSum b t (w N) N = o(N·L(w N)²)` demands an unbounded saving
over the trivial bound.  This file extracts the per-pair content.

**Markov.**  `#{ (p,q) : p ≠ q ≤ w, ‖Σ_{m ≤ min(N/p,N/q)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} W(m)‖ ≥ ηN }
≤ twoPointGramSum / (ηN)`, so under the leaf that count is `o(L(w N)²)` for every fixed `η > 0`.

**What it does NOT give.**  A *fixed* pair `(p,q)` gets only `T_{p,q}(N) ≤ o(N·L(w N)²)`, and
`L(w N) → ∞`, so the leaf does not imply even `T_{p,q}(N) = o(N)` for a single pair: the
individual-term bound is vacuous.  The content is entirely about the *distribution* of the pair
correlations — all but `o(L(w)²)` pairs must decorrelate at scale `ηN` — while the number of
pairs is `π(w)² ≫ L(w)²`.

So the leaf sits strictly between two named statements: it is **not implied by** per-pair
qualitative decorrelation (lap 13: the budget is too small), and it does **not imply** per-pair
decorrelation for any prescribed pair (this file).  It is a genuinely averaged Elliott-type
statement over a dilation set growing with `N`, i.e. an MRT-shaped problem, not a Tao-2016-shaped
one.  That is the sharpest placement of the leaf in the literature this run has reached.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The pairs whose truncated two-point correlation is at least `η·N`. -/
noncomputable def badPairs (b : ℕ) (t : ℝ) (η : ℝ) (w N : ℕ) : Finset (ℕ × ℕ) :=
  (primesLe w ×ˢ primesLe w).filter
    (fun pq => pq.1 ≠ pq.2 ∧ η * (N : ℝ) ≤ ‖twoPointTruncSum b pq.1 pq.2 t N‖)

lemma twoPointGramSum_eq_prod (b : ℕ) (t : ℝ) (w N : ℕ) :
    twoPointGramSum b t w N
      = ∑ pq ∈ primesLe w ×ˢ primesLe w,
          (if pq.1 = pq.2 then 0 else ‖twoPointTruncSum b pq.1 pq.2 t N‖) := by
  rw [twoPointGramSum, Finset.sum_product]

/-- **MARKOV.**  The number of `η`-correlated pairs is at most `twoPointGramSum / (ηN)`. -/
theorem card_badPairs_mul_le (b : ℕ) (t : ℝ) (η : ℝ) (w N : ℕ) (hη : 0 < η) :
    ((badPairs b t η w N).card : ℝ) * (η * (N : ℝ)) ≤ twoPointGramSum b t w N := by
  classical
  have hsub : badPairs b t η w N ⊆ primesLe w ×ˢ primesLe w := Finset.filter_subset _ _
  have hnn : ∀ pq ∈ primesLe w ×ˢ primesLe w, pq ∉ badPairs b t η w N →
      (0 : ℝ) ≤ (if pq.1 = pq.2 then 0 else ‖twoPointTruncSum b pq.1 pq.2 t N‖) := by
    intro pq _ _
    split
    · exact le_rfl
    · exact norm_nonneg _
  have hterm : ∀ pq ∈ badPairs b t η w N,
      η * (N : ℝ) ≤ (if pq.1 = pq.2 then 0 else ‖twoPointTruncSum b pq.1 pq.2 t N‖) := by
    intro pq hpq
    have h := (Finset.mem_filter.mp hpq).2
    rw [if_neg h.1]
    exact h.2
  calc ((badPairs b t η w N).card : ℝ) * (η * (N : ℝ))
      = ∑ _pq ∈ badPairs b t η w N, η * (N : ℝ) := by rw [Finset.sum_const]; ring
    _ ≤ ∑ pq ∈ badPairs b t η w N,
          (if pq.1 = pq.2 then 0 else ‖twoPointTruncSum b pq.1 pq.2 t N‖) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ pq ∈ primesLe w ×ˢ primesLe w,
          (if pq.1 = pq.2 then 0 else ‖twoPointTruncSum b pq.1 pq.2 t N‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = twoPointGramSum b t w N := (twoPointGramSum_eq_prod b t w N).symm

/-- **THE PER-PAIR CONTENT OF THE LEAF.**  For every `η > 0`, the proportion of `η`-correlated
pairs, measured against the Kátai budget `L(w N)²`, tends to `0`. -/
theorem card_badPairs_div_tendsto (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (η : ℝ) (hη : 0 < η)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hslow : ∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ))
    (hgram : Tendsto (fun N => twoPointGramSum b t (w N) N / ((N : ℝ) * (kataiPrimeRecip (w N)) ^ 2))
      atTop (𝓝 0)) :
    Tendsto (fun N => ((badPairs b t η (w N) N).card : ℝ) / (kataiPrimeRecip (w N)) ^ 2)
      atTop (𝓝 0) := by
  have hmaj : Tendsto
      (fun N => (1 / η) * (twoPointGramSum b t (w N) N
        / ((N : ℝ) * (kataiPrimeRecip (w N)) ^ 2))) atTop (𝓝 0) := by
    simpa using hgram.const_mul (1 / η)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hslow] with N hN
    have hL : 0 < kataiPrimeRecip (w N) := by
      have := kataiPrimeRecip_ge_half hN.1; linarith
    positivity
  · filter_upwards [hslow, Filter.eventually_gt_atTop 0] with N hN hNpos
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hL : 0 < kataiPrimeRecip (w N) := by
      have := kataiPrimeRecip_ge_half hN.1; linarith
    have hkey := card_badPairs_mul_le b t η (w N) N hη
    set G := twoPointGramSum b t (w N) N with hGdef
    set Lw := kataiPrimeRecip (w N) with hLdef
    have hrw : 1 / η * (G / ((N : ℝ) * Lw ^ 2)) = G / (η * (N:ℝ) * Lw ^ 2) := by
      field_simp
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos : (0:ℝ) < η * (N:ℝ) := by positivity
    nlinarith [hkey, sq_nonneg Lw, hL, hpos]

end NormalNumbers.CastingOut
