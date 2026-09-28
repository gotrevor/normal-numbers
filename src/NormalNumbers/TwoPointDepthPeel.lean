import NormalNumbers.PairDecoupleOneDigit

/-!
# Dropping the peel weight: the fixed pair at GROWING depth

`PairDecoupleOneDigit.lean` factors the fixed-pair phase EXACTLY at every depth `K`,

    e(t · pairTail) = (2K-point root-of-unity product) · peelWeightAt b p q K t n ,

with `peelWeightAt = e(t b^{−K} · (θ_{pn+K} − θ_{qn+K}))` a unit-modulus weight.  At a FIXED `K`
that weight is a genuine obstruction: it is a bounded but arithmetically wild factor, so the leaf
at fixed depth (`MultiElliottWeighted`) is a *weighted* correlation.

This file runs the directive's mandated move: let the depth GROW with the range.  Since
`omegaTail b N ≤ log₂(N+1) + 1` (`omegaTail_le_log`), the weight's argument is
`O(|t| b^{−K} log M)` uniformly over `n < M`, so **for `K = K(M)` with `b^{K(M)} ≫ log M` the
weight is `1 + o(1)` uniformly** and drops out.  The crux then becomes an *unweighted*
`2K(M)`-point Elliott correlation — the shape the literature (Tao, MRT) actually speaks about.

Main results:
* `norm_phase_pairTail_sub_digitTrunc` — the pointwise weight-removal error, explicit;
* `norm_fullMean_sub_le` — the same on the mean over `n < M`, with the explicit bound
  `peelBound b p q K M t`;
* **`pairDecorr_of_unweighted`** — `PairDecorr b t` from unweighted `2K(M)`-point means, for any
  depth schedule `K` whose `peelBound` vanishes;
* `tendsto_peelBound_id` — the schedule `K(M) = M` satisfies that hypothesis, so the criterion is
  not vacuous.  (`K(M) ≈ log_b log M` is the efficient choice and also satisfies it; the
  criterion is stated for an arbitrary schedule precisely so the user picks the cheapest one.)
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `|θ_{pn+K} − θ_{qn+K}|` is at most the sum of the two logarithmic carry bounds. -/
lemma abs_shiftPairTail_le (b : ℕ) (hb : 2 ≤ b) (p q K n : ℕ) :
    |shiftPairTail b p q K K n|
      ≤ ((Nat.log 2 (p * n + K + 1) : ℝ) + 1) + ((Nat.log 2 (q * n + K + 1) : ℝ) + 1) := by
  have h1 := omegaTail_le_log b hb (p * n + K)
  have h2 := omegaTail_le_log b hb (q * n + K)
  have h1n := omegaTail_nonneg b hb (p * n + K)
  have h2n := omegaTail_nonneg b hb (q * n + K)
  rw [shiftPairTail, abs_le]
  constructor <;> linarith

/-- **The weight-removal error, pointwise.**  `4π|t| b^{−K}` times the carry bound. -/
theorem norm_phase_pairTail_sub_digitTrunc (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (p q K n : ℕ) :
    ‖phase (t * pairTail b p q n) - phase (t * digitTrunc b p q K n)‖
      ≤ 4 * Real.pi * |t| / (b : ℝ) ^ K
        * (((Nat.log 2 (p * n + K + 1) : ℝ) + 1) + ((Nat.log 2 (q * n + K + 1) : ℝ) + 1)) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  set u : ℝ := t / (b : ℝ) ^ K * shiftPairTail b p q K K n with hu
  have hsplit : t * pairTail b p q n = t * digitTrunc b p q K n + u := by
    rw [pairTail_eq_digitTrunc_add b hb p q K n, hu]
    field_simp
  have hfac : phase (t * pairTail b p q n) - phase (t * digitTrunc b p q K n)
      = phase (t * digitTrunc b p q K n) * (phase u - 1) := by
    rw [hsplit, phase_add]; ring
  rw [hfac, norm_mul, norm_phase, one_mul]
  refine le_trans (norm_phase_sub_one_le' u) ?_
  have habs : |u| = |t| / (b : ℝ) ^ K * |shiftPairTail b p q K K n| := by
    rw [hu, abs_mul, abs_div, abs_of_pos hbK]
  rw [habs]
  have hB := abs_shiftPairTail_le b hb p q K n
  have hc : (0 : ℝ) ≤ 4 * Real.pi * (|t| / (b : ℝ) ^ K) := by positivity
  calc 4 * Real.pi * (|t| / (b : ℝ) ^ K * |shiftPairTail b p q K K n|)
      = (4 * Real.pi * (|t| / (b : ℝ) ^ K)) * |shiftPairTail b p q K K n| := by ring
    _ ≤ (4 * Real.pi * (|t| / (b : ℝ) ^ K))
        * (((Nat.log 2 (p * n + K + 1) : ℝ) + 1) + ((Nat.log 2 (q * n + K + 1) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hB hc
    _ = _ := by ring

/-- The explicit uniform weight-removal budget on `[0, M)`. -/
noncomputable def peelBound (b p q K M : ℕ) (t : ℝ) : ℝ :=
  4 * Real.pi * |t| / (b : ℝ) ^ K
    * (((Nat.log 2 (p * M + K + 1) : ℝ) + 1) + ((Nat.log 2 (q * M + K + 1) : ℝ) + 1))

lemma peelBound_nonneg (b p q K M : ℕ) (t : ℝ) (hb : 2 ≤ b) : 0 ≤ peelBound b p q K M t := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  unfold peelBound
  have : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  positivity

/-- **The weight-removal error on the mean.**  Uniform over `n < M`, by monotonicity of `log₂`. -/
theorem norm_fullMean_sub_le (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (p q K M : ℕ) :
    ‖fullMean (fun n => phase (t * pairTail b p q n)) M
        - fullMean (fun n => phase (t * digitTrunc b p q K n)) M‖
      ≤ peelBound b p q K M t := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [fullMean, peelBound_nonneg b p q K 0 t hb]
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  have hptwise : ∀ n ∈ range M,
      ‖phase (t * pairTail b p q n) - phase (t * digitTrunc b p q K n)‖
        ≤ peelBound b p q K M t := by
    intro n hn
    simp only [Finset.mem_range] at hn
    refine le_trans (norm_phase_pairTail_sub_digitTrunc b hb t p q K n) ?_
    have hmono1 : (Nat.log 2 (p * n + K + 1) : ℝ) ≤ (Nat.log 2 (p * M + K + 1) : ℝ) := by
      exact_mod_cast Nat.log_mono_right (by nlinarith [Nat.mul_le_mul_left p (le_of_lt hn)])
    have hmono2 : (Nat.log 2 (q * n + K + 1) : ℝ) ≤ (Nat.log 2 (q * M + K + 1) : ℝ) := by
      exact_mod_cast Nat.log_mono_right (by nlinarith [Nat.mul_le_mul_left q (le_of_lt hn)])
    unfold peelBound
    have hc : (0 : ℝ) ≤ 4 * Real.pi * |t| / (b : ℝ) ^ K := by positivity
    nlinarith [hmono1, hmono2, hc]
  have hsum : ‖∑ n ∈ range M, (phase (t * pairTail b p q n)
      - phase (t * digitTrunc b p q K n))‖ ≤ (M : ℝ) * peelBound b p q K M t := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ n ∈ range M, ‖phase (t * pairTail b p q n) - phase (t * digitTrunc b p q K n)‖
        ≤ ∑ _n ∈ range M, peelBound b p q K M t := Finset.sum_le_sum hptwise
      _ = (M : ℝ) * peelBound b p q K M t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [fullMean, fullMean, div_sub_div_same, ← Finset.sum_sub_distrib, norm_div,
    Complex.norm_natCast, div_le_iff₀ hMR]
  linarith [hsum]

/-- **THE UNWEIGHTED LEAF AT A GROWING DEPTH.**  No `peelWeight`: a pure `2K(M)`-point
root-of-unity correlation, the object Elliott/Tao/MRT-type theorems are about. -/
def MultiElliottGrowing (b p q : ℕ) (t : ℝ) (K : ℕ → ℕ) : Prop :=
  Tendsto (fun M => fullMean (fun n =>
    ∏ k ∈ range (K M), (digitRoot b t k ^ omegaNat (p * n + 1 + k)
      * (starRingEnd ℂ) (digitRoot b t k ^ omegaNat (q * n + 1 + k)))) M) atTop (𝓝 0)

/-- **The directive's step 2, formalised.**  If the depth schedule `K` beats the carry
(`peelBound → 0`) and the *unweighted* `2K(M)`-point means vanish, then the fixed-pair crux
`PairDecorr b t` holds.  The weight is gone; only an Elliott correlation is left. -/
theorem pairDecorr_of_unweighted (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K : ℕ → ℕ)
    (hbud : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun M => peelBound b p q (K M) M t) atTop (𝓝 0))
    (hmul : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t K) :
    PairDecorr b t := by
  intro p q hp hq hpq
  have hmain : Tendsto (fun M =>
      fullMean (fun n => phase (t * digitTrunc b p q (K M) n)) M) atTop (𝓝 0) := by
    refine (hmul p q hp hq hpq).congr fun M => ?_
    refine congrArg (fun z => z / (M : ℂ)) (Finset.sum_congr rfl fun n _ => ?_)
    exact (phase_digitTrunc b t p q (K M) n).symm
  have hdiff : Tendsto (fun M =>
      fullMean (fun n => phase (t * pairTail b p q n)) M
        - fullMean (fun n => phase (t * digitTrunc b p q (K M) n)) M) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun M => norm_nonneg _)
      (Filter.Eventually.of_forall fun M => norm_fullMean_sub_le b hb t p q (K M) M)
      (hbud p q hp hq hpq)
  have := hdiff.add hmain
  simpa [pairTail] using this

/-! ### Non-vacuity of the budget hypothesis -/

/-- The schedule `K(M) = M` satisfies the budget hypothesis: the carry bound is `O(M)` while
`b^M ≥ 2^M`.  (The efficient schedule `K(M) ≍ log_b log M` also does; this lemma only certifies
that `pairDecorr_of_unweighted` is not vacuous.) -/
theorem tendsto_peelBound_id (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ) :
    Tendsto (fun M => peelBound b p q M M t) atTop (𝓝 0) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbig : ∀ M : ℕ, (2 : ℝ) ^ M ≤ (b : ℝ) ^ M := by
    intro M
    refine pow_le_pow_left₀ (by norm_num) ?_ M
    exact_mod_cast hb
  -- majorant: `C · (M+1) · (1/2)^M`
  set C : ℝ := 4 * Real.pi * |t| * ((p : ℝ) + q + 4) with hC
  have hCnn : 0 ≤ C := by
    have : (0 : ℝ) ≤ (p : ℝ) + q + 4 := by positivity
    rw [hC]; positivity
  have hmaj : ∀ M : ℕ, peelBound b p q M M t ≤ C * ((M : ℝ) + 1) * (1 / 2 : ℝ) ^ M := by
    intro M
    have hlog1 : (Nat.log 2 (p * M + M + 1) : ℝ) ≤ ((p * M + M + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.log_le_self 2 _
    have hlog2 : (Nat.log 2 (q * M + M + 1) : ℝ) ≤ ((q * M + M + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.log_le_self 2 _
    have hL : ((Nat.log 2 (p * M + M + 1) : ℝ) + 1) + ((Nat.log 2 (q * M + M + 1) : ℝ) + 1)
        ≤ ((p : ℝ) + q + 4) * ((M : ℝ) + 1) := by
      push_cast at hlog1 hlog2
      nlinarith [hlog1, hlog2, Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) p,
        Nat.cast_nonneg (α := ℝ) q]
    have hbM : (0 : ℝ) < (b : ℝ) ^ M := by positivity
    have hinv : 1 / (b : ℝ) ^ M ≤ (1 / 2 : ℝ) ^ M := by
      rw [div_pow, one_pow] at *
      exact one_div_le_one_div_of_le (by positivity) (hbig M)
    have hnn : (0 : ℝ) ≤ 4 * Real.pi * |t| := by positivity
    have hLnn : (0 : ℝ) ≤ ((Nat.log 2 (p * M + M + 1) : ℝ) + 1)
        + ((Nat.log 2 (q * M + M + 1) : ℝ) + 1) := by positivity
    unfold peelBound
    calc 4 * Real.pi * |t| / (b : ℝ) ^ M
          * (((Nat.log 2 (p * M + M + 1) : ℝ) + 1) + ((Nat.log 2 (q * M + M + 1) : ℝ) + 1))
        = (4 * Real.pi * |t|) * (1 / (b : ℝ) ^ M)
          * (((Nat.log 2 (p * M + M + 1) : ℝ) + 1)
            + ((Nat.log 2 (q * M + M + 1) : ℝ) + 1)) := by ring
      _ ≤ (4 * Real.pi * |t|) * (1 / 2 : ℝ) ^ M * (((p : ℝ) + q + 4) * ((M : ℝ) + 1)) := by
          have h1 : (4 * Real.pi * |t|) * (1 / (b : ℝ) ^ M)
              ≤ (4 * Real.pi * |t|) * (1 / 2 : ℝ) ^ M := by nlinarith [hinv, hnn]
          have h2 : (0 : ℝ) ≤ (4 * Real.pi * |t|) * (1 / 2 : ℝ) ^ M := by positivity
          nlinarith [h1, h2, hL, hLnn]
      _ = C * ((M : ℝ) + 1) * (1 / 2 : ℝ) ^ M := by rw [hC]; ring
  have hzero : Tendsto (fun M : ℕ => C * ((M : ℝ) + 1) * (1 / 2 : ℝ) ^ M) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => (M : ℝ) * (1 / 2 : ℝ) ^ M) atTop (𝓝 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun M : ℕ => (1 / 2 : ℝ) ^ M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 : Tendsto (fun M : ℕ => C * ((M : ℝ) * (1 / 2 : ℝ) ^ M + (1 / 2 : ℝ) ^ M))
        atTop (𝓝 (C * (0 + 0))) := (h1.add h2).const_mul C
    rw [show (0 : ℝ) = C * (0 + 0) by ring]
    exact h3.congr fun M => by ring
  refine squeeze_zero (fun M => peelBound_nonneg b p q M M t hb) hmaj hzero

/-! ### The reduction is an EQUIVALENCE

`pairDecorr_of_unweighted` is not merely sufficient: the weight-removal bound is symmetric, so a
schedule meeting the budget makes the unweighted `2K(M)`-point correlation *equal* to the crux in
the limit.  Hence the fixed-pair leaf and the unweighted growing-depth Elliott correlation are the
SAME problem — no route lies strictly between them. -/

/-- The converse direction: the crux forces the unweighted means to vanish. -/
theorem multiElliottGrowing_of_pairDecorr (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K : ℕ → ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hbud : Tendsto (fun M => peelBound b p q (K M) M t) atTop (𝓝 0))
    (hcrux : PairDecorr b t) : MultiElliottGrowing b p q t K := by
  have hmain : Tendsto (fun M =>
      fullMean (fun n => phase (t * pairTail b p q n)) M) atTop (𝓝 0) := by
    simpa [pairTail] using hcrux p q hp hq hpq
  have hdiff : Tendsto (fun M =>
      fullMean (fun n => phase (t * digitTrunc b p q (K M) n)) M
        - fullMean (fun n => phase (t * pairTail b p q n)) M) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun M => norm_nonneg _)
      (Filter.Eventually.of_forall fun M => ?_) hbud
    rw [norm_sub_rev]
    exact norm_fullMean_sub_le b hb t p q (K M) M
  have hsum : Tendsto (fun M =>
      fullMean (fun n => phase (t * digitTrunc b p q (K M) n)) M) atTop (𝓝 0) := by
    have h0 := hdiff.add hmain
    rw [add_zero] at h0
    exact h0.congr fun M => by ring
  refine hsum.congr fun M => ?_
  refine congrArg (fun z => z / (M : ℂ)) (Finset.sum_congr rfl fun n _ => ?_)
  exact phase_digitTrunc b t p q (K M) n

/-- **THE WEIGHT-FREE SURFACE, AS AN EQUIVALENCE.**  For any depth schedule `K` meeting the
carry budget, the fixed-pair crux `PairDecorr b t` is *equivalent* to the vanishing of the
**unweighted** `2K(M)`-point root-of-unity correlations along `pn+1+k`, `qn+1+k`.

This is the honest statement of the route's depth: the leaf is neither weaker nor stronger than a
growing-length Elliott correlation for the completely multiplicative function `ζ^ω` — the object
Elliott's conjecture (and Tao 2016, MRT 2015 in their averaged/logarithmic forms) is about. -/
theorem pairDecorr_iff_unweighted (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K : ℕ → ℕ)
    (hbud : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun M => peelBound b p q (K M) M t) atTop (𝓝 0)) :
    PairDecorr b t ↔
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t K := by
  constructor
  · intro h p q hp hq hpq
    exact multiElliottGrowing_of_pairDecorr b hb t K hp hq hpq (hbud p q hp hq hpq) h
  · exact pairDecorr_of_unweighted b hb t K hbud

/-- The equivalence at the certified schedule `K(M) = M`. -/
theorem pairDecorr_iff_unweighted_id (b : ℕ) (hb : 2 ≤ b) (t : ℝ) :
    PairDecorr b t ↔
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t id :=
  pairDecorr_iff_unweighted b hb t id fun p q _ _ _ => tendsto_peelBound_id b hb p q t

end NormalNumbers.CastingOut
