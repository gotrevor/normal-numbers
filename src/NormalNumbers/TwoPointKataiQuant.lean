import NormalNumbers.TwoPointGrowing

/-!
# The quantitative Kátai/BSZ criterion with a growing cutoff

Kickoff item 2.  `KataiOrthogonalityAvg` (`PairDecoupleAvg.lean`) is stated qualitatively, with
the prime cut `w` quantified *before* `N`.  What Bourgain–Sarnak–Ziegler (Prop. 2.1) and Kátai
actually prove is a **quantitative inequality**, valid for every `w` and `N` at once:

    |E_{n<N} f(n) a(n)|²  ≲  1/log log w  +  avg_{p ≠ q ≤ w} |E_{n<N} a(pn) conj a(qn)|,

for `|f| ≤ 1` multiplicative on coprimes and `|a| ≤ 1` (the `1/log log w` being `(Σ_{p≤w} 1/p)^{-1}`
by Mertens; the truncation error, of size `O(w/N)`, is absorbed by asking `w² ≤ N`).  Because the
inequality holds for all `(w, N)` simultaneously, it may be run along a **diagonal** `w = w(N)`
growing with `N` — which is the whole point of the re-plumb: an average over dilations that grows
with `N` is the regime where MRT-style averaging and the large sieve in the multiplier have room,
whereas a fixed finite pair set gives them none.

This file states the quantitative inequality (`KataiQuant`) and proves the wiring: the
quantitative inequality plus a *slowly growing* pair average gives the Kátai conclusion.  The
inequality itself is Cauchy–Schwarz + Turán–Kubilius and is the named open obligation
`KataiQuant`, cited exactly as `KataiOrthogonalityAvg` is.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **The quantitative Kátai/BSZ inequality** (Kátai; Bourgain–Sarnak–Ziegler Prop. 2.1).
Uniform in `w` and `N`, hence usable along a diagonal `w = w(N)`. -/
def KataiQuant : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a f : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖f n‖ ≤ 1) →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ w N : ℕ, 2 ≤ w → ((w : ℝ)) ^ 2 ≤ (N : ℝ) →
      ‖fullMean (fun n => f n * a n) N‖ ^ 2
        ≤ C * (1 / Real.log (Real.log w) + pairAvg a w N)

/-- **The growing-`w` pair average.**  The cut grows with `N`, slowly enough (`w² ≤ N`) for the
truncation error in the Kátai inequality to be harmless. -/
def PairMeanAvgZeroSlowGrowing (a : ℕ → ℂ) : Prop :=
  ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
    (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
    Tendsto (fun N => pairAvg a (w N) N) atTop (𝓝 0)

lemma tendsto_one_div_logLog {w : ℕ → ℕ} (hw : Tendsto w atTop atTop) :
    Tendsto (fun N => 1 / Real.log (Real.log (w N))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => ((w N : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hw
  have h2 : Tendsto (fun N => Real.log (Real.log (w N))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  simpa [Pi.inv_def] using h2.inv_tendsto_atTop

/-- **THE RE-PLUMB.**  The quantitative inequality, run along a slowly growing cutoff, gives the
Kátai conclusion from an average over a pair set that grows with `N`. -/
theorem tendsto_fullMean_of_kataiQuant (hQ : KataiQuant) (a f : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    (hP : PairMeanAvgZeroSlowGrowing a) :
    Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) := by
  obtain ⟨C, hC, hineq⟩ := hQ
  obtain ⟨w, hw, hslow, hpair⟩ := hP
  set M : ℕ → ℂ := fun N => fullMean (fun n => f n * a n) N with hM
  -- the majorant tends to `0`
  have hmaj : Tendsto (fun N => C * (1 / Real.log (Real.log (w N)) + pairAvg a (w N) N))
      atTop (𝓝 0) := by
    have := ((tendsto_one_div_logLog hw).add hpair).const_mul C
    simpa using this
  have hsq : Tendsto (fun N => ‖M N‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) ?_ hmaj
    filter_upwards [hslow] with N hN
    exact hineq a f ha hf hmul (w N) N hN.1 hN.2
  have : Tendsto (fun N => Real.sqrt (‖M N‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hsq.sqrt
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact this.congr fun N => Real.sqrt_sq (norm_nonneg _)


/-! ### The swing, re-run on the growing-`w` leaf -/

lemma pairMeanAvgZeroSlowGrowing_of_twoPoint (b : ℕ) (hb : 2 ≤ b) (t : ℝ)
    (h : TwoPointWeightedAvgSlowGrowing b t) :
    PairMeanAvgZeroSlowGrowing (fun n => phase (t * omegaTail b n)) := by
  obtain ⟨w, h1, h2, h3⟩ := h
  refine ⟨w, h1, h2, h3.congr fun N => ?_⟩
  rw [pairAvg_phase_omegaTail, pairDecorrAvgSum_eq_twoPointAvgSum b hb]

/-- `ShiftIndep` from the QUANTITATIVE Kátai criterion and the growing-`w` leaf. -/
theorem shiftIndep_of_kataiQuant (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (hQ : KataiQuant)
    (hD : DelangeMean t) (hP : TwoPointWeightedAvgSlowGrowing b t) : ShiftIndep b t := by
  set a : ℕ → ℂ := fun n => phase (t * omegaTail b n) with ha
  set f : ℕ → ℂ := fun n => phase (t * (omegaNat n : ℝ)) with hf
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hfnorm : ∀ n, ‖f n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := fun m n h =>
    phase_omegaNat_multiplicative t m n h
  have hDKc : Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) :=
    tendsto_fullMean_of_kataiQuant hQ a f hanorm hfnorm hmul
      (pairMeanAvgZeroSlowGrowing_of_twoPoint b hb t hP)
  have hshift : Tendsto (fun N => fullMean (fun n => f (n + 1) * a (n + 1)) N) atTop (𝓝 0) :=
    tendsto_fullMean_shift (g := fun n => f n * a n)
      (fun n => by rw [norm_mul]; nlinarith [hfnorm n, hanorm n, norm_nonneg (f n),
        norm_nonneg (a n)]) hDKc
  set A : ℕ → ℂ := fun n => phase (t * (omegaNat (n + 1) : ℝ)) with hA
  set B : ℕ → ℂ := fun n => phase (t * omegaTail b (n + 1)) with hB
  have hBnorm : ∀ N, ‖fullMean B N‖ ≤ 1 := fun N =>
    norm_fullMean_le_one B N (fun m => le_of_eq (norm_phase _))
  have hprod : Tendsto (fun N => (fullMean A N) * (fullMean B N)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp hD) ε hε] with N hN
    calc ‖(fullMean A N) * (fullMean B N)‖ = ‖fullMean A N‖ * ‖fullMean B N‖ := norm_mul _ _
      _ ≤ ‖fullMean A N‖ * 1 := by
          nlinarith [hBnorm N, norm_nonneg (fullMean A N), norm_nonneg (fullMean B N)]
      _ = ‖fullMean A N‖ := by ring
      _ < ε := hN
  have hfin := hshift.sub hprod
  rw [sub_zero] at hfin
  exact hfin

/-- **THE RE-PLUMBED SWING.**  `ConjC1` from Delange's theorem, the *quantitative* Kátai/BSZ
inequality, and a pair average over a cutoff `w(N)` that grows WITH `N`.  This is the route the
bet's kickoff item 2 asked for: the open leaf now lives in the growing-dilation regime. -/
theorem conjC1_of_delange_kataiQuant_twoPointSlowGrowing (hQ : KataiQuant)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      TwoPointWeightedAvgSlowGrowing b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_weylMean fun b hb m hm hdvd =>
    weylMean_tendsto_zero_of b (by omega) ((m : ℤ) : ℝ) (hD b hb m hm hdvd)
      (shiftIndep_of_kataiQuant b (by omega) (((m : ℤ) : ℝ) / b) hQ (hD b hb m hm hdvd)
        (hP b hb m hm hdvd))

/-- The ratified headline still feeds the re-plumbed swing: nothing was strengthened. -/
theorem conjC1_of_delange_kataiQuant_twoPointWeightedAvg (hQ : KataiQuant)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      TwoPointWeightedAvg b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_kataiQuant_twoPointSlowGrowing hQ hD fun b hb m hm hdvd =>
    twoPointWeightedAvgSlowGrowing_of_twoPointWeightedAvg b _ (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
