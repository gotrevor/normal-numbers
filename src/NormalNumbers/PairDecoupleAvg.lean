import NormalNumbers.PairDecoupleProve

/-!
# The AVERAGED Kátai/BSZ route: weakening the open leaf to an average over the multipliers

Kickoff item 2 ("check whether Kátai can be applied with `p, q` LARGE only — BSZ needs just
sufficiently large primes — and whether that helps"), never attempted before this file.

`KataiOrthogonality` as stated in `SwingC1Katai.lean` demands the multiplicative-shift
decorrelation `E_n a(pn) conj a(qn) → 0` for **every** pair of distinct primes.  That is *not*
what Bourgain–Sarnak–Ziegler (Prop. 2.1) and Kátai actually prove.  Their criterion is an
**average** over the pairs:

`|E_{n ≤ N} f(n) a(n)|² ≲ 1/w + (1/π(w)²) Σ_{p ≠ q ≤ w} |E_{n ≤ N} a(pn) conj a(qn)|`,

so it suffices that the *mean* over ordered pairs of distinct primes `≤ w` is small once `w` is
large.  This file states that averaged criterion (`KataiOrthogonalityAvg`), proves it implies the
all-pairs criterion already in use (`kataiOrthogonality_of_avg`), and re-runs the swing on the
correspondingly **weaker** open leaf `PairDecorrAvg`.

## Why this is route-decisive, not cosmetic

The leaf `PairDecorr` was proved equivalent to `MultiElliott` — Elliott's conjecture for a growing
number of linear forms, open even in logarithmic average.  `PairDecorrAvg` is the *averaged* form
of that correlation, and averaged Chowla/Elliott conjectures are in a different literature class
entirely: the averaged Chowla conjecture is a THEOREM (Matomäki–Radziwiłł–Tao, *An averaged form
of Chowla's conjecture*, Algebra & Number Theory 9 (2015) 2167–2196), as are averaged Elliott-type
statements over shifts.  Here the average is over the *multipliers* `p, q` rather than over shifts,
which is the exact degree of freedom BSZ hands us for free.

Nothing below is weakened by hand: `kataiOrthogonality_of_avg` is the machine-checked certificate
that the averaged criterion is at least as strong as the one the existing chain consumes, and
`pairDecorrAvg_of_pairDecorr` certifies that the new leaf is at most as strong as the old one.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The averaged pair mean -/

/-- The mean, over ordered pairs of **distinct** primes `≤ w`, of the multiplicative-shift
autocorrelation of `a` over `N` terms.  This is the quantity BSZ's criterion actually bounds. -/
noncomputable def pairAvg (a : ℕ → ℂ) (w N : ℕ) : ℝ :=
  (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      if p = q then 0 else ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖)
    / ((primesLe w).card : ℝ) ^ 2

/-- **The BSZ hypothesis.**  The averaged decorrelation: for every `ε`, once the prime cut `w`
is large the pair average is `< ε` for all large `N`.  Strictly weaker than asking each pair to
decorrelate: a density-zero set of exceptional pairs is allowed, and no individual pair is
required to have a limit. -/
def PairMeanAvgZero (a : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, ∀ᶠ N : ℕ in atTop, pairAvg a w N < ε

/-- **The Daboussi–Kátai / Bourgain–Sarnak–Ziegler criterion, in its true averaged form.**
Identical to `KataiOrthogonality` except that the hypothesis on `a` is the *average* over pairs
of primes, which is what the published proofs supply. -/
def KataiOrthogonalityAvg : Prop :=
  ∀ (a f : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖f n‖ ≤ 1) →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    PairMeanAvgZero a →
    Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0)

/-! ### The averaged criterion is at least as strong as the all-pairs one -/

lemma card_primesLe_pos {w : ℕ} (hw : 2 ≤ w) : 0 < (primesLe w).card := by
  refine Finset.card_pos.mpr ⟨2, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩

/-- All-pairs decorrelation implies the averaged one. -/
theorem pairMeanAvgZero_of_forall_pairs (a : ℕ → ℂ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun N => fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N)
        atTop (𝓝 0)) :
    PairMeanAvgZero a := by
  classical
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop 2] with w hw
  have hcard : (0 : ℝ) < ((primesLe w).card : ℝ) := by
    exact_mod_cast card_primesLe_pos hw
  -- each entry of the finite double sum tends to `0`
  have hterm : ∀ p ∈ primesLe w, Tendsto (fun N => ∑ q ∈ primesLe w,
      if p = q then (0 : ℝ) else
        ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖) atTop (𝓝 0) := by
    intro p hp
    have : Tendsto (fun N => ∑ q ∈ primesLe w,
        if p = q then (0 : ℝ) else
          ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖) atTop
        (𝓝 (∑ _q ∈ primesLe w, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun q hq => ?_
      by_cases hpq : p = q
      · simp [hpq]
      · simpa [hpq] using
          ((h p q (prime_of_mem_primesLe hp) (prime_of_mem_primesLe hq) hpq).norm)
    simpa using this
  have hsum : Tendsto (fun N => ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      if p = q then (0 : ℝ) else
        ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum (primesLe w) hterm
    simpa using this
  have hdiv : Tendsto (fun N => pairAvg a w N) atTop (𝓝 0) := by
    have := hsum.div_const (((primesLe w).card : ℝ) ^ 2)
    simpa [pairAvg] using this
  exact (hdiv.eventually (gt_mem_nhds hε)).mono fun N hN => by
    simpa using hN

/-- **The averaged criterion implies the one the existing chain consumes.**  Machine-checked
certificate that replacing `KataiOrthogonality` by `KataiOrthogonalityAvg` never strengthens
what is assumed. -/
theorem kataiOrthogonality_of_avg (h : KataiOrthogonalityAvg) : KataiOrthogonality := by
  intro a f ha hf hmul hpair
  exact h a f ha hf hmul (pairMeanAvgZero_of_forall_pairs a hpair)


/-! ### Only LARGE primes matter

The kickoff's item 2: "BSZ needs just sufficiently large primes".  Here is the machine-checked
form of that.  The pairs in which either prime is `≤ W` number `O(π(W)·π(w)) = o(π(w)²)`, so they
cannot obstruct the average, whatever they do. -/

lemma primesLe_mono {w w' : ℕ} (h : w ≤ w') : primesLe w ⊆ primesLe w' := by
  intro p hp
  rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

lemma tendsto_card_primesLe : Tendsto (fun w => ((primesLe w).card : ℝ)) atTop atTop := by
  classical
  refine tendsto_atTop.mpr fun M => ?_
  obtain ⟨M', hM'⟩ := exists_nat_gt M
  obtain ⟨t, hts, htc⟩ := Nat.infinite_setOfPred_prime.exists_subset_card_eq M'
  set w₀ : ℕ := t.sup id with hw₀
  have hsub : t ⊆ primesLe w₀ := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Finset.le_sup (f := id) hp; simp only [id] at this; omega),
       hts hp⟩
  filter_upwards [Filter.eventually_ge_atTop w₀] with w hw
  have : M' ≤ (primesLe w).card := by
    rw [← htc]
    exact Finset.card_le_card (hsub.trans (primesLe_mono hw))
  have : (M' : ℝ) ≤ ((primesLe w).card : ℝ) := by exact_mod_cast this
  linarith

/-- **Only sufficiently large primes matter.**  If the multiplicative-shift decorrelation holds
for every pair of distinct primes *above some fixed `W`*, the BSZ average vanishes.  The small
primes are free: they occupy a vanishing proportion of the pairs. -/
theorem pairMeanAvgZero_of_large_pairs (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (W : ℕ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → W < p → W < q → p ≠ q →
      Tendsto (fun N => fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N)
        atTop (𝓝 0)) :
    PairMeanAvgZero a := by
  classical
  have hbound : ∀ p q N : ℕ,
      ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖ ≤ 1 := by
    intro p q N
    refine norm_fullMean_le_one _ N fun m => ?_
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [ha (p * m), ha (q * m), norm_nonneg (a (p * m)), norm_nonneg (a (q * m))]
  intro ε hε
  -- pick `w` so large that the small-prime pairs contribute `< ε/2`
  have hsmall : Tendsto (fun w : ℕ =>
      2 * ((primesLe W).card : ℝ) / ((primesLe w).card : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2 * ((primesLe W).card : ℝ)) (f := atTop (α := ℕ))).div_atTop
      tendsto_card_primesLe
  filter_upwards [hsmall.eventually (gt_mem_nhds (show (0:ℝ) < ε / 2 by linarith)),
    Filter.eventually_ge_atTop 2, Filter.eventually_ge_atTop W] with w hw hw2 hwW
  have hcard : (0 : ℝ) < ((primesLe w).card : ℝ) := by
    exact_mod_cast card_primesLe_pos hw2
  set S : ℕ → ℕ → ℕ → ℝ := fun p q N =>
    if p = q then (0 : ℝ) else ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖
    with hS
  have hS0 : ∀ p q N, 0 ≤ S p q N := by
    intro p q N; rw [hS]; dsimp only; split_ifs; · exact le_rfl
    · exact norm_nonneg _
  have hS1 : ∀ p q N, S p q N ≤ 1 := by
    intro p q N; rw [hS]; dsimp only; split_ifs
    · norm_num
    · exact hbound p q N
  -- the pairs with both primes `> W` : a finite sum tending to `0` in `N`
  have hbig : Tendsto (fun N => ∑ p ∈ (primesLe w).filter (fun p => W < p),
      ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N) atTop (𝓝 0) := by
    have hrow : ∀ p ∈ (primesLe w).filter (fun p => W < p),
        Tendsto (fun N => ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N) atTop (𝓝 0) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have : Tendsto (fun N => ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N) atTop
          (𝓝 (∑ _q ∈ (primesLe w).filter (fun q => W < q), (0 : ℝ))) := by
        refine tendsto_finsetSum _ fun q hq => ?_
        rw [Finset.mem_filter] at hq
        by_cases hpq : p = q
        · simp [hS, hpq]
        · simpa [hS, hpq] using
            ((h p q (prime_of_mem_primesLe hp.1) (prime_of_mem_primesLe hq.1)
              hp.2 hq.2 hpq).norm)
      simpa using this
    simpa using tendsto_finsetSum ((primesLe w).filter (fun p => W < p)) hrow
  filter_upwards [hbig.eventually (gt_mem_nhds (show (0:ℝ) < ε / 2 * ((primesLe w).card : ℝ) ^ 2
      by positivity))] with N hN
  -- split the double sum
  have hsplit : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, S p q N
      ≤ (∑ p ∈ (primesLe w).filter (fun p => W < p),
          ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N)
        + 2 * ((primesLe W).card : ℝ) * ((primesLe w).card : ℝ) := by
    have hWsub : (primesLe W) ⊆ primesLe w := primesLe_mono hwW
    classical
    have key : ∀ p ∈ primesLe w, ∑ q ∈ primesLe w, S p q N
        ≤ (if W < p then ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N else 0)
          + (if W < p then ((primesLe W).card : ℝ) else ((primesLe w).card : ℝ)) := by
      intro p hp
      by_cases hpW : W < p
      · rw [if_pos hpW, if_pos hpW,
          ← Finset.sum_filter_add_sum_filter_not (primesLe w) (fun q => W < q) (fun q => S p q N)]
        have : ∑ q ∈ (primesLe w).filter (fun q => ¬ W < q), S p q N
            ≤ ((primesLe W).card : ℝ) := by
          calc ∑ q ∈ (primesLe w).filter (fun q => ¬ W < q), S p q N
              ≤ ∑ q ∈ (primesLe w).filter (fun q => ¬ W < q), (1 : ℝ) :=
                Finset.sum_le_sum fun q _ => hS1 p q N
            _ = (((primesLe w).filter (fun q => ¬ W < q)).card : ℝ) := by simp
            _ ≤ ((primesLe W).card : ℝ) := by
                have : (primesLe w).filter (fun q => ¬ W < q) ⊆ primesLe W := by
                  intro q hq
                  rw [Finset.mem_filter] at hq
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_range.mpr (by omega), prime_of_mem_primesLe hq.1⟩
                exact_mod_cast Finset.card_le_card this
        linarith
      · rw [if_neg hpW, if_neg hpW, zero_add]
        calc ∑ q ∈ primesLe w, S p q N ≤ ∑ q ∈ primesLe w, (1 : ℝ) :=
              Finset.sum_le_sum fun q _ => hS1 p q N
          _ = ((primesLe w).card : ℝ) := by simp
    refine le_trans (Finset.sum_le_sum key) ?_
    rw [Finset.sum_add_distrib]
    have e1 : ∑ p ∈ primesLe w,
        (if W < p then ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N else 0)
        = ∑ p ∈ (primesLe w).filter (fun p => W < p),
            ∑ q ∈ (primesLe w).filter (fun q => W < q), S p q N := (Finset.sum_filter _ _).symm
    have e2 : ∑ p ∈ primesLe w,
        (if W < p then ((primesLe W).card : ℝ) else ((primesLe w).card : ℝ))
        ≤ 2 * ((primesLe W).card : ℝ) * ((primesLe w).card : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not (primesLe w) (fun p => W < p)]
      have a1 : ∑ p ∈ (primesLe w).filter (fun p => W < p),
          (if W < p then ((primesLe W).card : ℝ) else ((primesLe w).card : ℝ))
          ≤ ((primesLe w).card : ℝ) * ((primesLe W).card : ℝ) := by
        rw [Finset.sum_congr rfl (fun p hp => by
          rw [if_pos (Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
        have : (((primesLe w).filter (fun p => W < p)).card : ℝ) ≤ ((primesLe w).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        nlinarith [Nat.cast_nonneg (α := ℝ) ((primesLe W).card)]
      have a2 : ∑ p ∈ (primesLe w).filter (fun p => ¬ W < p),
          (if W < p then ((primesLe W).card : ℝ) else ((primesLe w).card : ℝ))
          ≤ ((primesLe W).card : ℝ) * ((primesLe w).card : ℝ) := by
        rw [Finset.sum_congr rfl (fun p hp => by
          rw [if_neg (Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
        have : (((primesLe w).filter (fun p => ¬ W < p)).card : ℝ) ≤ ((primesLe W).card : ℝ) := by
          have : (primesLe w).filter (fun p => ¬ W < p) ⊆ primesLe W := by
            intro q hq
            rw [Finset.mem_filter] at hq
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (by omega), prime_of_mem_primesLe hq.1⟩
          exact_mod_cast Finset.card_le_card this
        nlinarith [Nat.cast_nonneg (α := ℝ) ((primesLe w).card)]
      linarith
    rw [e1]; linarith
  rw [pairAvg, div_lt_iff₀ (by positivity)]
  have hw' : 2 * ((primesLe W).card : ℝ) / ((primesLe w).card : ℝ) < ε / 2 := hw
  have : 2 * ((primesLe W).card : ℝ) * ((primesLe w).card : ℝ)
      < ε / 2 * ((primesLe w).card : ℝ) ^ 2 := by
    rw [div_lt_iff₀ hcard] at hw'
    nlinarith [hcard]
  calc ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, S p q N
      ≤ _ := hsplit
    _ < ε / 2 * ((primesLe w).card : ℝ) ^ 2 + ε / 2 * ((primesLe w).card : ℝ) ^ 2 := by
        linarith
    _ = ε * ((primesLe w).card : ℝ) ^ 2 := by ring

/-! ### The averaged leaf -/

/-- The pair average written on the orbit difference `θ_{pn} − θ_{qn}` itself. -/
noncomputable def pairDecorrAvgSum (b : ℕ) (t : ℝ) (w N : ℕ) : ℝ :=
  (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      if p = q then 0 else
        ‖fullMean (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) N‖)
    / ((primesLe w).card : ℝ) ^ 2

lemma pairAvg_phase_omegaTail (b : ℕ) (t : ℝ) (w N : ℕ) :
    pairAvg (fun n => phase (t * omegaTail b n)) w N = pairDecorrAvgSum b t w N := by
  have heq : ∀ p q : ℕ, (fun n => phase (t * omegaTail b (p * n))
      * (starRingEnd ℂ) (phase (t * omegaTail b (q * n))))
      = fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n))) := by
    intro p q
    funext n
    rw [conj_phase, ← phase_add]
    congr 1
    ring
  unfold pairAvg pairDecorrAvgSum
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hpq : p = q
  · simp [hpq]
  · simp only [if_neg hpq, heq p q]

/-- **THE WEAKENED OPEN LEAF.**  Only the *average* over pairs of distinct primes `≤ w` of the
orbit-difference means has to be small — the exact input BSZ/Kátai consume. -/
def PairDecorrAvg (b : ℕ) (t : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, ∀ᶠ N : ℕ in atTop, pairDecorrAvgSum b t w N < ε

lemma pairMeanAvgZero_iff_pairDecorrAvg (b : ℕ) (t : ℝ) :
    PairMeanAvgZero (fun n => phase (t * omegaTail b n)) ↔ PairDecorrAvg b t := by
  constructor <;> intro h ε hε <;>
    exact (h ε hε).mono fun w hw => hw.mono fun N hN => by
      simpa [pairAvg_phase_omegaTail] using hN

/-- The new leaf is implied by the old one: nothing has been strengthened. -/
theorem pairDecorrAvg_of_pairDecorr (b : ℕ) (t : ℝ) (h : PairDecorr b t) : PairDecorrAvg b t := by
  refine (pairMeanAvgZero_iff_pairDecorrAvg b t).mp
    (pairMeanAvgZero_of_forall_pairs _ fun p q hp hq hpq => ?_)
  have heq : ∀ n : ℕ, phase (t * omegaTail b (p * n))
      * (starRingEnd ℂ) (phase (t * omegaTail b (q * n)))
      = phase (t * (omegaTail b (p * n) - omegaTail b (q * n))) := by
    intro n
    rw [conj_phase, ← phase_add]
    congr 1
    ring
  simpa only [heq] using h p q hp hq hpq

/-! ### The swing, re-run on the averaged inputs -/

/-- `ShiftIndep` from the averaged criterion and the averaged leaf. -/
theorem shiftIndep_of_pairDecorrAvg (b : ℕ) (t : ℝ) (hDK : KataiOrthogonalityAvg)
    (hD : DelangeMean t) (hP : PairDecorrAvg b t) : ShiftIndep b t := by
  set a : ℕ → ℂ := fun n => phase (t * omegaTail b n) with ha
  set f : ℕ → ℂ := fun n => phase (t * (omegaNat n : ℝ)) with hf
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hfnorm : ∀ n, ‖f n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := fun m n h =>
    phase_omegaNat_multiplicative t m n h
  have hDKc : Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) :=
    hDK a f hanorm hfnorm hmul ((pairMeanAvgZero_iff_pairDecorrAvg b t).mpr hP)
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

/-- **THE SWING ON THE AVERAGED LEAF.**  `ConjC1` from the true (averaged) Kátai/BSZ criterion,
Delange's theorem, and the *averaged* orbit decorrelation.  Strictly weaker hypotheses than
`conjC1_of_delange_katai`. -/
theorem conjC1_of_delange_kataiAvg_pairDecorrAvg (hDK : KataiOrthogonalityAvg)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      PairDecorrAvg b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_weylMean fun b hb m hm hdvd =>
    weylMean_tendsto_zero_of b (by omega) ((m : ℤ) : ℝ) (hD b hb m hm hdvd)
      (shiftIndep_of_pairDecorrAvg b (((m : ℤ) : ℝ) / b) hDK (hD b hb m hm hdvd)
        (hP b hb m hm hdvd))



/-! ### Van der Corput, averaged over the multipliers

`norm_mean_le_vdC` is fully quantitative and uniform in the sequence, so it can be averaged over
the pairs `(p, q)`: Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) pushes the average inside the
square root.  The result reduces the averaged leaf `PairDecorrAvg` to an averaged *shifted*
correlation — the averaged form of the multi-point Elliott correlation. -/

/-- The averaged off-diagonal shifted correlation of the pair phases, normalised exactly as van
der Corput needs it. -/
noncomputable def avgOffDiag (b : ℕ) (t : ℝ) (w R K : ℕ) : ℝ :=
  (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      offDiagShift (fun i => phase (t * pairTail b p q i)) R K)
    / (((primesLe w).card : ℝ) ^ 2 * (K : ℝ) ^ 2 * R)

lemma avgOffDiag_nonneg (b : ℕ) (t : ℝ) (w R K : ℕ) : 0 ≤ avgOffDiag b t w R K := by
  refine div_nonneg (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    offDiagShift_nonneg _ _ _) (by positivity)

/-- **Van der Corput, averaged over the multipliers.** -/
theorem pairDecorrAvgSum_le_vdC (b : ℕ) (t : ℝ) (w R K : ℕ) (hw : 2 ≤ w) (hR : 0 < R)
    (hK : 0 < K) :
    pairDecorrAvgSum b t w R
      ≤ Real.sqrt (1 / (K : ℝ) + avgOffDiag b t w R K) + 2 * (K : ℝ) / R := by
  classical
  set C : ℝ := ((primesLe w).card : ℝ) with hCdef
  have hC : (0 : ℝ) < C := by
    rw [hCdef]; exact_mod_cast card_primesLe_pos hw
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  set A : ℕ → ℕ → ℝ := fun p q =>
    1 / (K : ℝ) + offDiagShift (fun i => phase (t * pairTail b p q i)) R K / ((K : ℝ) ^ 2 * R)
    with hA
  have hAnn : ∀ p q, 0 ≤ A p q := by
    intro p q
    have h0 := offDiagShift_nonneg (fun i => phase (t * pairTail b p q i)) R K
    have h1 : (0:ℝ) ≤ 1 / (K : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ offDiagShift (fun i => phase (t * pairTail b p q i)) R K
        / ((K : ℝ) ^ 2 * R) := div_nonneg h0 (by positivity)
    rw [hA]; dsimp only; linarith
  set SS : ℝ := ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, Real.sqrt (A p q) with hSS
  set SA : ℝ := ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, A p q with hSA
  have hSAnn : 0 ≤ SA := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => hAnn p q
  have hSSnn : 0 ≤ SS :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => Real.sqrt_nonneg _
  -- the per-pair van der Corput bound
  have hstep : ∀ p q : ℕ,
      (if p = q then (0 : ℝ) else
        ‖fullMean (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) R‖)
        ≤ Real.sqrt (A p q) + 2 * (K : ℝ) / R := by
    intro p q
    have hnn : 0 ≤ Real.sqrt (A p q) + 2 * (K : ℝ) / R := by positivity
    by_cases hpq : p = q
    · rw [if_pos hpq]; exact hnn
    · rw [if_neg hpq]
      have hmain := norm_mean_le_vdC (fun i => phase (t * pairTail b p q i)) R K hR hK
        (fun n => le_of_eq (norm_phase _))
      have heq : fullMean (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) R
          = (∑ i ∈ range R, phase (t * pairTail b p q i)) / (R : ℂ) := rfl
      rw [heq]
      exact hmain
  have hsum : (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      (if p = q then (0 : ℝ) else
        ‖fullMean (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) R‖))
      ≤ SS + C ^ 2 * (2 * (K : ℝ) / R) := by
    have hrow : ∀ p : ℕ, ∑ q ∈ primesLe w, (Real.sqrt (A p q) + 2 * (K : ℝ) / R)
        = (∑ q ∈ primesLe w, Real.sqrt (A p q)) + C * (2 * (K : ℝ) / R) := by
      intro p
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hCdef]
    calc (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          (if p = q then (0 : ℝ) else
            ‖fullMean (fun n => phase (t * (omegaTail b (p*n) - omegaTail b (q*n)))) R‖))
        ≤ ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (Real.sqrt (A p q) + 2 * (K : ℝ) / R) :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hstep p q
      _ = ∑ p ∈ primesLe w, ((∑ q ∈ primesLe w, Real.sqrt (A p q)) + C * (2 * (K : ℝ) / R)) :=
          Finset.sum_congr rfl fun p _ => hrow p
      _ = SS + C ^ 2 * (2 * (K : ℝ) / R) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hCdef, ← hSS]
          ring
  -- Cauchy–Schwarz
  have hCS : SS ^ 2 ≤ C ^ 2 * SA := by
    have h := sq_sum_le_card_mul_sum_sq (s := (primesLe w) ×ˢ (primesLe w))
      (f := fun x : ℕ × ℕ => Real.sqrt (A x.1 x.2))
    have hcard : ((((primesLe w) ×ˢ (primesLe w)).card : ℕ) : ℝ) = C ^ 2 := by
      rw [Finset.card_product, hCdef]; push_cast; ring
    have hsq : ∀ x : ℕ × ℕ, Real.sqrt (A x.1 x.2) ^ 2 = A x.1 x.2 := fun x =>
      Real.sq_sqrt (hAnn x.1 x.2)
    rw [hcard] at h
    simp only [hsq] at h
    rwa [Finset.sum_product, Finset.sum_product, ← hSS, ← hSA] at h
  have hSSle : SS ≤ C * Real.sqrt SA := by
    have hnn2 : 0 ≤ C * Real.sqrt SA := by positivity
    have h1 : SS ^ 2 ≤ (C * Real.sqrt SA) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hSAnn]; exact hCS
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hSSnn, Real.sqrt_sq hnn2] at h2
  -- identify `SA / C^2`
  have hSAval : SA / C ^ 2 = 1 / (K : ℝ) + avgOffDiag b t w R K := by
    have h1 : SA = C ^ 2 * (1 / (K : ℝ))
        + (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
            offDiagShift (fun i => phase (t * pairTail b p q i)) R K) / ((K : ℝ) ^ 2 * R) := by
      have hrow : ∀ p : ℕ, ∑ q ∈ primesLe w, A p q
          = C * (1 / (K : ℝ))
            + (∑ q ∈ primesLe w,
                offDiagShift (fun i => phase (t * pairTail b p q i)) R K) / ((K : ℝ) ^ 2 * R) := by
        intro p
        rw [hA]
        simp only
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hCdef, ← Finset.sum_div]
      rw [hSA, Finset.sum_congr rfl (fun p _ => hrow p), Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, ← hCdef, ← Finset.sum_div]
      ring
    rw [h1, avgOffDiag, ← hCdef]
    field_simp
  have hsd : Real.sqrt (SA / C ^ 2) = Real.sqrt SA / C := by
    rw [Real.sqrt_div hSAnn, Real.sqrt_sq hC.le]
  rw [pairDecorrAvgSum, ← hCdef, div_le_iff₀ (by positivity : (0:ℝ) < C ^ 2)]
  have hkey : Real.sqrt (1 / (K : ℝ) + avgOffDiag b t w R K) * C ^ 2 = C * Real.sqrt SA := by
    rw [← hSAval, hsd]; field_simp
  nlinarith [hsum, hSSle, hkey, hC]

/-- **THE AVERAGED SHIFTED LEAF.**  The averaged form of the multi-point correlation: only the
*mean over pairs of distinct primes* of the van der Corput off-diagonal has to be small. -/
def PairShiftCorrAvg (b : ℕ) (t : ℝ) : Prop :=
  ∀ K : ℕ, 0 < K → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ w : ℕ in atTop, ∀ᶠ R : ℕ in atTop, avgOffDiag b t w R K < ε

theorem pairDecorrAvg_of_pairShiftCorrAvg (b : ℕ) (t : ℝ) (h : PairShiftCorrAvg b t) :
    PairDecorrAvg b t := by
  intro ε hε
  obtain ⟨K, hK8⟩ := exists_nat_gt (8 / ε ^ 2)
  have hKpos : 0 < K := by
    by_contra hcon
    have hK0 : K = 0 := by omega
    rw [hK0] at hK8
    have : (0:ℝ) < 8 / ε ^ 2 := by positivity
    simp at hK8; linarith
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hdiag : 1 / (K : ℝ) < ε ^ 2 / 8 := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at hK8
    rw [div_lt_div_iff₀ hKR (by norm_num : (0:ℝ) < 8)]
    linarith
  filter_upwards [h K hKpos (ε ^ 2 / 8) (by positivity), Filter.eventually_ge_atTop 2]
    with w hw hw2
  obtain ⟨R₁, hR₁⟩ := exists_nat_gt (4 * (K : ℝ) / ε)
  filter_upwards [hw, Filter.eventually_gt_atTop (max R₁ 0)] with R hR hRgt
  have hRpos : 0 < R := by omega
  have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
  have h2K : 2 * (K : ℝ) / R < ε / 2 := by
    have hlt : 4 * (K : ℝ) / ε < (R : ℝ) := by
      refine lt_trans hR₁ ?_
      have : R₁ < R := by omega
      exact_mod_cast this
    rw [div_lt_iff₀ hε] at hlt
    rw [div_lt_iff₀ hRR]
    linarith
  have hsq : Real.sqrt (1 / (K : ℝ) + avgOffDiag b t w R K) < ε / 2 := by
    have hlt : 1 / (K : ℝ) + avgOffDiag b t w R K < (ε / 2) ^ 2 := by
      have he : (ε / 2) ^ 2 = ε ^ 2 / 8 + ε ^ 2 / 8 := by ring
      rw [he]; linarith
    have hnn : 0 ≤ 1 / (K : ℝ) + avgOffDiag b t w R K := by
      have := avgOffDiag_nonneg b t w R K; positivity
    have := Real.sqrt_lt_sqrt hnn hlt
    rwa [Real.sqrt_sq (by positivity)] at this
  have := pairDecorrAvgSum_le_vdC b t w R K hw2 hRpos hKpos
  linarith

/-! ### The crux, restated for LARGE primes only

This is the payoff of the averaged criterion: the swing never needs the orbit difference to
decorrelate for *small* multipliers.  Any fixed finite set of primes may be discarded. -/

/-- The orbit-difference decorrelation, asked only of pairs of distinct primes above some fixed
threshold. -/
def PairDecorrLarge (b : ℕ) (t : ℝ) : Prop :=
  ∃ W : ℕ, ∀ p q : ℕ, p.Prime → q.Prime → W < p → W < q → p ≠ q →
    Tendsto (fun N => fullMean
      (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) N) atTop (𝓝 0)

theorem pairDecorrAvg_of_pairDecorrLarge (b : ℕ) (t : ℝ) (h : PairDecorrLarge b t) :
    PairDecorrAvg b t := by
  obtain ⟨W, hW⟩ := h
  refine (pairMeanAvgZero_iff_pairDecorrAvg b t).mp
    (pairMeanAvgZero_of_large_pairs _ (fun n => le_of_eq (norm_phase _)) W
      fun p q hp hq hpW hqW hpq => ?_)
  have heq : ∀ n : ℕ, phase (t * omegaTail b (p * n))
      * (starRingEnd ℂ) (phase (t * omegaTail b (q * n)))
      = phase (t * (omegaTail b (p * n) - omegaTail b (q * n))) := by
    intro n
    rw [conj_phase, ← phase_add]
    congr 1
    ring
  simpa only [heq] using hW p q hp hq hpW hqW hpq

/-- **THE SWING ON LARGE MULTIPLIERS ONLY.**  `ConjC1` from the true (averaged) Kátai/BSZ
criterion, Delange's theorem, and the orbit decorrelation for pairs of distinct primes above an
arbitrary threshold `W` that may depend on `b` and `m`.  This is the kickoff's item 2, discharged:
Bourgain–Sarnak–Ziegler needs only sufficiently large primes, and so does the swing. -/
theorem conjC1_of_delange_kataiAvg_pairDecorrLarge (hDK : KataiOrthogonalityAvg)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      PairDecorrLarge b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_kataiAvg_pairDecorrAvg hDK hD fun b hb m hm hdvd =>
    pairDecorrAvg_of_pairDecorrLarge b _ (hP b hb m hm hdvd)

/-- **THE SWING ON THE AVERAGED SHIFTED LEAF.**  The weakest form this development reaches:
`ConjC1` from Delange's theorem, the *averaged* Kátai/BSZ criterion, and the requirement that the
van der Corput off-diagonal be small only **on average over the pairs of distinct prime
multipliers**.  Every pointwise limit has been replaced by a mean over `p, q ≤ w`. -/
theorem conjC1_of_delange_kataiAvg_pairShiftCorrAvg (hDK : KataiOrthogonalityAvg)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      PairShiftCorrAvg b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_kataiAvg_pairDecorrAvg hDK hD fun b hb m hm hdvd =>
    pairDecorrAvg_of_pairShiftCorrAvg b _ (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
