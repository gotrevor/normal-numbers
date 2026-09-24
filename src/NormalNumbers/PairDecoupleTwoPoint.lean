import NormalNumbers.PairDecoupleOneDigit

/-!
# Splitting the `K = 1` leaf: a PUBLISHED theorem plus a decoupling

Lap 24–25 put the crux in the exact form

`E_{n<R} ζ^{ω(pn+1)} · conj(ζ^{ω(qn+1)}) · W(n) → 0`,   `ζ = e(t/b)`, `W = peelWeight`,

with `W` unit-modulus and depending on `ω` at the arguments `pn+1+k`, `qn+1+k` for `k ≥ 1` only —
*disjoint* from the arguments `pn+1`, `qn+1` that the two-point factor sees.

This file splits that single statement into two independent obligations:

* `TwoPointElliott b p q t` — the **unweighted** two-point correlation
  `E_{n<R} ζ^{ω(pn+1)} conj(ζ^{ω(qn+1)}) → 0`.  For non-pretentious `ζ^ω` and two distinct
  multipliers this is exactly the theorem of Tao, *The logarithmically averaged Chowla and
  Elliott conjectures for two-point correlations*, Forum of Mathematics Pi **4** (2016) — the one
  published result the directive identifies as able to close this route.
* `WeightDecouple b p q t` — the leading digit decouples from the rest of the tail: the mean of
  the product is asymptotically the product of the means.

Neither is implied by the other and together they give the crux (`twoPointWeighted_of_split`), so
this is an honest decomposition rather than a restatement.  It isolates exactly what has to be
added to a published theorem.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The unweighted two-point factor of the peel: `ζ^{ω(pn+1)}·conj(ζ^{ω(qn+1)})`. -/
noncomputable def twoPointFactor (b p q : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  phase (t / b) ^ omegaNat (p * n + 1)
    * (starRingEnd ℂ) (phase (t / b) ^ omegaNat (q * n + 1))

lemma norm_twoPointFactor (b p q : ℕ) (t : ℝ) (n : ℕ) : ‖twoPointFactor b p q t n‖ = 1 := by
  simp [twoPointFactor, norm_mul, norm_pow, norm_phase]

/-- **Tao 2016's statement, as a named hypothesis.**  The two-point correlation of the
non-pretentious multiplicative function `ζ^ω` along the distinct forms `pn+1`, `qn+1`. -/
def TwoPointElliott (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun R => fullMean (twoPointFactor b p q t) R) atTop (𝓝 0)

/-- **The decoupling obligation.**  The leading digit of the pair difference is asymptotically
independent of the rest of the tail: the mean of the product is the product of the means. -/
def WeightDecouple (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun R =>
      fullMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) R
        - fullMean (twoPointFactor b p q t) R * fullMean (peelWeight b p q t) R)
    atTop (𝓝 0)

/-- **The `K = 1` leaf splits.**  A published two-point theorem plus a decoupling. -/
theorem twoPointWeighted_of_split (b p q : ℕ) (t : ℝ)
    (hE : TwoPointElliott b p q t) (hW : WeightDecouple b p q t) :
    TwoPointWeighted b p q t := by
  have hWnorm : ∀ R, ‖fullMean (peelWeight b p q t) R‖ ≤ 1 := fun R =>
    norm_fullMean_le_one _ R (fun m => le_of_eq (norm_peelWeight b p q t m))
  have hprod : Tendsto (fun R =>
      fullMean (twoPointFactor b p q t) R * fullMean (peelWeight b p q t) R) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp hE) ε hε] with R hR
    calc ‖fullMean (twoPointFactor b p q t) R * fullMean (peelWeight b p q t) R‖
        = ‖fullMean (twoPointFactor b p q t) R‖ * ‖fullMean (peelWeight b p q t) R‖ :=
          norm_mul _ _
      _ ≤ ‖fullMean (twoPointFactor b p q t) R‖ * 1 := by
          nlinarith [hWnorm R, norm_nonneg (fullMean (twoPointFactor b p q t) R),
            norm_nonneg (fullMean (peelWeight b p q t) R)]
      _ = ‖fullMean (twoPointFactor b p q t) R‖ := by ring
      _ < ε := hR
  have hsum := hW.add hprod
  rw [zero_add] at hsum
  refine hsum.congr fun R => ?_
  simp only [twoPointFactor]
  ring

/-- **THE CRUX, SPLIT.**  `PairDecorr` from the two-point Elliott correlation (Tao 2016) plus the
leading-digit decoupling, for every pair of distinct primes. -/
theorem pairDecorr_of_split (b : ℕ) (hb : 2 ≤ b) (t : ℝ)
    (hE : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → TwoPointElliott b p q t)
    (hW : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → WeightDecouple b p q t) :
    PairDecorr b t := by
  refine (pairDecorr_iff_twoPointWeighted b hb t).mpr fun p q hp hq hpq => ?_
  exact twoPointWeighted_of_split b p q t (hE p q hp hq hpq) (hW p q hp hq hpq)

/-- **The swing, on a published theorem plus one decoupling.**  Every hypothesis here is either a
theorem of the literature (`KataiOrthogonality`, `DelangeMean`, `TwoPointElliott`) or the single
remaining decoupling `WeightDecouple`. -/
theorem conjC1_of_delange_katai_twoPoint_decouple (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hE : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → TwoPointElliott b p q (((m : ℤ) : ℝ) / b))
    (hW : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → WeightDecouple b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_katai hDK hD fun b hb m hm hdvd =>
    pairDecorr_of_split b (by omega) _ (hE b hb m hm hdvd) (hW b hb m hm hdvd)

/-! ### The converse half: the split is not a weakening in disguise

If the crux holds and the two-point factor decorrelates, then the decoupling holds too — so
`WeightDecouple` is not hiding extra strength beyond the crux itself. -/

theorem weightDecouple_of_twoPointWeighted (b p q : ℕ) (t : ℝ)
    (hE : TwoPointElliott b p q t) (h : TwoPointWeighted b p q t) :
    WeightDecouple b p q t := by
  have hWnorm : ∀ R, ‖fullMean (peelWeight b p q t) R‖ ≤ 1 := fun R =>
    norm_fullMean_le_one _ R (fun m => le_of_eq (norm_peelWeight b p q t m))
  have hprod : Tendsto (fun R =>
      fullMean (twoPointFactor b p q t) R * fullMean (peelWeight b p q t) R) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp hE) ε hε] with R hR
    calc ‖fullMean (twoPointFactor b p q t) R * fullMean (peelWeight b p q t) R‖
        = ‖fullMean (twoPointFactor b p q t) R‖ * ‖fullMean (peelWeight b p q t) R‖ :=
          norm_mul _ _
      _ ≤ ‖fullMean (twoPointFactor b p q t) R‖ * 1 := by
          nlinarith [hWnorm R, norm_nonneg (fullMean (twoPointFactor b p q t) R),
            norm_nonneg (fullMean (peelWeight b p q t) R)]
      _ = ‖fullMean (twoPointFactor b p q t) R‖ := by ring
      _ < ε := hR
  have hAW : Tendsto (fun R =>
      fullMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) R) atTop (𝓝 0) := by
    refine h.congr fun R => ?_
    refine congrArg (fun z => z / (R : ℂ)) (Finset.sum_congr rfl fun n _ => ?_)
    simp only [twoPointFactor]
  rw [WeightDecouple]
  simpa using hAW.sub hprod

/-! ### The sharpest form the development reaches: averaged over the multipliers AND `K = 1`

Laps 22–23 replaced every pointwise limit over pairs `(p, q)` by a mean over `p, q ≤ w`
(the true Kátai/BSZ input); laps 24–25 replaced the `2K`-point correlation, `K → ∞`, by an exact
two-point one.  The two commute, because the second is an *identity*: the averaged leaf may be
written directly on the weighted two-point correlation. -/

/-- The averaged weighted two-point correlation. -/
noncomputable def twoPointAvgSum (b : ℕ) (t : ℝ) (w N : ℕ) : ℝ :=
  (∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      if p = q then 0 else
        ‖fullMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) N‖)
    / ((primesLe w).card : ℝ) ^ 2

lemma pairDecorrAvgSum_eq_twoPointAvgSum (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (w N : ℕ) :
    pairDecorrAvgSum b t w N = twoPointAvgSum b t w N := by
  have hpt : ∀ p q n : ℕ, phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))
      = twoPointFactor b p q t n * peelWeight b p q t n := by
    intro p q n
    have h := pairPhase_eq_twoPoint b hb t p q n
    rw [pairTail] at h
    rw [h, twoPointFactor]
  unfold pairDecorrAvgSum twoPointAvgSum
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hpq : p = q
  · simp [hpq]
  · simp only [if_neg hpq]
    congr 2
    funext n
    exact hpt p q n

/-- **THE SHARPEST LEAF.**  An average over ordered pairs of distinct prime multipliers `p, q ≤ w`
of a weighted TWO-point correlation.  Every pointwise limit and every `K → ∞` has been removed. -/
def TwoPointWeightedAvg (b : ℕ) (t : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, ∀ᶠ N : ℕ in atTop, twoPointAvgSum b t w N < ε

theorem pairDecorrAvg_iff_twoPointWeightedAvg (b : ℕ) (hb : 2 ≤ b) (t : ℝ) :
    PairDecorrAvg b t ↔ TwoPointWeightedAvg b t := by
  have key : ∀ w N : ℕ, pairDecorrAvgSum b t w N = twoPointAvgSum b t w N :=
    fun w N => pairDecorrAvgSum_eq_twoPointAvgSum b hb t w N
  constructor
  · intro h ε hε
    exact (h ε hε).mono fun w hw => hw.mono fun N hN => by rwa [key w N] at hN
  · intro h ε hε
    exact (h ε hε).mono fun w hw => hw.mono fun N hN => by rwa [key w N]

/-- **THE SWING, ON THE SHARPEST LEAF.**  `ConjC1` from Delange's theorem, the averaged
Kátai/BSZ criterion, and an averaged weighted two-point correlation. -/
theorem conjC1_of_delange_kataiAvg_twoPointWeightedAvg (hDK : KataiOrthogonalityAvg)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      TwoPointWeightedAvg b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_kataiAvg_pairDecorrAvg hDK hD fun b hb m hm hdvd =>
    (pairDecorrAvg_iff_twoPointWeightedAvg b (by omega) _).mpr (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
