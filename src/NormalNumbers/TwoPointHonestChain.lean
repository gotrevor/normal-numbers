import NormalNumbers.TwoPointKataiGap

/-!
# C1 on hypotheses that match the literature

Laps 4–5 showed that `KataiOrthogonalityAvg` (`PairDecoupleAvg.lean`), cited as the true averaged
form of Bourgain–Sarnak–Ziegler / Kátai, asks for less than their proof supplies: the pair term
enters the Cauchy–Schwarz as a **sum** measured against `L(w)² = (Σ_{p≤w} 1/p)²`, and
`avgShape_not_imply_kataiBudget` exhibits a table meeting the averaged criterion's quantifier
order whose pair sum is `≫ L(w)²`.

This file re-runs the whole C1 swing on hypotheses that *do* match the literature:

* `KataiQuantSharp` — the quantitative inequality with its true constants (`TwoPointKataiSharp`);
* `DelangeMean` — Delange's theorem, as before;
* **`TwoPointPairSumSmall b t`** — the honest open leaf: along a slowly growing cutoff `w(N)`,

      Σ_{p ≠ q ≤ w(N)} ‖E_{n<N} ζ^{ω(pn+1)} conj ζ^{ω(qn+1)} W(n)‖   =   o( L(w(N))² ).

`twoPointPairSum_eq` certifies that this is the same arithmetic quantity the ratified leaf
`TwoPointWeightedAvg` measures — only the normalisation, and the quantifier order, differ.  The
ratified statement `twoPointWeightedAvg_all` is untouched.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The pair SUM of the weighted two-point correlations. -/
noncomputable def twoPointPairSum (b : ℕ) (t : ℝ) (w N : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
    if p = q then 0 else
      ‖fullMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) N‖

/-- The orbit-difference pair sum *is* the weighted two-point pair sum. -/
lemma twoPointPairSum_eq (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (w N : ℕ) :
    pairSum (fun n => phase (t * omegaTail b n)) w N = twoPointPairSum b t w N := by
  have heq : ∀ p q : ℕ, (fun n => phase (t * omegaTail b (p * n))
      * (starRingEnd ℂ) (phase (t * omegaTail b (q * n))))
      = fun n => twoPointFactor b p q t n * peelWeight b p q t n := by
    intro p q
    funext n
    rw [conj_phase, ← phase_add, show t * omegaTail b (p * n) + -(t * omegaTail b (q * n))
      = t * (omegaTail b (p * n) - omegaTail b (q * n)) by ring]
    have h := pairPhase_eq_twoPoint b hb t p q n
    rw [pairTail] at h
    rw [h, twoPointFactor]
  unfold pairSum twoPointPairSum
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hpq : p = q
  · simp [hpq]
  · simp only [if_neg hpq, heq p q]

/-- **THE HONEST LEAF.**  The pair sum is `o(L(w)²)` along a slowly growing cutoff.  This is what
the Kátai/BSZ Cauchy–Schwarz actually needs; `TwoPointWeightedAvg` asks only for
`o(π(w)²)`, which laps 4–5 show is strictly too little. -/
def TwoPointPairSumSmall (b : ℕ) (t : ℝ) : Prop :=
  ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
    (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
    Tendsto (fun N => twoPointPairSum b t (w N) N / (kataiPrimeRecip (w N)) ^ 2) atTop (𝓝 0)

lemma pairSumSmallGrowing_of_twoPoint (b : ℕ) (hb : 2 ≤ b) (t : ℝ)
    (h : TwoPointPairSumSmall b t) :
    PairSumSmallGrowing (fun n => phase (t * omegaTail b n)) := by
  obtain ⟨w, h1, h2, h3⟩ := h
  refine ⟨w, h1, h2, h3.congr fun N => ?_⟩
  rw [twoPointPairSum_eq b hb]

/-- `ShiftIndep` from the honest quantitative criterion and the honest leaf. -/
theorem shiftIndep_of_kataiQuantSharp (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (hQ : KataiQuantSharp)
    (hD : DelangeMean t) (hP : TwoPointPairSumSmall b t) : ShiftIndep b t := by
  set a : ℕ → ℂ := fun n => phase (t * omegaTail b n) with ha
  set f : ℕ → ℂ := fun n => phase (t * (omegaNat n : ℝ)) with hf
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hfnorm : ∀ n, ‖f n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := fun m n h =>
    phase_omegaNat_multiplicative t m n h
  have hDKc : Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) :=
    tendsto_fullMean_of_kataiQuantSharp hQ a f hanorm hfnorm hmul
      (pairSumSmallGrowing_of_twoPoint b hb t hP)
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

/-- **THE HONEST SWING.**  `ConjC1` from Delange's theorem, the Kátai/BSZ inequality *with its
true constants*, and the pair-sum leaf.  Every hypothesis here is either a theorem of the
literature as its proof actually gives it, or the single open leaf `TwoPointPairSumSmall`. -/
theorem conjC1_of_delange_kataiQuantSharp_pairSumSmall (hQ : KataiQuantSharp)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      TwoPointPairSumSmall b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_weylMean fun b hb m hm hdvd =>
    weylMean_tendsto_zero_of b (by omega) ((m : ℤ) : ℝ) (hD b hb m hm hdvd)
      (shiftIndep_of_kataiQuantSharp b (by omega) (((m : ℤ) : ℝ) / b) hQ (hD b hb m hm hdvd)
        (hP b hb m hm hdvd))

/-! ### Where the ratified leaf sits relative to the honest one

`TwoPointWeightedAvg` normalises the same pair sum by `π(w)²`; the honest leaf normalises it by
`L(w)²`, and `π(w)/L(w)² → ∞` (`tendsto_card_div_kataiPrimeRecip_sq`).  So the honest leaf is the
strictly harder statement, and the ratified one does not imply it by normalisation alone. -/

lemma twoPointAvgSum_eq_pairSum_div (b : ℕ) (t : ℝ) (w N : ℕ) :
    twoPointAvgSum b t w N = twoPointPairSum b t w N / ((primesLe w).card : ℝ) ^ 2 := rfl

/-- The honest leaf implies the ratified one's diagonal form: it is genuinely stronger. -/
theorem twoPointWeightedAvgSlowGrowing_of_pairSumSmall (b : ℕ) (t : ℝ)
    (h : TwoPointPairSumSmall b t) : TwoPointWeightedAvgSlowGrowing b t := by
  obtain ⟨w, h1, h2, h3⟩ := h
  refine ⟨w, h1, h2, ?_⟩
  have hcardTop : Tendsto (fun N => ((primesLe (w N)).card : ℝ)) atTop atTop :=
    tendsto_card_primesLe.comp h1
  have hinv : Tendsto (fun N => 1 / ((primesLe (w N)).card : ℝ)) atTop (𝓝 0) := by
    simpa [one_div, Pi.inv_def] using hcardTop.inv_tendsto_atTop
  have hratio : Tendsto
      (fun N => (kataiPrimeRecip (w N)) ^ 2 / ((primesLe (w N)).card : ℝ) ^ 2) atTop (𝓝 0) := by
    have hp := (tendsto_kataiPrimeRecip_sq_div_card.comp h1).mul hinv
    rw [mul_zero] at hp
    refine hp.congr fun N => ?_
    rw [Function.comp_apply, div_mul_div_comm, mul_one, ← sq]
  have hmul := h3.mul hratio
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [h2] with N hN
  have hcpos : ((primesLe (w N)).card : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((primesLe (w N)).card : ℝ) := by exact_mod_cast card_primesLe_pos hN.1
    exact ne_of_gt this
  have hLpos : kataiPrimeRecip (w N) ≠ 0 := by
    have h2m : (2 : ℕ) ∈ primesLe (w N) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
    exact ne_of_gt (Finset.sum_pos' (fun p _ => by positivity) ⟨2, h2m, by norm_num⟩)
  rw [twoPointAvgSum_eq_pairSum_div]
  field_simp


end NormalNumbers.CastingOut
