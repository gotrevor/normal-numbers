import NormalNumbers.ElliottShiftRung

/-!
# The mirrored rung: non-pretentiousness on the *shifted* function

**A blocker found this lap, and discharged here.**  `ShiftCMLogElliott` bounds
`∑ f₁(n) f₂(n+h) / n` assuming non-pretentiousness of `f₁`, the **unshifted** function.  The crux
`NormalNumbers.ElliottLadder.DilatedCMLogElliott` has affine forms `a·n + c₁`, `a·n + c₂` with only
`c₁ ≠ c₂` assumed, and non-pretentiousness on the function attached to the **first** form.  When
`c₂ < c₁` that function sits at the *larger* shift, so the un-mirrored rung does not apply.

That gap is genuine and cannot be closed by relabelling.  Every top-level symmetry was checked and
each one moves the hypothesis onto `f₂`:
* swapping the pair (`Erdos67b.elliottLogCorrelation_swap`) needs non-pretentiousness of `f₂`;
* conjugating everything turns `∑ w f₁(m+h) f₂(m)` into `∑ w (conj f₂)(m) (conj f₁)(m+h)`, whose
  first function is again built from `f₂`;
* reindexing `m ↦ m − h` moves the shift onto `f₂` and changes nothing else.

So the hypothesis must genuinely be movable to the *second* block inside the graph argument.  It is,
and cheaply: in `norm_pairTwistedPrimeGraphMean_le_largeFrequencies` the two blocks enter the pairing
`‖blockFourier T b t‖ · ‖blockFourier T (conj ∘ c) t‖` **symmetrically**, and Parseval is applied to
both.  The choice of which factor is kept in the large-frequency sum and which is bounded trivially by
`H` is therefore free.  This file makes the other choice and propagates it up the four rungs.

Contents (each the `_snd` mirror of the corresponding result):
* `norm_pairTwistedPrimeGraphMean_le_largeFrequencies_snd`
* `norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment_snd`
* `exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment_snd`
* `exists_pairLogCorrelation_small_of_fourier_first_moments_snd`
* `ShiftCMLogElliottMirror` / `shiftCMLogElliottMirror` — the rung, with `MRTNonpretentious f₂`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter
open Erdos438.Fourier

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-- **The mirrored large-frequency bound.**  Identical to
`norm_pairTwistedPrimeGraphMean_le_largeFrequencies` with the roles of the two blocks exchanged: the
Fourier first moment is now taken on `conj ∘ c`, and it is the *first* block that is bounded
trivially by `H`. -/
theorem norm_pairTwistedPrimeGraphMean_le_largeFrequencies_snd {H T : ℕ} [NeZero T]
    (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ∀ j, ‖c j‖ ≤ 1)
    {θ M : ℝ} (hθ : 0 ≤ θ)
    (hmult : ∀ t ∈ Finset.range T, ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤ M) :
    ‖pairTwistedPrimeGraphMean w b c h s‖ ≤ θ * H + ((H : ℝ) * M / T) *
      ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
        ‖blockFourier T (fun j ↦ conj (c j)) (t : ℤ)‖ := by
  classical
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  set c' : Fin H → ℂ := fun j ↦ conj (c j) with hc'
  have hc'b : ∀ j, ‖c' j‖ ≤ 1 := by
    intro j; rw [hc', RCLike.norm_conj]; exact hc j
  have hpoint (t : ℕ) (ht : t ∈ Finset.range T) :
      ‖pairBlockPairing T b c (t : ℤ)‖ * ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤
        θ * ((‖blockFourier T b (t : ℤ)‖ ^ 2 + ‖blockFourier T c' (t : ℤ)‖ ^ 2) / 2) +
          if θ ≤ ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ then
            H * M * ‖blockFourier T c' (t : ℤ)‖ else 0 := by
    have hbH : ‖blockFourier T b (t : ℤ)‖ ≤ H := by
      simpa using norm_blockFourier_le T b (t : ℤ) hb
    have hnorm : ‖pairBlockPairing T b c (t : ℤ)‖ =
        ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ := norm_pairBlockPairing T b c _
    by_cases htlarge : θ ≤ ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖
    · rw [if_pos htlarge, hnorm]
      have hkey : ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ *
          ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤
            (H : ℝ) * M * ‖blockFourier T c' (t : ℤ)‖ := by
        have h1 : ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ ≤
            (H : ℝ) * ‖blockFourier T c' (t : ℤ)‖ :=
          mul_le_mul_of_nonneg_right hbH (norm_nonneg _)
        calc
          _ ≤ (H : ℝ) * ‖blockFourier T c' (t : ℤ)‖ *
              ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ (H : ℝ) * ‖blockFourier T c' (t : ℤ)‖ * M :=
            mul_le_mul_of_nonneg_left (hmult t ht) (by positivity)
          _ = _ := by ring
      nlinarith [sq_nonneg ‖blockFourier T b (t : ℤ)‖,
        sq_nonneg ‖blockFourier T c' (t : ℤ)‖, mul_nonneg hθ
          (add_nonneg (sq_nonneg ‖blockFourier T b (t : ℤ)‖)
            (sq_nonneg ‖blockFourier T c' (t : ℤ)‖))]
    · rw [if_neg htlarge, add_zero, hnorm]
      have hlt := le_of_not_ge htlarge
      have hamgm : ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ ≤
          (‖blockFourier T b (t : ℤ)‖ ^ 2 + ‖blockFourier T c' (t : ℤ)‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖blockFourier T b (t : ℤ)‖ - ‖blockFourier T c' (t : ℤ)‖)]
      have hprodnn : 0 ≤ ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        _ ≤ ‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖ * θ :=
          mul_le_mul_of_nonneg_left hlt hprodnn
        _ = θ * (‖blockFourier T b (t : ℤ)‖ * ‖blockFourier T c' (t : ℤ)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hamgm hθ
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.mul_sum] at hsum
  have hpb := sum_blockFourier_norm_sq_le b hHT hb
  have hpc := sum_blockFourier_norm_sq_le c' hHT hc'b
  have hparseval : (∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ ^ 2 + ‖blockFourier T c' (t : ℤ)‖ ^ 2) / 2) ≤ (T : ℝ) * H := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have htotal := hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hparseval hθ) le_rfl)
  calc
    ‖pairTwistedPrimeGraphMean w b c h s‖ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ‖pairBlockPairing T b c (t : ℤ)‖ *
          ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ := by
      rw [pairTwistedPrimeGraphMean_eq_fourier w b c h s hT, norm_mul, norm_inv,
        Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
      rw [norm_mul]
    _ ≤ (T : ℝ)⁻¹ * (θ * ((T : ℝ) * H) + H * M *
        ∑ t ∈ pairTwistedLargeFrequencies T h s w θ, ‖blockFourier T c' (t : ℤ)‖) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by
      rw [pairTwistedLargeFrequencies]
      field_simp

/-- Blocks of a conjugated sequence are the conjugated blocks. -/
theorem finiteSequenceBlock_conj (F : ℕ → ℂ) (H n : ℕ) :
    (fun j ↦ conj (finiteSequenceBlock F H n j)) =
      finiteSequenceBlock (fun m ↦ conj (F m)) H n := rfl

/-- Mirror of `norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment`: the first-moment
hypothesis concerns `conj ∘ F₂`. -/
theorem norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment_snd
    {L U H T : ℕ} [NeZero T] (hL : 0 < L) (hLU : L ≤ U)
    (w : ℕ → ℂ) (F₁ F₂ : ℕ → ℂ) (h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hF₁ : ∀ n, 0 < n → ‖F₁ n‖ ≤ 1) (hF₂ : ∀ n, 0 < n → ‖F₂ n‖ ≤ 1)
    {θ M Z : ℝ} (hθ : 0 ≤ θ) (hM : 0 ≤ M)
    (hmult : ∀ t ∈ Finset.range T, ‖twistedPrimeGraphMultiplier T h s w (t : ℤ)‖ ≤ M)
    (hfirst : ∀ t ∈ pairTwistedLargeFrequencies T h s w θ,
      logProbExpectation L U
        (fun n ↦ ‖blockFourier T
          (finiteSequenceBlock (fun m ↦ conj (F₂ m)) H n) (t : ℤ)‖) ≤ Z) :
    ‖logProbExpectation L U (fun n ↦ pairTwistedPrimeGraphMean w
        (finiteSequenceBlock F₁ H n) (finiteSequenceBlock F₂ H n) h s)‖ ≤
      θ * H + ((H : ℝ) * M / T) * (pairTwistedLargeFrequencies T h s w θ).card * Z := by
  have hpoint (n : ℕ) : ‖pairTwistedPrimeGraphMean w (finiteSequenceBlock F₁ H n)
      (finiteSequenceBlock F₂ H n) h s‖ ≤
      θ * H + ((H : ℝ) * M / T) *
        ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
          ‖blockFourier T (finiteSequenceBlock (fun m ↦ conj (F₂ m)) H n) (t : ℤ)‖ := by
    have hh := norm_pairTwistedPrimeGraphMean_le_largeFrequencies_snd w _ _ h s hHT hT
      (fun j ↦ hF₁ (n + j.1 + 1) (by omega)) (fun j ↦ hF₂ (n + j.1 + 1) (by omega)) hθ hmult
    exact hh
  have hweights : ∑ n : LogProbIndex L U, (logProbWeightNN L U n : ℝ) = 1 := by
    exact_mod_cast sum_logProbWeightNN hL hLU
  have hexpand : logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / T) *
      ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
        ‖blockFourier T (finiteSequenceBlock (fun m ↦ conj (F₂ m)) H n) (t : ℤ)‖) =
      θ * H + ((H : ℝ) * M / T) * ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
        logProbExpectation L U
          (fun n ↦ ‖blockFourier T
            (finiteSequenceBlock (fun m ↦ conj (F₂ m)) H n) (t : ℤ)‖) := by
    simp only [logProbExpectation, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hweights, one_mul]
    congr 1
    simp_rw [mul_left_comm (logProbWeightNN L U _ : ℝ) ((H : ℝ) * M / T)]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  calc
    _ ≤ logProbExpectation L U (fun n ↦ ‖pairTwistedPrimeGraphMean w
        (finiteSequenceBlock F₁ H n) (finiteSequenceBlock F₂ H n) h s‖) :=
      norm_logProbExpectation_le_expectation_norm _ _ _
    _ ≤ logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / T) *
        ∑ t ∈ pairTwistedLargeFrequencies T h s w θ,
          ‖blockFourier T (finiteSequenceBlock (fun m ↦ conj (F₂ m)) H n) (t : ℤ)‖) :=
      logProbExpectation_mono _ _ (fun n _ ↦ hpoint n)
    _ = _ := hexpand
    _ ≤ θ * H + ((H : ℝ) * M / T) * ∑ _t ∈ pairTwistedLargeFrequencies T h s w θ, Z := by
      gcongr
      exact hfirst _ ‹_›
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Mirror of `exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`. -/
theorem exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment_snd
    {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ L U : ℕ, 0 < L → L ≤ U → ∀ F₁ F₂ : ℕ → ℂ,
      (∀ n, 0 < n → ‖F₁ n‖ ≤ 1) → (∀ n, 0 < n → ‖F₂ n‖ ≤ 1) →
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖w p‖ ≤ 1) →
      (∀ t ∈ Finset.range (4 * h * H + 1),
        logProbExpectation L U (fun n ↦
          ‖blockFourier (4 * h * H + 1)
            (finiteSequenceBlock (fun m ↦ conj (F₂ m)) H n) (t : ℤ)‖) ≤ ζ * H) →
      ‖logProbExpectation L U (fun n ↦ pairTwistedPrimeGraphMean w
        (finiteSequenceBlock F₁ H n) (finiteSequenceBlock F₂ H n) h
        (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))))‖ ≤ η * H / (32 * Real.log H) := by
  obtain ⟨C, hC, H₁, hH₁, hcontrol⟩ := exists_eventually_twistedPrimeGraphMultiplier_bounds hh
  let cutoff : ℝ := η / 64
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  let N : ℝ := C / cutoff ^ 4
  have hN : 0 < N := by dsimp [N]; positivity
  let ζ : ℝ := η / (1024 * (N + 1))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hbudget : cutoff + 16 * ζ * N ≤ η / 32 := by
    have hratio : N / (N + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      cutoff + 16 * ζ * N = η / 64 + (η / 64) * (N / (N + 1)) := by
        dsimp [cutoff, ζ]
        field_simp; ring
      _ ≤ η / 64 + (η / 64) * 1 := by gcongr
      _ = η / 32 := by ring
  refine ⟨ζ, hζ, H₁, hH₁, ?_⟩
  intro H hH L U hL hLU F₁ F₂ hF₁ hF₂ w hw hfirst
  set P := H / (4 * h + 4) with hPdef
  set T := 4 * h * H + 1 with hTdef
  set s := PrimeEstimates.dyadicPrimes P with hsdef
  have hH2 : 2 ≤ H := hH₁.trans hH
  have hHr : (0 : ℝ) < H := by positivity
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hTpos : 0 < T := by rw [hTdef]; omega
  let _ : NeZero T := ⟨hTpos.ne'⟩
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hHT : H ≤ T := by rw [hTdef]; nlinarith
  have hdiv : P * (4 * h + 4) ≤ H := Nat.div_mul_le_self H _
  have hPH : 2 * P ≤ H := by nlinarith
  have hsprimes : s ⊆ Nat.primesLE H := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩
  have hnowrap : ∀ p ∈ s, H + p * h ≤ T := by
    intro p hp
    have hpH := (Nat.mem_primesLE.mp (hsprimes hp)).1
    have hprodle := Nat.mul_le_mul_right h hpH
    rw [hTdef]
    nlinarith
  obtain ⟨hfourth, hsup⟩ := hcontrol H hH w hw
  have hcard : (pairTwistedLargeFrequencies T h s w (cutoff / Real.log H)).card ≤ N := by
    have hc := card_pairTwistedLargeFrequencies_le s w
      (show 0 < cutoff / Real.log H by positivity) hfourth
    have heq : (C / Real.log H ^ 4) / (cutoff / Real.log H) ^ 4 = N := by
      dsimp [N]
      field_simp
    exact heq ▸ hc
  have hbound := norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment_snd
    hL hLU w F₁ F₂ h s hHT hnowrap hF₁ hF₂
    (θ := cutoff / Real.log H) (M := 16 / Real.log H) (Z := ζ * H)
    (by positivity) (by positivity) (fun t _ ↦ hsup t)
    (fun t ht ↦ hfirst t (Finset.mem_filter.mp ht).1)
  have hratio : (H : ℝ) * (16 / Real.log H) / T ≤ 16 / Real.log H := by
    apply (div_le_iff₀ hTr).mpr
    have hHTr : (H : ℝ) ≤ T := by exact_mod_cast hHT
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hHTr
      (show 0 ≤ (16 : ℝ) / Real.log H by positivity)
  calc
    _ ≤ cutoff / Real.log H * H + ((H : ℝ) * (16 / Real.log H) / T) *
        (pairTwistedLargeFrequencies T h s w (cutoff / Real.log H)).card * (ζ * H) := hbound
    _ ≤ cutoff / Real.log H * H + (16 / Real.log H) * N * (ζ * H) := by gcongr
    _ = (cutoff + 16 * ζ * N) * (H / Real.log H) := by ring
    _ ≤ (η / 32) * (H / Real.log H) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = η * H / (32 * Real.log H) := by ring

/-- Mirror of `exists_pairLogCorrelation_small_of_fourier_first_moments`: the first-moment hypothesis
now constrains `conj ∘ f₂`, i.e. the *shifted* function. -/
theorem exists_pairLogCorrelation_small_of_fourier_first_moments_snd
    {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ Hmin : ℕ,
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
        (∀ j < J, ∀ t ∈ Finset.range (4 * h * entropyScale H₀ j + 1),
          logProbExpectation L U (fun n ↦
            ‖blockFourier (4 * h * entropyScale H₀ j + 1)
              (finiteSequenceBlock (fun m ↦ conj (f₂ m)) (entropyScale H₀ j) n) (t : ℤ)‖) ≤
                ζ * entropyScale H₀ j) →
        ‖pairLogCorrelation L U f₁ f₂ h‖ < η := by
  obtain ⟨ζ, hζ, H₁, hH₁, hupper⟩ :=
    exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment_snd hh hη
  refine ⟨ζ, hζ, ?_⟩
  intro Hmin
  obtain ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, hlower⟩ :=
    exists_logProb_dyadic_pairTwistedMean_lower hη h (max Hmin H₁)
  refine ⟨H₀, J, L₀, W₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ hfirst
  by_contra hnot
  obtain ⟨j, hj, hlarge⟩ :=
    hlower L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ (le_of_not_gt hnot)
  set H := entropyScale H₀ j with hHdef
  have hH : H₁ ≤ H := ((le_max_right _ _).trans hmin).trans (le_entropyScale H₀ j)
  have hH2 : 2 ≤ H := hH₁.trans hH
  have hw : ∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖pairTwist f₁ f₂ p‖ ≤ 1 := by
    intro p hp
    have hppos : 0 < p := (Nat.prime_of_mem_primesLE (dyadicPrimes_subset_primesLE hh hp)).pos
    exact (norm_pairTwist hu₁ hu₂ hppos).le
  have hbridge : ∀ n : ℕ,
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) =
        pairTwistedPrimeGraphMean (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) :=
    fun n ↦ pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean _ _ _ _ _
      (dyadicPrimes_subset_primesLE hh)
  simp only [hbridge] at hlarge
  have hsmall := hupper H hH L U hL (by omega) f₁ f₂
    (fun n hn ↦ (hu₁ n hn).le) (fun n hn ↦ (hu₂ n hn).le) (pairTwist f₁ f₂) hw (hfirst j hj)
  have hlog := log_entropyScale_pos hH₀ j
  have hscale : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hpos : 0 < η * H / (32 * Real.log H) := by positivity
  have heq : η * H / (16 * Real.log H) = 2 * (η * H / (32 * Real.log H)) := by ring
  rw [heq] at hlarge
  linarith

/-! ## The mirrored rung -/

/-- Conjugation preserves non-pretentiousness: the quantified set of twists `(χ, t)` with `q ≤ A`,
`|t| ≤ A·X` is closed under `(χ, t) ↦ (conj χ, −t)`, and
`Erdos67b.dirichletArchimedeanTwist (conj χ) (−t) = conj (dirichletArchimedeanTwist χ t)`. -/
theorem mrtNonpretentious_conj {f : ℕ → ℂ} {A X : ℕ} (hpret : MRTNonpretentious f A X) :
    MRTNonpretentious (fun n ↦ conj (f n)) A X := by
  intro q hq hqA χ t ht
  have hconj := hpret q hq hqA (χ.ringHomComp (starRingEnd ℂ)) (-t)
    (by simpa only [abs_neg] using ht)
  refine hconj.trans_eq ?_
  unfold pretentiousDistSqToTwist pretentiousDistSq
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  unfold pretentiousTerm
  have harch : archimedeanTwist (-t) p = conj (archimedeanTwist t p) := by
    rw [conj_archimedeanTwist, archimedeanTwist]
    push_cast
    rw [mul_neg]
  have hW : dirichletArchimedeanTwist (χ.ringHomComp (starRingEnd ℂ)) (-t) p =
      conj (dirichletArchimedeanTwist χ t p) := by
    rw [dirichletArchimedeanTwist, dirichletArchimedeanTwist, map_mul, harch]
    congr 1
  rw [hW, Complex.conj_conj]
  simp [← map_mul]

/-- **The mirrored pure-shift rung**: non-pretentiousness is assumed on `f₂`, the function at the
*shifted* argument. -/
def ShiftCMLogElliottMirror : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ h : ℕ, 0 < h →
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ f₁ f₂ : ℕ → ℂ,
          IsCompletelyMultiplicativeOnPositive f₁ →
          IsCompletelyMultiplicativeOnPositive f₂ →
          (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
          (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
          MRTNonpretentious f₂ A X →
          ‖shiftedPairLogCorrelation f₁ f₂ h X W‖ ≤ ε * Real.log W

theorem shiftCMLogElliottMirror : ShiftCMLogElliottMirror := by
  intro ε hε h hh
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ζ, hζ, hgraph⟩ := exists_pairLogCorrelation_small_of_fourier_first_moments_snd hh hη
  let δ : ℝ := ζ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Hmin, hHmin, hmrt⟩ := mrtModulatedShortIntervalUnrestricted δ hδ
  obtain ⟨H₀, J, L₀, M₀, hH₀min, hH₀, hJ, hL₀, hM₀, hgraphMain⟩ := hgraph Hmin
  let Hmax := max H₀ ((range J).sup (entropyScale H₀))
  have hHmax : Hmin ≤ Hmax := hH₀min.trans (le_max_left _ _)
  obtain ⟨N, hN, hmrtMain⟩ := hmrt Hmax hHmax
  obtain ⟨A₀, hA₀4, hA₀N, hA₀L, hthreshold⟩ := elliottExists_finalThreshold L₀ N M₀ hε
  refine ⟨A₀, by omega, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  have hA₀W : A₀ ≤ W := hA.trans hAW
  have hW4 : 4 ≤ W := hA₀4.trans hA₀W
  have hW : 0 < W := by omega
  obtain ⟨hlog, hmassThreshold, herror⟩ := hthreshold W hA₀W
  set L := elliottTrimmedLower X W L₀ with hLdef
  obtain ⟨hL, hLL, hLX⟩ := elliottTrimmedLower_geometry hW4 hWX
    (hA₀L.trans (hA₀W.trans hWX))
  obtain ⟨hMlo, hMhi⟩ := elliottTrimmedMass_bounds hW hWX hlog
  have hM : 0 < (logProbMassNN L X : ℝ) := by
    exact_mod_cast logProbMassNN_pos hL (by omega)
  have hm₂' : IsCompletelyMultiplicativeOnPositive (fun n ↦ conj (f₂ n)) :=
    conj_isCompletelyMultiplicativeOnPositive hm₂
  have hu₂' : ∀ n : ℕ, 0 < n → ‖conj (f₂ n)‖ = 1 := by
    intro n hn; rw [Complex.norm_conj]; exact hu₂ n hn
  have hpret' : MRTNonpretentious (fun n ↦ conj (f₂ n)) A X := mrtNonpretentious_conj hpret
  have hcorr : ‖pairLogCorrelation L X f₁ f₂ h‖ < η := by
    apply hgraphMain L X hL hLX hLL (hmassThreshold.trans hMlo) f₁ f₂ hm₁ hm₂ hu₁ hu₂
    intro j hj t _ht
    have hHlo : Hmin ≤ entropyScale H₀ j := hH₀min.trans (le_entropyScale H₀ j)
    have hHhi : entropyScale H₀ j ≤ Hmax :=
      (Finset.le_sup (f := entropyScale H₀) (mem_range.2 hj)).trans (le_max_right _ _)
    have hfirst := hmrtMain A X W (entropyScale H₀ j) (hA₀N.trans hA) hAW hWX
      hHlo hHhi (fun n ↦ conj (f₂ n)) hm₂' hu₂' hpret'
      ((t : ℝ) / (4 * h * entropyScale H₀ j + 1))
    have hbound := logProb_fourier_firstMoment_of_MRT hW
      (show 0 < entropyScale H₀ j by omega) hM hMlo hδ.le (fun n ↦ conj (f₂ n))
      (4 * h * entropyScale H₀ j + 1) (t : ℤ) (by
        simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          using hfirst)
    exact hbound.trans (by dsimp [δ]; nlinarith [Nat.cast_nonneg (α := ℝ) (entropyScale H₀ j)])
  rw [pairLogCorrelation, logProbExpectation_eq_mass_inv_smul_sum,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM), inv_mul_eq_div] at hcorr
  have hsum := (div_lt_iff₀ hM).1 hcorr
  have htrim := norm_shiftedPairLogCorrelation_le_trimmed (X := X) hW L₀ h f₁ f₂ hu₁ hu₂
  calc
    ‖shiftedPairLogCorrelation f₁ f₂ h X W‖ ≤
        ‖∑ n ∈ Icc L X, (n : ℝ)⁻¹ • (f₁ n * f₂ (n + h))‖ + L₀ := htrim
    _ ≤ η * (logProbMassNN L X : ℝ) + L₀ := add_le_add hsum.le le_rfl
    _ ≤ η * (2 * Real.log W) + (ε / 2) * Real.log W :=
      add_le_add (mul_le_mul_of_nonneg_left hMhi hη.le) herror
    _ = ε * Real.log W := by dsimp [η]; ring

end

end NormalNumbers.ElliottTwistedGraph
