import NormalNumbers.ElliottDilatedUpper

/-!
# The mirrored upper bound for the `a`-dilated prime graph

`NormalNumbers.ElliottTwistedGraphMirror` discharged, for the pure-shift graph, the observation that
the Fourier first-moment hypothesis may be placed on *either* block: in the large-frequency split the
two blocks enter the pairing symmetrically (Parseval is applied to both), so which factor is kept in
the large-frequency sum and which is bounded trivially by `H` is a free choice.

This file makes the other choice in the **dilated** stack, i.e. produces the `_snd` mirrors of

* `NormalNumbers.ElliottDilatedPairing.norm_dilatedPairTwistedMean_le_largeFrequencies`
* `NormalNumbers.ElliottDilatedPairing.norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment`
* `NormalNumbers.ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment`

One simplification over the un-mirrored versions: the second block is transformed at the *plain*
frequency `t`, with no alias shift `u*D`, so the first-moment hypothesis is a condition on a single
integer frequency rather than on the aliased pair.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset
open Erdos438.Fourier

namespace NormalNumbers.ElliottDilatedUpper

open Erdos67b
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottLadder

noncomputable section

/-- **The mirrored dilated large-frequency bound.**  Identical to
`NormalNumbers.ElliottDilatedPairing.norm_dilatedPairTwistedMean_le_largeFrequencies` with the roles
of the two blocks exchanged: the surviving Fourier factor is the second block's (at the unaliased
frequency `t`), and it is the first block that is bounded trivially by `H`. -/
theorem norm_dilatedPairTwistedMean_le_largeFrequencies_snd {H T α D : ℕ} [NeZero T] [NeZero α]
    (hTD : T = α * D) (w : ℕ → ℂ) (b c : Fin H → ℂ) (c₁ h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ∀ j, ‖c j‖ ≤ 1)
    {θ M : ℝ} (hθ : 0 ≤ θ)
    (hmult : ∀ x ∈ (Finset.range T) ×ˢ (Finset.range α),
      ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤ M) :
    ‖dilatedPairTwistedMean w b c α c₁ h s‖ ≤ θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
      ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
        ‖blockFourier T (fun j ↦ conj (c j)) (x.1 : ℤ)‖ := by
  classical
  have hTne : T ≠ 0 := NeZero.ne T
  have hαne : α ≠ 0 := NeZero.ne α
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hTne)
  have hαr : (0 : ℝ) < α := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hαne)
  set c' : Fin H → ℂ := fun j ↦ conj (c j) with hc'
  have hc'b : ∀ j, ‖c' j‖ ≤ 1 := by
    intro j; rw [hc', RCLike.norm_conj]; exact hc j
  set P : Finset (ℕ × ℕ) := (Finset.range T) ×ˢ (Finset.range α) with hPdef
  have hpoint : ∀ x ∈ P,
      ‖dilatedBlockPairing T D b c (x.1 : ℤ) (x.2 : ℤ)‖ *
          ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤
        θ * ((‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2 +
              ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) / 2) +
          if θ ≤ ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ then
            (H : ℝ) * M * ‖blockFourier T c' (x.1 : ℤ)‖ else 0 := by
    intro x hx
    have hbH : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ≤ H := by
      simpa using norm_blockFourier_le T b ((x.1 : ℤ) + (x.2 : ℤ) * D) hb
    have hnorm : ‖dilatedBlockPairing T D b c (x.1 : ℤ) (x.2 : ℤ)‖ =
        ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ * ‖blockFourier T c' (x.1 : ℤ)‖ :=
      norm_dilatedBlockPairing T D b c _ _
    by_cases htlarge : θ ≤ ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖
    · rw [if_pos htlarge, hnorm]
      have hkey : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
          ‖blockFourier T c' (x.1 : ℤ)‖ *
          ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤
            (H : ℝ) * M * ‖blockFourier T c' (x.1 : ℤ)‖ := by
        have h1 : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
            ‖blockFourier T c' (x.1 : ℤ)‖ ≤
            (H : ℝ) * ‖blockFourier T c' (x.1 : ℤ)‖ :=
          mul_le_mul_of_nonneg_right hbH (norm_nonneg _)
        calc
          _ ≤ (H : ℝ) * ‖blockFourier T c' (x.1 : ℤ)‖ *
              ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ (H : ℝ) * ‖blockFourier T c' (x.1 : ℤ)‖ * M :=
            mul_le_mul_of_nonneg_left (hmult x hx) (by positivity)
          _ = _ := by ring
      nlinarith [sq_nonneg ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖,
        sq_nonneg ‖blockFourier T c' (x.1 : ℤ)‖, mul_nonneg hθ
          (add_nonneg (sq_nonneg ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖)
            (sq_nonneg ‖blockFourier T c' (x.1 : ℤ)‖))]
    · rw [if_neg htlarge, add_zero, hnorm]
      have hlt := le_of_not_ge htlarge
      have hamgm : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
          ‖blockFourier T c' (x.1 : ℤ)‖ ≤
          (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2 +
            ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ -
          ‖blockFourier T c' (x.1 : ℤ)‖)]
      have hprodnn : 0 ≤ ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
          ‖blockFourier T c' (x.1 : ℤ)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        _ ≤ ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
            ‖blockFourier T c' (x.1 : ℤ)‖ * θ := mul_le_mul_of_nonneg_left hlt hprodnn
        _ = θ * (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
            ‖blockFourier T c' (x.1 : ℤ)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hamgm hθ
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.mul_sum] at hsum
  have hpb : (∑ x ∈ P, ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2) ≤ (α : ℝ) * (T * H) := by
    rw [hPdef, Finset.sum_product]
    rw [Finset.sum_comm]
    have hrow : ∀ u ∈ Finset.range α,
        (∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + (u : ℤ) * D)‖ ^ 2) ≤ (T : ℝ) * H := by
      intro u _
      have key := sum_norm_sq_blockFourier_shift (T := T) (H := H) hTne b (u * D)
      calc (∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + (u : ℤ) * D)‖ ^ 2)
          = ∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + ((u * D : ℕ) : ℤ))‖ ^ 2 :=
            Finset.sum_congr rfl fun t _ ↦ by
              norm_cast
        _ = ∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 := key
        _ ≤ (T : ℝ) * H := sum_blockFourier_norm_sq_le b hHT hb
    calc
      _ ≤ ∑ _u ∈ Finset.range α, (T : ℝ) * H := Finset.sum_le_sum hrow
      _ = (α : ℝ) * (T * H) := by simp [mul_comm]
  have hpc : (∑ x ∈ P, ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) ≤ (α : ℝ) * (T * H) := by
    rw [hPdef, Finset.sum_product]
    have : ∀ t ∈ Finset.range T,
        (∑ _u ∈ Finset.range α, ‖blockFourier T c' (t : ℤ)‖ ^ 2) =
          (α : ℝ) * ‖blockFourier T c' (t : ℤ)‖ ^ 2 := by
      intro t _; simp [mul_comm]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    have := sum_blockFourier_norm_sq_le c' hHT hc'b
    nlinarith [hαr.le, this]
  have hparseval : (∑ x ∈ P,
      (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2 +
        ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) / 2) ≤ (T : ℝ) * α * H := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    nlinarith [hpb, hpc]
  have htotal := hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hparseval hθ) le_rfl)
  calc
    ‖dilatedPairTwistedMean w b c α c₁ h s‖ ≤ ((T : ℝ) * α)⁻¹ * ∑ x ∈ P,
        ‖dilatedBlockPairing T D b c (x.1 : ℤ) (x.2 : ℤ)‖ *
          ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ := by
      rw [dilatedPairTwistedMean_eq_fourier hTD w b c c₁ h s hT, norm_mul, norm_inv, norm_mul,
        Complex.norm_natCast, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hPdef, Finset.sum_product]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ ↦ ?_)
      rw [norm_mul]
    _ ≤ ((T : ℝ) * α)⁻¹ * (θ * ((T : ℝ) * α * H) + H * M *
        ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
          ‖blockFourier T c' (x.1 : ℤ)‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [dilatedLargeFrequencies, hPdef]
      exact htotal
    _ = _ := by field_simp

/-- Conjugation commutes with re-basing a block. -/
theorem affineBlock_conj (f : ℕ → ℂ) (a n H : ℕ) :
    affineBlock (fun m ↦ conj (f m)) a n H = fun j ↦ conj (affineBlock f a n H j) := by
  funext j
  simp only [affineBlock]
  exact positiveIntExtension_conj f _

/-- **The mirrored logarithmic-average layer for the dilated mean.**  Port of
`NormalNumbers.ElliottTwistedGraphMirror.norm_logProb_pairTwistedPrimeGraphMean_le_of_fourier_first_moment_snd`
to the dilated mean: the Fourier first-moment hypothesis now concerns `conj ∘ F₂`, at the plain
frequency `t` (the alias shift lives on the first block, which is here discarded). -/
theorem norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment_snd
    {L U H T α D : ℕ} [NeZero T] [NeZero α] (hTD : T = α * D)
    (hL : 0 < L) (hLU : L ≤ U)
    (w : ℕ → ℂ) (F₁ F₂ : ℕ → ℂ) (a c₁ h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hF₁ : ∀ n : ℕ, 0 < n → ‖F₁ n‖ ≤ 1) (hF₂ : ∀ n : ℕ, 0 < n → ‖F₂ n‖ ≤ 1)
    {θ M Z : ℝ} (hθ : 0 ≤ θ) (hM : 0 ≤ M)
    (hmult : ∀ x ∈ (Finset.range T) ×ˢ (Finset.range α),
      ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤ M)
    (hfirst : ∀ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
      logProbExpectation L U
        (fun n ↦ ‖blockFourier T (affineBlock (fun m ↦ conj (F₂ m)) a n H) (x.1 : ℤ)‖) ≤ Z) :
    ‖logProbExpectation L U (fun n ↦ dilatedPairTwistedMean w
        (affineBlock F₁ a n H) (affineBlock F₂ a n H) α c₁ h s)‖ ≤
      θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
        (dilatedLargeFrequencies T D h c₁ α s w θ).card * Z := by
  classical
  simp only [affineBlock_conj] at hfirst
  have hpoint (n : ℕ) : ‖dilatedPairTwistedMean w
      (affineBlock F₁ a n H) (affineBlock F₂ a n H) α c₁ h s‖ ≤
      θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
        ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
          ‖blockFourier T (fun j ↦ conj (affineBlock F₂ a n H j)) (x.1 : ℤ)‖ :=
    norm_dilatedPairTwistedMean_le_largeFrequencies_snd hTD w _ _ c₁ h s hHT hT
      (norm_affineBlock_le_one hF₁ a n) (norm_affineBlock_le_one hF₂ a n) hθ hmult
  have hweights : ∑ n : LogProbIndex L U, (logProbWeightNN L U n : ℝ) = 1 := by
    exact_mod_cast sum_logProbWeightNN hL hLU
  have hexpand : logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
      ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
        ‖blockFourier T (fun j ↦ conj (affineBlock F₂ a n H j)) (x.1 : ℤ)‖) =
      θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
        ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
          logProbExpectation L U
            (fun n ↦ ‖blockFourier T (fun j ↦ conj (affineBlock F₂ a n H j)) (x.1 : ℤ)‖) := by
    simp only [logProbExpectation, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hweights, one_mul]
    congr 1
    simp_rw [mul_left_comm (logProbWeightNN L U _ : ℝ) ((H : ℝ) * M / ((T : ℝ) * α))]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  calc
    _ ≤ logProbExpectation L U (fun n ↦ ‖dilatedPairTwistedMean w
        (affineBlock F₁ a n H) (affineBlock F₂ a n H) α c₁ h s‖) :=
      norm_logProbExpectation_le_expectation_norm _ _ _
    _ ≤ logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
        ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
          ‖blockFourier T (fun j ↦ conj (affineBlock F₂ a n H j)) (x.1 : ℤ)‖) :=
      logProbExpectation_mono _ _ (fun n _ ↦ hpoint n)
    _ = _ := hexpand
    _ ≤ θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
        ∑ _x ∈ dilatedLargeFrequencies T D h c₁ α s w θ, Z := by
      gcongr
      exact hfirst _ ‹_›
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The mirrored dilated graph upper bound.**  `_snd` mirror of
`exists_dilatedPairTwistedMean_small_of_fourier_first_moment`: the Fourier first-moment hypothesis
is on `conj ∘ F₂`.  The parameter choreography is untouched. -/
theorem exists_dilatedPairTwistedMean_small_of_fourier_first_moment_snd
    {h a c₁ : ℕ} (hh : 0 < h) (ha : 0 < a) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ L U : ℕ, 0 < L → L ≤ U → ∀ F₁ F₂ : ℕ → ℂ,
      (∀ n, 0 < n → ‖F₁ n‖ ≤ 1) → (∀ n, 0 < n → ‖F₂ n‖ ≤ 1) →
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖w p‖ ≤ 1) →
      (∀ t : ℤ, logProbExpectation L U (fun n ↦
          ‖blockFourier (a * (4 * h * H + 1))
            (affineBlock (fun m ↦ conj (F₂ m)) a n H) t‖) ≤ ζ * H) →
      ‖logProbExpectation L U (fun n ↦ dilatedPairTwistedMean w
        (affineBlock F₁ a n H) (affineBlock F₂ a n H) a c₁ h
        (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))))‖ ≤ η * H / (32 * Real.log H) := by
  classical
  obtain ⟨C, hC, H₁, hH₁, hcontrol⟩ := exists_eventually_scaledTwistedMultiplier_bounds hh ha
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
        dsimp [cutoff, ζ]; field_simp; ring
      _ ≤ η / 64 + (η / 64) * 1 := by gcongr
      _ = η / 32 := by ring
  refine ⟨ζ, hζ, H₁, hH₁, ?_⟩
  intro H hH L U hL hLU F₁ F₂ hF₁ hF₂ w hw hfirst
  set P := H / (4 * h + 4) with hPdef
  set D := 4 * h * H + 1 with hDdef
  set T := a * D with hTdef
  set s := PrimeEstimates.dyadicPrimes P with hsdef
  have hH2 : 2 ≤ H := hH₁.trans hH
  have hHr : (0 : ℝ) < H := by positivity
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hDpos : 0 < D := by rw [hDdef]; omega
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have : NeZero T := ⟨hTpos.ne'⟩
  have : NeZero a := ⟨ha.ne'⟩
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have har : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hDT : D ≤ T := Nat.le_mul_of_pos_left D ha
  have hHD : H ≤ D := by rw [hDdef]; nlinarith
  have hHT : H ≤ T := hHD.trans hDT
  have hdiv : P * (4 * h + 4) ≤ H := Nat.div_mul_le_self H _
  have hPH : 2 * P ≤ H := by nlinarith
  have hsprimes : s ⊆ Nat.primesLE H := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩
  have hnowrap : ∀ p ∈ s, H + p * h ≤ T := by
    intro p hp
    have hpH := (Nat.mem_primesLE.mp (hsprimes hp)).1
    have hprod := Nat.mul_le_mul_right h hpH
    have : H + p * h ≤ D := by rw [hDdef]; nlinarith
    exact this.trans hDT
  have hsup : ∀ x ∈ (Finset.range T) ×ˢ (Finset.range a),
      ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤ 16 / Real.log H := by
    intro x _
    exact norm_dilatedTwistedMultiplier_le s w
      (fun w' hw' t ↦ (hcontrol H hH w' hw').2 t) hw _ _
  have hfourth : (∑ x ∈ (Finset.range T) ×ˢ (Finset.range a),
      ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ^ 4) ≤
      (a : ℝ) * (C / Real.log H ^ 4) :=
    sum_fourth_dilatedTwistedMultiplier_le s w
      (fun w' hw' ↦ (hcontrol H hH w' hw').1) hw
  have hcard : (dilatedLargeFrequencies T D h c₁ a s w (cutoff / Real.log H)).card ≤
      (a : ℝ) * N := by
    have hc := card_dilatedLargeFrequencies_le s w
      (show 0 < cutoff / Real.log H by positivity) hfourth
    have heq : ((a : ℝ) * (C / Real.log H ^ 4)) / (cutoff / Real.log H) ^ 4 = (a : ℝ) * N := by
      dsimp [N]; field_simp
    exact heq ▸ hc
  have hbound := norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment_snd
    (T := T) (α := a) (D := D) rfl hL hLU w F₁ F₂ a c₁ h s hHT hnowrap hF₁ hF₂
    (θ := cutoff / Real.log H) (M := 16 / Real.log H) (Z := ζ * H)
    (by positivity) (by positivity) hsup
    (fun x _ ↦ hfirst (x.1 : ℤ))
  have hratio : (H : ℝ) * (16 / Real.log H) / ((T : ℝ) * a) ≤ (16 / Real.log H) / a := by
    rw [div_le_div_iff₀ (by positivity) har]
    have hHTr : (H : ℝ) ≤ T := by exact_mod_cast hHT
    have h16 : (0:ℝ) ≤ 16 / Real.log H := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hHTr h16]
  calc
    _ ≤ cutoff / Real.log H * H + ((H : ℝ) * (16 / Real.log H) / ((T : ℝ) * a)) *
        (dilatedLargeFrequencies T D h c₁ a s w (cutoff / Real.log H)).card * (ζ * H) := hbound
    _ ≤ cutoff / Real.log H * H + ((16 / Real.log H) / a) * ((a : ℝ) * N) * (ζ * H) := by
      gcongr
    _ = (cutoff + 16 * ζ * N) * (H / Real.log H) := by field_simp
    _ ≤ (η / 32) * (H / Real.log H) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = η * H / (32 * Real.log H) := by ring

end

end NormalNumbers.ElliottDilatedUpper

#print axioms
  NormalNumbers.ElliottDilatedUpper.norm_dilatedPairTwistedMean_le_largeFrequencies_snd
#print axioms
  NormalNumbers.ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment_snd
