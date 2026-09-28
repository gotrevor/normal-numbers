import NormalNumbers.ElliottDilatedPairing

/-!
# The upper-bound assembly for the `a`-dilated prime graph

`NormalNumbers.ElliottDilatedPairing` proved every ingredient of the dilated Fourier stack.  This
file assembles them into the dilated analogue of
`NormalNumbers.ElliottTwistedGraph.exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`.

Two things have to be arranged.

* **The modulus must factor.**  The dilated orthogonality needs `T = α * D` with `α = a`.  We take
  `D = 4*h*H + 1` (the dependency's modulus) and `T = a * D`.  The only place this is felt is the
  fourth-moment bound, whose proof is stated for an arbitrary modulus `T > 4*P*h`; carrying it at
  `T = a*(4*h*H+1)` multiplies the constant by `a`, and `a` is fixed before the parameters are
  chosen, so it is absorbed exactly as the dependency absorbs its own `C`
  (`exists_eventually_scaledTwistedMultiplier_bounds` below).

* **The alias factor must cancel.**  The dilated large-frequency bound carries a prefactor
  `H * M / (T * α)` and the frequency count is `α` times the undilated one.  These cancel: the
  final budget `cutoff + 16 ζ N ≤ η/32` is *verbatim* the dependency's, with no `α` in it.

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

/-- **The multiplier bounds at the scaled modulus `a * (4*h*H + 1)`.**  Port of
`NormalNumbers.ElliottTwistedGraph.exists_eventually_twistedPrimeGraphMultiplier_bounds`; the
modulus is scaled by the fixed constant `a`, which multiplies the fourth-moment constant by `a`
and leaves the supremum bound untouched (it does not see `T` at all). -/
theorem exists_eventually_scaledTwistedMultiplier_bounds {h a : ℕ} (hh : 0 < h) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖w p‖ ≤ 1) →
      (∑ t ∈ Finset.range (a * (4 * h * H + 1)),
        ‖twistedPrimeGraphMultiplier (a * (4 * h * H + 1)) h
          (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) w (t : ℤ)‖ ^ 4 ≤
            C / Real.log H ^ 4) ∧
        ∀ t : ℤ, ‖twistedPrimeGraphMultiplier (a * (4 * h * H + 1)) h
          (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))) w t‖ ≤ 16 / Real.log H := by
  obtain ⟨A, hA, P₀, hP₀, hfourth⟩ := exists_dyadic_twistedPrimeGraphMultiplier_fourth_moment_bound
  obtain ⟨P₁, hprime⟩ := Filter.eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  let K : ℕ := 4 * h + 4
  have hK : 2 ≤ K := by dsimp [K]; omega
  let P₂ : ℕ := max (max P₀ P₁) (2 * K)
  have hP₂ : 2 * K ≤ P₂ := le_max_right _ _
  let C : ℝ := 32 * A * K * (4 * h + 1) * a
  have hC : 0 < C := by
    have : (0:ℝ) < a := by exact_mod_cast ha
    dsimp [C]; positivity
  refine ⟨C, hC, max 2 (K * P₂), le_max_left _ _, ?_⟩
  intro H hHH w hw
  set P := H / K with hPdef
  set T := a * (4 * h * H + 1) with hTdef
  obtain ⟨hPP₂, hPH, hratio, hlogP, hlogH, hlogratio⟩ :=
    primeGraph_quotient_comparisons hK hP₂ ((le_max_right _ _).trans hHH)
  have hPP₀ : P₀ ≤ P := ((le_max_left _ _).trans (le_max_left _ _)).trans hPP₂
  have hPP₁ : P₁ ≤ P := ((le_max_right _ _).trans (le_max_left _ _)).trans hPP₂
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hPr : (0 : ℝ) < P := by positivity
  have hHpos : 0 < H := by
    have : 2 ≤ H := (le_max_left _ _).trans hHH
    omega
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hTr : (T : ℝ) ≤ a * ((4 * h + 1) * H) := by
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hHpos
    rw [hTdef]
    push_cast
    nlinarith
  have hTP : (T : ℝ) / P ≤ a * (2 * K * (4 * h + 1)) := by
    apply (div_le_iff₀ hPr).mpr
    nlinarith
  have hlogInv : (1 : ℝ) / Real.log P ^ 4 ≤ 16 / Real.log H ^ 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hpow := pow_le_pow_left₀ hlogH.le hlogratio 4
    nlinarith [hpow]
  have hTlow : 4 * P * h < T := by
    have hPH' : P ≤ H := by rw [hPdef]; omega
    have hmul := Nat.mul_le_mul_left (4 * h) hPH'
    have hle : 4 * h * H + 1 ≤ T := hTdef ▸ Nat.le_mul_of_pos_left (4 * h * H + 1) ha
    calc 4 * P * h = 4 * h * P := by ring
      _ ≤ 4 * h * H := hmul
      _ < 4 * h * H + 1 := by omega
      _ ≤ T := hle
  have h4 := hfourth P hPP₀ T h hh hTlow w hw
  constructor
  · calc
      _ ≤ A * T / ((P : ℝ) * Real.log P ^ 4) := h4
      _ = A * ((T : ℝ) / P) * (1 / Real.log P ^ 4) := by ring
      _ ≤ A * (a * (2 * K * (4 * h + 1))) * (16 / Real.log H ^ 4) := by gcongr
      _ = C / Real.log H ^ 4 := by dsimp [C]; ring
  · intro t
    have hp := hprime (2 * P) (by omega)
    have hlog2P : 0 < Real.log (2 * P : ℕ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * P))
    have hlogle : Real.log (P : ℝ) ≤ Real.log (2 * P : ℕ) :=
      Real.log_le_log hPr (by exact_mod_cast (by omega : P ≤ 2 * P))
    calc
      _ ≤ (Nat.primeCounting (2 * P) : ℝ) / P :=
        norm_dyadic_twistedPrimeGraphMultiplier_le_primeCounting T h (by omega) hw t
      _ ≤ (4 * (2 * P : ℕ) / Real.log (2 * P : ℕ)) / P :=
        div_le_div_of_nonneg_right (by simpa only [mul_div_assoc] using hp) hPr.le
      _ = 8 / Real.log (2 * P : ℕ) := by push_cast; field_simp; ring
      _ ≤ 8 / Real.log P := div_le_div_of_nonneg_left (by norm_num) hlogP hlogle
      _ ≤ 16 / Real.log H := by
        apply (div_le_div_iff₀ hlogP hlogH).mpr
        linarith

/-- **The dilated graph upper bound.**  Port of
`NormalNumbers.ElliottTwistedGraph.exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`
to the `a`-dilated mean.  The parameter choreography (`cutoff = η/64`, `N = C/cutoff⁴`,
`ζ = η/(1024(N+1))`, budget `cutoff + 16ζN ≤ η/32`) is the dependency's verbatim: the alias factor
`α = a` enters the frequency count and the prefactor with opposite exponents and cancels exactly,
and the only trace of the dilation is inside `C`. -/
theorem exists_dilatedPairTwistedMean_small_of_fourier_first_moment
    {h a c₁ : ℕ} (hh : 0 < h) (ha : 0 < a) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ L U : ℕ, 0 < L → L ≤ U → ∀ F₁ F₂ : ℕ → ℂ,
      (∀ n, 0 < n → ‖F₁ n‖ ≤ 1) → (∀ n, 0 < n → ‖F₂ n‖ ≤ 1) →
      ∀ w : ℕ → ℂ, (∀ p ∈ PrimeEstimates.dyadicPrimes (H / (4 * h + 4)), ‖w p‖ ≤ 1) →
      (∀ t : ℤ, logProbExpectation L U (fun n ↦
          ‖blockFourier (a * (4 * h * H + 1)) (affineBlock F₁ a n H) t‖) ≤ ζ * H) →
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
  -- the multiplier bounds, uniform in the twist
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
  have hbound := norm_logProb_dilatedPairTwistedMean_le_of_fourier_first_moment
    (T := T) (α := a) (D := D) rfl hL hLU w F₁ F₂ a c₁ h s hHT hnowrap hF₁ hF₂
    (θ := cutoff / Real.log H) (M := 16 / Real.log H) (Z := ζ * H)
    (by positivity) (by positivity) hsup
    (fun x _ ↦ hfirst ((x.1 : ℤ) + (x.2 : ℤ) * D))
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

#print axioms NormalNumbers.ElliottDilatedUpper.exists_eventually_scaledTwistedMultiplier_bounds
#print axioms
  NormalNumbers.ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment
