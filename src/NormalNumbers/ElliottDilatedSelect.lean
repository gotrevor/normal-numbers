import NormalNumbers.ElliottGenericGraphBounded

/-!
# The entropy-selected scale for the dilated graph

Step (iii)(c), first half.  The three proved ingredients

* `NormalNumbers.ElliottGenericGraph.exists_logProb_bounded_dilated_decoupling` (lap 40) — the
  dilated graph decouples for arbitrary unit-disk sequences, at an arbitrary CRT residue shift;
* `NormalNumbers.ElliottDilatedMean.norm_logProb_dilatedMean_sub_correlation_le` (lap 37) — with
  such a decoupling bound in hand, the dilated *mean* is `dilatedCorrelationWeight` times the affine
  correlation, up to the window errors;
* a uniform window-error threshold (`exists_uniform_dilated_window_error`, this file: the dilated
  analogue of `Erdos67b.exists_uniform_primeGraph_window_error`, with the extra base-point term
  `2 Dmax/(L M)` coming from the backward shift `⌊p c₁ / a⌋ ≤ c₁ H`),

are combined into `exists_logProb_dilatedMean_correlation_close`: at the entropy-selected scale
`H = a · entropyScale H₀ j`, the dilated mean is within `ε H / log H` of
`dilatedCorrelationWeight H a c₁ h s • affineLogCorrelation L U f₁ f₂ a c₁ (c₁+h)`, uniformly over
all admissible prime sets `s`.

The residue shift fed to the decoupling is `Δ m = crtShift (a m) (fun p ↦ ⌊p c₁ / a⌋)`, i.e.
`NormalNumbers.ElliottDilatedMean.dilatedShift`, which is exactly the residue at which the dilated
graph sum computes the affine correlation.

Because the graph reads the block at base point `a(n+1)` and shifts the *index* back by at most
`c₁ H`, the lower threshold `L₀` has to dominate `c₁ H` for every one of the finitely many scales
`H` in play; that is the only new bookkeeping.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottDilatedSelect

open Erdos67b
open Erdos67b.FiniteEntropy
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottAffineGraph
open NormalNumbers.ElliottGenericGraph
open NormalNumbers.ElliottDilatedBridge
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottDilatedCorrelation
open NormalNumbers.ElliottDilatedMean

noncomputable section

/-! ## The uniform window-error threshold, with the dilated base-point term -/

/-- Dilated analogue of `Erdos67b.exists_uniform_primeGraph_window_error`: the same finite-threshold
argument, with the extra term `2 c H/(L M)` produced by the backward base-point shift.  Function
free, so one threshold serves all functions and all prime sets. -/
theorem exists_uniform_dilated_window_error (S : Finset ℕ) (hS : ∀ H ∈ S, 2 ≤ H) (c : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℝ, 0 < W₀ ∧ ∀ H ∈ S, ∀ L U : ℕ,
      0 < L → L ≤ U → W₀ ≤ (logProbMassNN L U : ℝ) →
      (Nat.primeCounting H : ℝ) * H *
          (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U) +
            2 * ((c * H : ℕ) : ℝ) / ((L : ℝ) * logProbMassNN L U)) ≤
        ε * H / Real.log H := by
  classical
  let B : ℕ → ℝ := fun H ↦ (Nat.primeCounting H : ℝ) * H * (2 + 2 * H + 2 * (c * H : ℕ))
  let t : ℕ → ℝ := fun H ↦ ε * H / Real.log H
  have ht (H : ℕ) (hH : H ∈ S) : 0 < t H := by
    have hH2 := hS H hH
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
    have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    dsimp [t]; positivity
  have hB (H : ℕ) : 0 ≤ B H := by dsimp [B]; positivity
  have hterms (H : ℕ) (hH : H ∈ S) : 0 ≤ B H / t H := div_nonneg (hB H) (ht H hH).le
  let W₀ : ℝ := 1 + ∑ H ∈ S, B H / t H
  have hW₀ : 0 < W₀ := by
    have hsum := Finset.sum_nonneg hterms
    dsimp [W₀]; linarith
  refine ⟨W₀, hW₀, ?_⟩
  intro H hH L U hL hLU hWM
  have hM : (0 : ℝ) < logProbMassNN L U := by exact_mod_cast logProbMassNN_pos hL hLU
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (logProbMassNN L U : ℝ) ≤ (L : ℝ) * logProbMassNN L U := by nlinarith
  have hshift := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * H) hM hden
  have hshift' := div_le_div_of_nonneg_left
    (by positivity : (0 : ℝ) ≤ 2 * ((c * H : ℕ) : ℝ)) hM hden
  have hbudget : B H / t H ≤ (logProbMassNN L U : ℝ) := by
    have hsingle := Finset.single_le_sum hterms hH
    dsimp [W₀] at hWM
    linarith
  have hbudget' : B H / (logProbMassNN L U : ℝ) ≤ t H := by
    apply (div_le_iff₀ hM).mpr
    have hh := (div_le_iff₀ (ht H hH)).mp hbudget
    simpa only [mul_comm] using hh
  calc
    _ ≤ (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / (logProbMassNN L U : ℝ) +
          2 * ((c * H : ℕ) : ℝ) / (logProbMassNN L U : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hshift) hshift') (by positivity)
    _ = B H / (logProbMassNN L U : ℝ) := by dsimp [B]; ring
    _ ≤ t H := hbudget'

/-! ## The entropy-selected dilated mean -/

/-- **Step (iii)(c), first half: the dilated mean at the entropy-selected scale.**  Dilated analogue
of `NormalNumbers.ElliottTwistedGraph.exists_logProb_pairTwistedMean_correlation_close`. -/
theorem exists_logProb_dilatedMean_correlation_close
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {a : ℕ} (ha : 0 < a) (c₁ h : ℕ) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ a ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
      ∃ j : ℕ, j < J ∧ ∀ s : Finset ℕ,
        s ⊆ Nat.primesLE (a * entropyScale H₀ j) →
        (∀ p ∈ s, δ * (a * entropyScale H₀ j : ℕ) ≤ p) →
        ‖logProbExpectation L U (fun n ↦
            dilatedPairTwistedMean (pairTwist f₁ f₂)
              (affineBlock f₁ a n (a * entropyScale H₀ j))
              (affineBlock f₂ a n (a * entropyScale H₀ j)) a c₁ h s) -
            dilatedCorrelationWeight (a * entropyScale H₀ j) a c₁ h s •
              affineLogCorrelation L U f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)‖ ≤
          ε * (a * entropyScale H₀ j : ℕ) /
            Real.log ((a * entropyScale H₀ j : ℕ) : ℝ) := by
  classical
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨H₀, J, L₀, hmin, hH₀, hH₀a, hJ, hL₀, hdecouple⟩ :=
    exists_logProb_bounded_dilated_decoupling hδ hhalf ha c₁ h
      (fun m ↦ dilatedShift (a * m) a c₁) Hmin
  -- the finitely many scales in play
  let S : Finset ℕ := (Finset.range J).image (fun j ↦ a * entropyScale H₀ j)
  have hS : ∀ H ∈ S, 2 ≤ H := by
    intro H hH
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hH
    have h1 : 2 ≤ entropyScale H₀ j := hH₀.trans (le_entropyScale H₀ j)
    have h2 : entropyScale H₀ j ≤ a * entropyScale H₀ j := Nat.le_mul_of_pos_left _ ha
    omega
  obtain ⟨W₀, hW₀, hwindow⟩ := exists_uniform_dilated_window_error S hS c₁ hhalf
  -- the threshold `L₀` must dominate the base-point shift at every scale in play
  let Lmax : ℕ := S.sup (fun H ↦ c₁ * H)
  refine ⟨H₀, J, max L₀ (Lmax + 1), W₀, hmin, hH₀, hH₀a, hJ, by omega, hW₀, ?_⟩
  intro L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂
  obtain ⟨j, hj, hdec⟩ := hdecouple L U hL hU ((le_max_left _ _).trans hLL)
    f₁ f₂ (fun n hn ↦ (hu₁ n hn).le) (fun n hn ↦ (hu₂ n hn).le)
  refine ⟨j, hj, ?_⟩
  intro s hsprimes hs
  set m := entropyScale H₀ j with hmdef
  set H := a * m with hHdef
  have hmH₀ : H₀ ≤ m := le_entropyScale H₀ j
  have hmH : m ≤ H := Nat.le_mul_of_pos_left m ha
  have hH2 : 2 ≤ H := (hH₀.trans hmH₀).trans hmH
  have hHS : H ∈ S := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  -- the twist is unimodular on the active primes
  have htwist : ∀ p ∈ s, ‖pairTwist f₁ f₂ p‖ ≤ 1 := by
    intro p hp
    have hppos : 0 < p := (Nat.prime_of_mem_primesLE (hsprimes hp)).pos
    exact (norm_pairTwist hu₁ hu₂ hppos).le
  have hdec' := hdec (pairTwist f₁ f₂) s htwist hs
  -- the base-point shift is bounded by `c₁ H`, and `L` dominates it
  have hD : ∀ p : PrimeGraphIndex H, p.1 * c₁ / a ≤ c₁ * H := by
    intro p
    have hpH : p.1 ≤ H := (Nat.mem_primesLE.mp p.2).1
    calc p.1 * c₁ / a ≤ p.1 * c₁ := Nat.div_le_self _ _
      _ ≤ c₁ * H := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left c₁ hpH
  have hDL : c₁ * H ≤ L := by
    have hsup : c₁ * H ≤ Lmax := Finset.le_sup (f := fun H ↦ c₁ * H) hHS
    have := (le_max_right L₀ (Lmax + 1)).trans hLL
    omega
  have hmain := norm_logProb_dilatedMean_sub_correlation_le hL (by omega : L ≤ U)
    hm₁ hm₂ hu₁ hu₂ (H := H) ha c₁ h hsprimes hD hDL hdec'
  have hwin := hwindow H hHS L U hL (by omega) hWM
  refine hmain.trans ?_
  have hHcast : ((H : ℕ) : ℝ) = ((a * entropyScale H₀ j : ℕ) : ℝ) := by rw [hHdef]
  calc
    ε / 2 * (H : ℕ) / Real.log ((H : ℕ) : ℝ) +
        (Nat.primeCounting H : ℝ) * H *
          (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U) +
            2 * ((c₁ * H : ℕ) : ℝ) / ((L : ℝ) * logProbMassNN L U))
        ≤ ε / 2 * (H : ℕ) / Real.log ((H : ℕ) : ℝ) +
            ε / 2 * (H : ℕ) / Real.log ((H : ℕ) : ℝ) := add_le_add le_rfl hwin
    _ = ε * (H : ℕ) / Real.log ((H : ℕ) : ℝ) := by ring

end

end NormalNumbers.ElliottDilatedSelect

#print axioms NormalNumbers.ElliottDilatedSelect.exists_logProb_dilatedMean_correlation_close
