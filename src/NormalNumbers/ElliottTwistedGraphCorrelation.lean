import NormalNumbers.ElliottTwistedGraphBounded

/-!
# Correlation transfer for the pair-twisted prime graph

The rung above `NormalNumbers.ElliottTwistedGraphBounded`: the port of
`Erdos67b.norm_logProb_primeGraph_sub_correlation_le` and the chain that leads from it to
`Erdos67b.exists_logProb_dyadic_primeGraphMean_lower`.

**The point of the twist, finally cashed.**  In the proved (conjugate) case every graph edge of step
`p·h` contributes the *same* correlation `C_h` because `f(pn) conj(f(pn+ph)) = f(n) conj(f(n+h))`
exactly.  For two independent functions that identity fails by the factor `f₁(p) f₂(p)`, which varies
with `p` and can cancel the sum.  Attaching the known unimodular weight `pairTwist f₁ f₂ p =
conj (f₁ p · f₂ p)` restores it exactly (`pair_dilation_twisted`), and therefore:

> the pair-twisted graph's correlation coefficient is **literally** the dependency's
> `Erdos67b.primeGraphCorrelationWeight H h s` — the same real number, with no loss and no new
> parameter.  In particular `exists_dyadic_primeGraphCorrelationWeight_lower` applies unchanged,
> as it depends only on `H`, `h` and the prime set.

Contents:
* `pairTwistedSum_natCast`, `pairTwistedSum_sequenceBlock` — the CRT value in terms of genuine
  non-wrapping edges of the original sequences.
* `norm_logProb_pairTwistedGraph_sub_correlation_le` — the full graph average, with the
  dependency's error `π(H)·H·(2/M + 2H/(L·M))`.
* `norm_logProb_pairTwistedMean_sub_correlation_le` — the same with the CRT sum traded for the
  uniform-residue mean, at the cost of the decoupling error.
* `exists_logProb_pairTwistedMean_correlation`,
  `exists_logProb_pairTwistedMean_correlation_close` — entropy-selected scale, all window errors
  discharged by one harmonic-mass threshold (`Erdos67b.exists_uniform_primeGraph_window_error`
  applies verbatim, being function-free).
* `exists_logProb_dyadic_pairTwistedMean_lower` — **a large pair correlation forces a large
  pair-twisted graph mean**, the lower-bound half of the crux, with the dependency's constant `16`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-! ## The CRT value on an actual sequence block -/

/-- Compare `Erdos67b.primeGraphSum_natCast`. -/
theorem pairTwistedSum_natCast {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h n : ℕ) (s : Finset ℕ) :
    pairTwistedSum w b c h s (n : ZMod (primeGraphModulus H)) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if p.1 ∣ n + j.1 + 1 then w p.1 * pairShiftEdge b c (p.1 * h) j else 0
      else 0 := by
  have hcrt (p : PrimeGraphIndex H) :
      ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1) (primeGraphModuli_pairwise H)
        (n : ZMod (primeGraphModulus H)) p = (n : ZMod p.1) :=
    congrFun (map_natCast
      (ZMod.prodEquivPi (fun q : PrimeGraphIndex H ↦ q.1) (primeGraphModuli_pairwise H)) n) p
  simp only [pairTwistedSum, crtComplexSum, pairTwistedObservable, pairTwistedCoordinate,
    hcrt, ← Nat.cast_add, ZMod.natCast_eq_zero_iff, Nat.add_assoc]

/-- Compare `Erdos67b.primeGraphSum_sequenceBlock`. -/
theorem pairTwistedSum_sequenceBlock (w : ℕ → ℂ) (f₁ f₂ : ℕ → ℂ) (H h n : ℕ) (s : Finset ℕ) :
    pairTwistedSum w (finiteSequenceBlock f₁ H n) (finiteSequenceBlock f₂ H n) h s
        (n : ZMod (primeGraphModulus H)) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then
          pairTwistedDivisibleObservable w f₁ f₂ p.1 h (n + (j.1 + 1)) else 0
      else 0 := by
  classical
  rw [pairTwistedSum_natCast]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  split_ifs with hp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j.1 + p.1 * h < H <;>
      simp [pairShiftEdge, finiteSequenceBlock, pairTwistedDivisibleObservable, hj,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · rfl

/-! ## The complete graph average -/

/-- **The complete pair-twisted graph average.**  Port of
`Erdos67b.norm_logProb_primeGraph_sub_correlation_le`.  The correlation coefficient is *exactly*
the dependency's `primeGraphCorrelationWeight`, and the error is the dependency's verbatim. -/
theorem norm_logProb_pairTwistedGraph_sub_correlation_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {f₁ f₂ : ℕ → ℂ}
    (hm₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hm₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n, 0 < n → ‖f₂ n‖ = 1)
    (H h : ℕ) (s : Finset ℕ) :
    ‖logProbExpectation L U (fun n ↦
        pairTwistedSum (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h s (n : ZMod (primeGraphModulus H))) -
      primeGraphCorrelationWeight H h s • pairLogCorrelation L U f₁ f₂ h‖ ≤
        (Nat.primeCounting H : ℝ) * H *
          (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)) := by
  classical
  set C := pairLogCorrelation L U f₁ f₂ h with hC
  set e := 2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U) with he'
  have he : 0 ≤ e := by rw [he']; positivity
  let A (p : PrimeGraphIndex H) (j : Fin H) : ℂ :=
    logProbExpectation L U (fun n ↦
      pairTwistedDivisibleObservable (pairTwist f₁ f₂) f₁ f₂ p.1 h (n + (j.1 + 1)))
  have hedge (p : PrimeGraphIndex H) (j : Fin H) : ‖A p j - (p.1 : ℝ)⁻¹ • C‖ ≤ e := by
    have hh := norm_logProb_pairTwistedDivisible_sub_correlation_le hL hLU
      (Nat.prime_of_mem_primesLE p.2).pos hm₁ hm₂ hu₁ hu₂ h (j.1 + 1)
    refine hh.trans ?_
    rw [he']
    gcongr
    exact_mod_cast (by omega : j.1 + 1 ≤ H)
  have hexpect : logProbExpectation L U (fun n ↦
        pairTwistedSum (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h s (n : ZMod (primeGraphModulus H))) =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then A p j else 0 else 0 := by
    simp_rw [pairTwistedSum_sequenceBlock]
    rw [logProbExpectation_finset_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.1 ∈ s
    · simp only [hp, if_true]
      rw [logProbExpectation_finset_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : j.1 + p.1 * h < H
      · simp only [hj, if_true]; rfl
      · simp [hj, logProbExpectation]
    · simp [hp, logProbExpectation]
  have hcoef : primeGraphCorrelationWeight H h s • C =
      ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0 else 0 := by
    rw [primeGraphCorrelationWeight, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.1 ∈ s
    · simp only [hp, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, card_fin_add_lt, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, div_eq_mul_inv]
    · simp [hp]
  rw [hexpect, hcoef, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : PrimeGraphIndex H, ‖(if p.1 ∈ s then
        ∑ j : Fin H, if j.1 + p.1 * h < H then A p j else 0 else 0) -
      (if p.1 ∈ s then ∑ j : Fin H,
        if j.1 + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0 else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, (H : ℝ) * e := by
      refine Finset.sum_le_sum fun p _ ↦ ?_
      by_cases hp : p.1 ∈ s
      · simp only [hp, if_true, ← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ j : Fin H, ‖(if j.1 + p.1 * h < H then A p j else 0) -
              (if j.1 + p.1 * h < H then (p.1 : ℝ)⁻¹ • C else 0)‖ := norm_sum_le _ _
          _ ≤ ∑ _j : Fin H, e := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            by_cases hj : j.1 + p.1 * h < H
            · simpa only [hj, if_true] using hedge p j
            · simpa only [hj, if_false, sub_zero, norm_zero] using he
          _ = H * e := by simp
      · simp only [hp, if_false, sub_zero, norm_zero]
        positivity
    _ = (Nat.primeCounting H : ℝ) * H * e := by
      rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul, mul_assoc]

/-! ## Trading the CRT sum for the uniform-residue mean -/

/-- Port of `Erdos67b.norm_logProb_primeGraphMean_sub_correlation_le`. -/
theorem norm_logProb_pairTwistedMean_sub_correlation_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {f₁ f₂ : ℕ → ℂ}
    (hm₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hm₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n, 0 < n → ‖f₂ n‖ = 1)
    (H h : ℕ) (s : Finset ℕ) {e : ℝ}
    (hdec : ‖logProbExpectation L U
      (pairTwistedDiscrepancy (pairTwist f₁ f₂) f₁ f₂ H h s)‖ ≤ e) :
    ‖logProbExpectation L U (fun n ↦
        pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
          (finiteSequenceBlock f₂ H n) h s) -
        primeGraphCorrelationWeight H h s • pairLogCorrelation L U f₁ f₂ h‖ ≤
      e + (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)) := by
  have herr := norm_logProb_pairTwistedGraph_sub_correlation_le hL hLU hm₁ hm₂ hu₁ hu₂ H h s
  change ‖logProbExpectation L U (fun n ↦
    pairTwistedSum (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h s (n : ZMod (primeGraphModulus H)) -
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h s)‖ ≤ e at hdec
  rw [logProbExpectation_sub] at hdec
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logProbExpectation L U (fun n ↦
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h s))
    (logProbExpectation L U (fun n ↦
      pairTwistedSum (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h s (n : ZMod (primeGraphModulus H))))
    (primeGraphCorrelationWeight H h s • pairLogCorrelation L U f₁ f₂ h)
  rw [norm_sub_rev
    (logProbExpectation L U (fun n ↦
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h s))
    (logProbExpectation L U (fun n ↦
      pairTwistedSum (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h s (n : ZMod (primeGraphModulus H))))] at htri
  linarith

/-! ## The entropy-selected scale -/

/-- Port of `Erdos67b.exists_logProb_primeGraphMean_correlation`. -/
theorem exists_logProb_pairTwistedMean_correlation
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
      ∃ j : ℕ, j < J ∧ ∀ h : ℕ, ∀ s : Finset ℕ,
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U (fun n ↦
            pairTwistedMeanCRT (pairTwist f₁ f₂)
              (finiteSequenceBlock f₁ (entropyScale H₀ j) n)
              (finiteSequenceBlock f₂ (entropyScale H₀ j) n) h s) -
            primeGraphCorrelationWeight (entropyScale H₀ j) h s •
              pairLogCorrelation L U f₁ f₂ h‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) +
            (Nat.primeCounting (entropyScale H₀ j) : ℝ) * entropyScale H₀ j *
            (2 / (logProbMassNN L U : ℝ) +
              2 * entropyScale H₀ j / ((L : ℝ) * logProbMassNN L U)) := by
  obtain ⟨H₀, J, L₀, hHmin, hH₀, hJ, hL₀, hcontrol⟩ :=
    exists_logProb_bounded_pairTwisted_decoupling hδ hε Hmin
  refine ⟨H₀, J, L₀, hHmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL f₁ f₂ hm₁ hm₂ hu₁ hu₂
  -- the graph never reads the value at `0`; replace it by `0` so the bounds are global
  let g₁ : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f₁ n
  let g₂ : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f₂ n
  have hg₁ : ∀ n, ‖g₁ n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [g₁, hn]
    · simp only [g₁, hn, if_false]
      exact (hu₁ n (Nat.pos_of_ne_zero hn)).le
  have hg₂ : ∀ n, ‖g₂ n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [g₂, hn]
    · simp only [g₂, hn, if_false]
      exact (hu₂ n (Nat.pos_of_ne_zero hn)).le
  obtain ⟨j, hj, hdec⟩ := hcontrol L U hL hU hLL g₁ g₂ hg₁ hg₂
  refine ⟨j, hj, ?_⟩
  intro h s hs
  set H := entropyScale H₀ j with hHdef
  -- blocks only ever read strictly positive arguments, so `f` and `g` give the same graph
  have hblk₁ (n : ℕ) : finiteSequenceBlock g₁ H n = finiteSequenceBlock f₁ H n := by
    funext i
    simp only [finiteSequenceBlock, g₁, Nat.succ_ne_zero, if_false]
  have hblk₂ (n : ℕ) : finiteSequenceBlock g₂ H n = finiteSequenceBlock f₂ H n := by
    funext i
    simp only [finiteSequenceBlock, g₂, Nat.succ_ne_zero, if_false]
  have htwist : ∀ p ∈ s, ‖pairTwist f₁ f₂ p‖ ≤ 1 := by
    intro p hp
    have hppos : 0 < p := by
      have hpH := hs p hp
      have : (0 : ℝ) < δ * H := by
        have : 0 < H := lt_of_lt_of_le (by omega) (le_entropyScale H₀ j)
        positivity
      have hpr : (0 : ℝ) < p := lt_of_lt_of_le this hpH
      exact_mod_cast hpr
    exact (norm_pairTwist hu₁ hu₂ hppos).le
  have hdec' := hdec (pairTwist f₁ f₂) h s htwist hs
  have hsame : pairTwistedDiscrepancy (pairTwist f₁ f₂) g₁ g₂ H h s =
      pairTwistedDiscrepancy (pairTwist f₁ f₂) f₁ f₂ H h s := by
    funext n
    simp only [pairTwistedDiscrepancy, hblk₁, hblk₂]
  rw [hsame] at hdec'
  exact norm_logProb_pairTwistedMean_sub_correlation_le hL (by omega) hm₁ hm₂ hu₁ hu₂ H h s hdec'

/-- Port of `Erdos67b.exists_logProb_primeGraphMean_correlation_close`.  The window-error threshold
`Erdos67b.exists_uniform_primeGraph_window_error` is function-free, so it applies verbatim. -/
theorem exists_logProb_pairTwistedMean_correlation_close
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
      ∃ j : ℕ, j < J ∧ ∀ h : ℕ, ∀ s : Finset ℕ,
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U (fun n ↦
            pairTwistedMeanCRT (pairTwist f₁ f₂)
              (finiteSequenceBlock f₁ (entropyScale H₀ j) n)
              (finiteSequenceBlock f₂ (entropyScale H₀ j) n) h s) -
            primeGraphCorrelationWeight (entropyScale H₀ j) h s •
              pairLogCorrelation L U f₁ f₂ h‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨H₀, J, L₀, hmin, hH₀, hJ, hL₀, hcontrol⟩ :=
    exists_logProb_pairTwistedMean_correlation hδ hhalf Hmin
  let S : Finset ℕ := (Finset.range J).image (entropyScale H₀)
  have hS : ∀ H ∈ S, 2 ≤ H := by
    intro H hH
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hH
    exact hH₀.trans (le_entropyScale H₀ j)
  obtain ⟨W₀, hW₀, hwindow⟩ := exists_uniform_primeGraph_window_error S hS hhalf
  refine ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂
  obtain ⟨j, hj, hcorr⟩ := hcontrol L U hL hU hLL f₁ f₂ hm₁ hm₂ hu₁ hu₂
  refine ⟨j, hj, ?_⟩
  intro h s hs
  have hmem : entropyScale H₀ j ∈ S := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have hw := hwindow (entropyScale H₀ j) hmem L U hL (by omega) hWM
  have hc := hcorr h s hs
  apply hc.trans
  calc
    _ ≤ ε / 2 * entropyScale H₀ j / Real.log (entropyScale H₀ j) +
        ε / 2 * entropyScale H₀ j / Real.log (entropyScale H₀ j) := add_le_add le_rfl hw
    _ = ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by ring

/-! ## The lower bound -/

/-- **A large pair correlation forces a large pair-twisted graph mean.**  Port of
`Erdos67b.exists_logProb_dyadic_primeGraphMean_lower`, with the dependency's constant `16`.  The
active dyadic prime block and every scale and window budget are the dependency's, because the
correlation coefficient is literally `primeGraphCorrelationWeight`. -/
theorem exists_logProb_dyadic_pairTwistedMean_lower
    {η : ℝ} (hη : 0 < η) (h Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f₁ f₂ : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f₁ →
        IsCompletelyMultiplicativeOnPositive f₂ →
        (∀ n, 0 < n → ‖f₁ n‖ = 1) → (∀ n, 0 < n → ‖f₂ n‖ = 1) →
        η ≤ ‖pairLogCorrelation L U f₁ f₂ h‖ →
      ∃ j : ℕ, j < J ∧
        η * entropyScale H₀ j / (16 * Real.log (entropyScale H₀ j)) ≤
          ‖logProbExpectation L U (fun n ↦
            pairTwistedMeanCRT (pairTwist f₁ f₂)
              (finiteSequenceBlock f₁ (entropyScale H₀ j) n)
              (finiteSequenceBlock f₂ (entropyScale H₀ j) n) h
              (PrimeEstimates.dyadicPrimes (entropyScale H₀ j / (4 * h + 4))))‖ := by
  obtain ⟨P₀, hP₀, hweight⟩ := exists_dyadic_primeGraphCorrelationWeight_lower
  let K : ℕ := 4 * h + 4
  have hK : 0 < K := by dsimp [K]; omega
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  let δ : ℝ := 1 / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, hcontrol⟩ :=
    exists_logProb_pairTwistedMean_correlation_close hδ
      (show 0 < η / 16 by positivity) (max Hmin (K * P₀))
  refine ⟨H₀, J, L₀, W₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂ hcorr
  obtain ⟨j, hj, hclose⟩ := hcontrol L U hL hU hLL hWM f₁ f₂ hm₁ hm₂ hu₁ hu₂
  set H := entropyScale H₀ j with hHdef
  set P := H / K with hPdef
  have hHH : K * P₀ ≤ H :=
    ((le_max_right _ _).trans hmin).trans (le_entropyScale H₀ j)
  have hPP : P₀ ≤ P := (Nat.le_div_iff_mul_le hK).mpr (by simpa only [mul_comm] using hHH)
  have hP2 : 2 ≤ P := hP₀.trans hPP
  have hdiv : P * K ≤ H := Nat.div_mul_le_self H K
  have hPH : 2 * P ≤ H := by dsimp [K] at hdiv; nlinarith
  have hstep : 4 * P * h ≤ H := by dsimp [K] at hdiv; nlinarith
  have hPlt : H < K * (P + 1) := Nat.lt_mul_div_succ H hK
  have hscale : (H : ℝ) / (2 * K) ≤ P := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
    have hcast : (H : ℝ) < K * ((P : ℝ) + 1) := by exact_mod_cast hPlt
    have hPr : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
    nlinarith
  have hs : ∀ p ∈ PrimeEstimates.dyadicPrimes P, δ * H ≤ p := by
    intro p hp
    have hPp := (PrimeEstimates.mem_primesInInterval.mp hp).1
    calc
      δ * H = (H : ℝ) / (2 * K) := by dsimp [δ]; ring
      _ ≤ P := hscale
      _ ≤ p := by exact_mod_cast hPp.le
  have hclose' := hclose h (PrimeEstimates.dyadicPrimes P) hs
  have hw := hweight P hPP H h hPH hstep
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlogH : 0 < Real.log (H : ℝ) := log_entropyScale_pos hH₀ j
  have hlogle : Real.log (P : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : P ≤ H))
  have hw' : (H : ℝ) / (8 * Real.log H) ≤
      primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) := by
    apply le_trans _ hw
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hw0 := primeGraphCorrelationWeight_nonneg H h (PrimeEstimates.dyadicPrimes P)
  have hprod := mul_le_mul hw' hcorr hη.le hw0
  have htri := norm_le_norm_add_norm_sub
    (logProbExpectation L U (fun n ↦
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h (PrimeEstimates.dyadicPrimes P)))
    (primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) •
      pairLogCorrelation L U f₁ f₂ h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0] at htri
  refine ⟨j, hj, ?_⟩
  change η * H / (16 * Real.log H) ≤ _
  have hbudget : (H : ℝ) / (8 * Real.log H) * η =
      η * H / (16 * Real.log H) + η / 16 * H / Real.log H := by ring
  rw [hbudget] at hprod
  change ‖logProbExpectation L U (fun n ↦
      pairTwistedMeanCRT (pairTwist f₁ f₂) (finiteSequenceBlock f₁ H n)
        (finiteSequenceBlock f₂ H n) h (PrimeEstimates.dyadicPrimes P)) -
        primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) •
          pairLogCorrelation L U f₁ f₂ h‖ ≤
      η / 16 * H / Real.log H at hclose'
  linarith

end

end NormalNumbers.ElliottTwistedGraph
