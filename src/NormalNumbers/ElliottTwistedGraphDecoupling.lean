import NormalNumbers.ElliottTwistedGraphCRT
import ErdosProblems.Erdos67b.PrimeGraphDecoupling

/-!
# Entropy decoupling for the pair-twisted prime graph

This is the rung above `NormalNumbers.ElliottTwistedGraphCRT`: the port of
`Erdos67b.exists_logProb_primeGraph_small_tail` and
`Erdos67b.exists_logProb_primeGraph_decoupling` to the phase-twisted, two-block prime graph.

The device that makes the two-block generalisation fit the entropy machinery unchanged is worth
naming, because it is the only genuinely new bookkeeping in the whole lower-bound port:

> The entropy argument selects a scale from **one** finite-alphabet sequence.  Tao's two-function
> setting has two sequences `f₁, f₂`.  We therefore run the entropy argument on a single sequence
> `F : ℕ → α` in a finite alphabet equipped with **two** decode maps `d₁, d₂ : α → ℂ`, and read the
> two graph blocks off the *same* block of `F` as `d₁ ∘ blk` and `d₂ ∘ blk`.  A single scale `j` then
> serves both functions simultaneously — which is exactly what the argument needs, and is why no
> second entropy budget appears.

Everything else is inherited verbatim:

* `Erdos67b.logProb_block_rare_event_le` is stated for an **arbitrary** rare-event family
  `E : (Fin H → α) → Finset (ZMod P)`, so the twisted two-block exceptional set is admissible with
  no change;
* `Erdos67b.exists_logProb_block_entropy_control` is stated for an arbitrary finite `α`, so the
  product alphabet costs nothing;
* `exists_pairTwisted_exponential_tail` (previous rung) supplies the Hoeffding input with the
  dependency's own constant.

Consequently the twist `w` and the second block may be chosen **after** the scale `j` — they are
quantified under `∀ h s` exactly as `h` and `s` are in the dependency.

Contents:
* `pairTwistedDiscrepancy` (+ `pairTwistedDiscrepancy_conj_one` anchor),
  `norm_pairTwistedDiscrepancy_le`.
* `exists_logProb_pairTwisted_small_tail` — port of
  `Erdos67b.exists_logProb_primeGraph_small_tail`.
* `exists_logProb_pairTwisted_decoupling` — port of
  `Erdos67b.exists_logProb_primeGraph_decoupling`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-- The centred pair-twisted graph observable on the actual sequence blocks and the residue of the
starting integer.  Compare `Erdos67b.primeGraphDiscrepancy`. -/
def pairTwistedDiscrepancy (w : ℕ → ℂ) (F G : ℕ → ℂ) (H h : ℕ) (s : Finset ℕ) (n : ℕ) : ℂ :=
  pairTwistedSum w (finiteSequenceBlock F H n) (finiteSequenceBlock G H n) h s
      (n : ZMod (primeGraphModulus H)) -
    pairTwistedMeanCRT w (finiteSequenceBlock F H n) (finiteSequenceBlock G H n) h s

/-- Faithfulness anchor: the dependency's discrepancy is the untwisted conjugate case. -/
theorem pairTwistedDiscrepancy_conj_one (F : ℕ → ℂ) (H h : ℕ) (s : Finset ℕ) (n : ℕ) :
    pairTwistedDiscrepancy (fun _ ↦ 1) F (fun m ↦ conj (F m)) H h s n =
      primeGraphDiscrepancy F H h s n := by
  simp only [pairTwistedDiscrepancy, primeGraphDiscrepancy]
  rw [show finiteSequenceBlock (fun m ↦ conj (F m)) H n =
    (fun i ↦ conj (finiteSequenceBlock F H n i)) from rfl,
    pairTwistedSum_conj_one, pairTwistedMeanCRT_conj_one]

theorem norm_pairTwistedDiscrepancy_le (w : ℕ → ℂ) (F G : ℕ → ℂ) (H h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hF : ∀ n, ‖F n‖ ≤ B) (hG : ∀ n, ‖G n‖ ≤ B) (hs : ∀ p ∈ s, δ * H ≤ p) (n : ℕ) :
    ‖pairTwistedDiscrepancy w F G H h s n‖ ≤
      2 * (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  have hb : ∀ j, ‖finiteSequenceBlock F H n j‖ ≤ B := fun j ↦ hF _
  have hc : ∀ j, ‖finiteSequenceBlock G H n j‖ ≤ B := fun j ↦ hG _
  have hsum := norm_pairTwistedSum_le w (finiteSequenceBlock F H n)
    (finiteSequenceBlock G H n) h s hB hδ hw hb hc hs (n : ZMod (primeGraphModulus H))
  have hmean := norm_pairTwistedMeanCRT_le w (finiteSequenceBlock F H n)
    (finiteSequenceBlock G H n) h s hB hδ hw hb hc hs
  exact (norm_sub_le _ _).trans (by linarith)

/-! ## The entropy-selected rare event -/

/-- Port of `Erdos67b.exists_logProb_primeGraph_small_tail`.  The scale `j` is selected from the
finite-alphabet sequence alone; the twist `w`, the shift `h` and the active primes `s` are all
chosen afterwards. -/
theorem exists_logProb_pairTwisted_small_tail
    {α : Type*} [Finite α] [Nonempty α]
    (d₁ d₂ : α → ℂ) {B δ ρ κ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hd₁ : ∀ a, ‖d₁ a‖ ≤ B) (hd₂ : ∀ a, ‖d₂ a‖ ≤ B) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J, ∀ (w : ℕ → ℂ) (h : ℕ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        finiteEventMass (logProbFiniteLaw L U hL (by omega))
          {n | ρ * entropyScale H₀ j / Real.log (entropyScale H₀ j) ≤
            ‖pairTwistedDiscrepancy w (d₁ ∘ F) (d₂ ∘ F) (entropyScale H₀ j) h s n.1‖} ≤ κ := by
  classical
  let _ := Fintype.ofFinite α
  obtain ⟨c, hc, H₁, hH₁, htail⟩ := exists_pairTwisted_exponential_tail hB hδ hρ
  obtain ⟨H₂, hH₂⟩ := eventually_atTop.mp (eventually_four_le_mul_nat_div_log (mul_pos hc hκ))
  let H₀ := max Hmin (max H₁ H₂)
  have hH₀min : Hmin ≤ H₀ := le_max_left _ _
  have hH₀one : H₁ ≤ H₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hH₀two : H₂ ≤ H₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hH₀ : 2 ≤ H₀ := hH₁.trans hH₀one
  let τ := c * κ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let P : ℕ → ℕ := fun j ↦ primeGraphModulus (entropyScale H₀ j)
  let _ : ∀ j, NeZero (P j) := fun j ↦ instNeZeroPrimeGraphModulus _
  have hP (j : ℕ) : Real.log (P j) ≤ Real.log 4 * entropyScale H₀ j := by
    rw [show P j = primorial (entropyScale H₀ j) from primeGraphModulus_eq_primorial _]
    exact log_primorial_le_log_four_mul _
  obtain ⟨J, L₀, hJ, hL₀, hselect⟩ := exists_logProb_block_entropy_control (α := α)
    hH₀ hτ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)) P hP
  refine ⟨H₀, J, L₀, hH₀min, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F
  obtain ⟨j, hj, hinfo, hdef⟩ := hselect L U hL hU hLL F
  refine ⟨j, hj, ?_⟩
  intro w h s hw hs
  set H := entropyScale H₀ j with hHdef
  have hHH₀ : H₀ ≤ H := le_entropyScale H₀ j
  have hHH₁ : H₁ ≤ H := hH₀one.trans hHH₀
  have hHH₂ : H₂ ≤ H := hH₀two.trans hHH₀
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  let E : (Fin H → α) → Finset (ZMod (primeGraphModulus H)) := fun b ↦
    Finset.univ.filter fun z ↦ ρ * H / Real.log H ≤
      ‖pairTwistedSum w (d₁ ∘ b) (d₂ ∘ b) h s z - pairTwistedMeanCRT w (d₁ ∘ b) (d₂ ∘ b) h s‖
  have hrare : ∀ b, ((E b).card : ℝ) * Real.exp (c * H / Real.log H) ≤ primeGraphModulus H := by
    intro b
    exact htail H hHH₁ w (d₁ ∘ b) (d₂ ∘ b) h s hw (fun i ↦ hd₁ (b i)) (fun i ↦ hd₂ (b i)) hs
  have hprob := logProb_block_rare_event_le hL (by omega : L ≤ U) F E
    (show 0 < c * H / Real.log H by positivity) hrare hinfo hdef
  have hsmall : (τ * H / Real.log H + 2) / (c * H / Real.log H) ≤ κ := by
    apply (div_le_iff₀ (show 0 < c * H / Real.log H by positivity)).mpr
    have hlarge := hH₂ H hHH₂
    dsimp [τ]
    simp only [mul_div_assoc] at *
    nlinarith
  have hfinal := hprob.trans hsmall
  have hset : {n : LogProbIndex L U | (n.1 : ZMod (primeGraphModulus H)) ∈
      E (finiteSequenceBlock F H n.1)} =
      {n : LogProbIndex L U | ρ * H / Real.log H ≤
        ‖pairTwistedDiscrepancy w (d₁ ∘ F) (d₂ ∘ F) H h s n.1‖} := by
    ext n
    change ((n.1 : ZMod (primeGraphModulus H)) ∈ E (finiteSequenceBlock F H n.1)) ↔ _
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hset] at hfinal
  exact hfinal

/-- Port of `Erdos67b.exists_logProb_primeGraph_decoupling`: averaged pair-twisted graph decoupling
with an arbitrarily small coefficient, uniformly over finite-alphabet sequences, all twists, all
shifts, and all eligible prime subsets. -/
theorem exists_logProb_pairTwisted_decoupling
    {α : Type*} [Finite α] [Nonempty α]
    (d₁ d₂ : α → ℂ) {B δ ε : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hε : 0 < ε)
    (hd₁ : ∀ a, ‖d₁ a‖ ≤ B) (hd₂ : ∀ a, ‖d₂ a‖ ≤ B) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (_hL : 0 < L) (_hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J, ∀ (w : ℕ → ℂ) (h : ℕ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U
          (pairTwistedDiscrepancy w (d₁ ∘ F) (d₂ ∘ F) (entropyScale H₀ j) h s)‖ ≤
            ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  let R := primeGraphRadius B δ
  have hR : 0 < R := primeGraphRadius_pos hB hδ
  let ρ := ε / 2
  let κ := ε / (16 * R)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcoef : ρ + 8 * R * κ = ε := by
    dsimp [ρ, κ]
    field_simp
    ring
  obtain ⟨Hprime, hprime⟩ := eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  obtain ⟨H₀, J, L₀, hmin, hH₀, hJ, hL₀, hselect⟩ :=
    exists_logProb_pairTwisted_small_tail d₁ d₂ hB hδ hρ hκ hd₁ hd₂ (max Hmin Hprime)
  refine ⟨H₀, J, L₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F
  obtain ⟨j, hj, htail⟩ := hselect L U hL hU hLL F
  refine ⟨j, hj, ?_⟩
  intro w h s hw hs
  set H := entropyScale H₀ j with hHdef
  have hHlower : H₀ ≤ H := le_entropyScale H₀ j
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hcount := hprime H (((le_max_right _ _).trans hmin).trans hHlower)
  have hbound (n : LogProbIndex L U) :
      ‖pairTwistedDiscrepancy w (d₁ ∘ F) (d₂ ∘ F) H h s n.1‖ ≤
        2 * (Nat.primeCounting H : ℝ) * R :=
    norm_pairTwistedDiscrepancy_le w (d₁ ∘ F) (d₂ ∘ F) H h s hB.le hδ hw
      (fun n ↦ hd₁ (F n)) (fun n ↦ hd₂ (F n)) hs n.1
  have hexp := norm_finiteExpectation_le_of_tail (logProbFiniteLaw L U hL (by omega))
    (fun n ↦ pairTwistedDiscrepancy w (d₁ ∘ F) (d₂ ∘ F) H h s n.1)
    (show 0 ≤ ρ * H / Real.log H by positivity)
    (show 0 ≤ 2 * (Nat.primeCounting H : ℝ) * R by positivity)
    hbound (htail w h s hw hs)
  change ‖logProbExpectation L U (pairTwistedDiscrepancy w (d₁ ∘ F) (d₂ ∘ F) H h s)‖ ≤
    ρ * H / Real.log H + (2 * (Nat.primeCounting H : ℝ) * R) * κ at hexp
  have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 2 * R * κ by positivity)
  apply hexp.trans
  calc
    ρ * H / Real.log H + (2 * (Nat.primeCounting H : ℝ) * R) * κ ≤
        (ρ + 8 * R * κ) * ((H : ℝ) / Real.log H) := by
      rw [mul_div_assoc]
      nlinarith
    _ = ε * H / Real.log H := by rw [hcoef, mul_div_assoc]

end

end NormalNumbers.ElliottTwistedGraph
