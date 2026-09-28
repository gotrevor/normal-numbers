import NormalNumbers.ElliottDilatedGrouped
import ErdosProblems.Erdos67b.PrimeGraphApproximation

/-!
# Removing the finite-alphabet restriction from the *dilated* graph

Step (iii)(b) of the dilated crux assembly.  `NormalNumbers.ElliottGenericGraph`'s decoupling
`exists_logProb_gen_decoupling` reads its data as a sequence over a **finite** alphabet.  The crux
needs it for an arbitrary pair of unimodular multiplicative functions.  This file performs that
widening, in the shape the dilated route consumes: the conclusion is stated on
`genDiscrepancyAt` of `dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H)`, i.e. on
the very object `NormalNumbers.ElliottDilatedMean.norm_logProb_dilatedMean_sub_correlation_le`
takes as its hypothesis.

Two ingredients, both already proved:

* the generic edge perturbation estimates of this file — the
  `NormalNumbers.ElliottTwistedGraph.norm_pairTwisted*_sub_le` chain with `pairShiftEdge` replaced
  by an arbitrary edge family and the edge-difference bound `η` as a parameter.  Nothing about the
  edge is used, so the constants are the dependency's;
* lap 39's `NormalNumbers.ElliottDilatedGrouped.ungroupBlock_finiteSequenceBlock_groupSeq`, which
  exhibits `affineBlock f a n (a*m)` as an *ordinary* block of the `a`-grouped sequence
  `groupSeq a f`, whose alphabet `Fin a → ↥net` is still finite.

So the finite alphabet is `α = (Fin a → ↥net) × (Fin a → ↥net)` over the dependency's own unit-disk
net, the approximating sequence is chosen componentwise over `Fin a`, and the perturbation budget is
the pure-shift one `ζ = ε/(32 D)`, `D = 1/δ + 1`, because
`NormalNumbers.ElliottDilatedGrouped.norm_dilatedEdgeReindexed_sub_le` has the dependency's
constant `2Bζ`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottGenericGraph

open Erdos67b
open Erdos67b.FiniteEntropy
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottDilatedBridge
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottDilatedGrouped

noncomputable section

/-! ## Generic edge perturbation, with the dependency's constants -/

theorem norm_genCoordinate_sub_le {H : ℕ} (w : ℕ → ℂ) (E E' : ℕ → Fin H → ℂ) (p : ℕ) [NeZero p]
    {η : ℝ} (hη : 0 ≤ η) (hw : ‖w p‖ ≤ 1) (hclose : ∀ j, ‖E p j - E' p j‖ ≤ η) (z : ZMod p) :
    ‖genCoordinate w E p z - genCoordinate w E' p z‖ ≤ (H / p + 1 : ℕ) * η := by
  classical
  let t : Finset (Fin H) := Finset.univ.filter fun j ↦ z + (j.1 + 1 : ℕ) = 0
  have ht : t = Finset.univ.filter (fun j : Fin H ↦ (j.1 : ZMod p) = -z - 1) := by
    ext j
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
    constructor <;> intro hh <;> linear_combination hh
  have hcard : t.card ≤ H / p + 1 := by rw [ht]; exact card_fin_residue_le H p (-z - 1)
  have hsum : genCoordinate w E p z - genCoordinate w E' p z =
      ∑ j ∈ t, (w p * E p j - w p * E' p j) := by
    simp only [genCoordinate, t, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hedge (j : Fin H) : ‖w p * E p j - w p * E' p j‖ ≤ η := by
    rw [← mul_sub, norm_mul]
    calc ‖w p‖ * ‖E p j - E' p j‖ ≤ 1 * ‖E p j - E' p j‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ η := hclose j
  rw [hsum]
  calc
    ‖∑ j ∈ t, (w p * E p j - w p * E' p j)‖ ≤ ∑ j ∈ t, ‖w p * E p j - w p * E' p j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ t, η := Finset.sum_le_sum (fun j _ ↦ hedge j)
    _ = t.card * η := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / p + 1 : ℕ) * η :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη

theorem norm_genObservable_sub_le {H : ℕ} (w : ℕ → ℂ) (E E' : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hclose : ∀ p, ∀ j, ‖E p j - E' p j‖ ≤ η) (hs : ∀ p ∈ s, δ * H ≤ p)
    (p : PrimeGraphIndex H) (z : ZMod p.1) :
    ‖genObservable w E s p z - genObservable w E' s p z‖ ≤ (1 / δ + 1) * η := by
  unfold genObservable
  split_ifs with hp
  · have hpr : (0 : ℝ) < p.1 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p.1))
    have hdiv : (H / p.1 : ℕ) ≤ (H : ℝ) / p.1 := by
      apply (le_div_iff₀ hpr).mpr
      exact_mod_cast Nat.div_mul_le_self H p.1
    have hratio : (H : ℝ) / p.1 ≤ 1 / δ := by
      apply (div_le_div_iff₀ hpr hδ).mpr
      nlinarith [hs p.1 hp]
    have hfloor : (H / p.1 + 1 : ℕ) ≤ 1 / δ + (1 : ℝ) := by push_cast; linarith
    exact (norm_genCoordinate_sub_le w E E' p.1 hη (hw p.1 hp) (hclose p.1) z).trans
      (mul_le_mul_of_nonneg_right hfloor hη)
  · simp only [sub_self, norm_zero]
    positivity

theorem norm_genSum_sub_le {H : ℕ} (w : ℕ → ℂ) (E E' : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hclose : ∀ p, ∀ j, ‖E p j - E' p j‖ ≤ η) (hs : ∀ p ∈ s, δ * H ≤ p)
    (z : ZMod (primeGraphModulus H)) :
    ‖genSum w E s z - genSum w E' s z‖ ≤ (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * η) := by
  unfold genSum crtComplexSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p, (genObservable w E s p _ - genObservable w E' s p _)‖
        ≤ ∑ p, ‖genObservable w E s p _ - genObservable w E' s p _‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, (1 / δ + 1) * η := Finset.sum_le_sum
      (fun p _ ↦ norm_genObservable_sub_le w E E' s hη hδ hw hclose hs p _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]

theorem norm_genMeanCRT_sub_le {H : ℕ} (w : ℕ → ℂ) (E E' : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hclose : ∀ p, ∀ j, ‖E p j - E' p j‖ ≤ η) (hs : ∀ p ∈ s, δ * H ≤ p) :
    ‖genMeanCRT w E s - genMeanCRT w E' s‖ ≤ (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * η) := by
  rw [← crtComplexMean_genObservable, ← crtComplexMean_genObservable]
  unfold crtComplexMean
  rw [← Finset.sum_sub_distrib]
  have hcoord (p : PrimeGraphIndex H) :
      ‖(p.1 : ℝ)⁻¹ • (∑ x, genObservable w E s p x) -
        (p.1 : ℝ)⁻¹ • (∑ x, genObservable w E' s p x)‖ ≤ (1 / δ + 1) * η := by
    rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hsum : ‖∑ x, (genObservable w E s p x - genObservable w E' s p x)‖ ≤
        (p.1 : ℝ) * ((1 / δ + 1) * η) := by
      apply (norm_sum_le _ _).trans
      have hh := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦
        norm_genObservable_sub_le w E E' s hη hδ hw hclose hs p x)
      simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] using hh
    have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.1)
    have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using hh
  apply (norm_sum_le _ _).trans
  have hh := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hcoord p)
  simpa only [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul] using hh

theorem norm_genDiscrepancyAt_sub_le {H : ℕ} (w : ℕ → ℂ) (E E' : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hclose : ∀ p, ∀ j, ‖E p j - E' p j‖ ≤ η) (hs : ∀ p ∈ s, δ * H ≤ p)
    (z : ZMod (primeGraphModulus H)) :
    ‖genDiscrepancyAt w E s z - genDiscrepancyAt w E' s z‖ ≤
      2 * (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * η) := by
  have hsum := norm_genSum_sub_le w E E' s hη hδ hw hclose hs z
  have hmean := norm_genMeanCRT_sub_le w E E' s hη hδ hw hclose hs
  have heq : genDiscrepancyAt w E s z - genDiscrepancyAt w E' s z =
      (genSum w E s z - genSum w E' s z) - (genMeanCRT w E s - genMeanCRT w E' s) := by
    unfold genDiscrepancyAt; abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

/-! ## Removing the finite alphabet from the dilated graph -/

theorem norm_ungroupBlock_le {a m : ℕ} {b : Fin m → (Fin a → ℂ)} {B : ℝ}
    (hb : ∀ i j, ‖b i j‖ ≤ B) (j : Fin (a * m)) : ‖ungroupBlock b j‖ ≤ B := by
  simp only [ungroupBlock]; exact hb _ _

/-- **Step (iii)(b) of the dilated crux: the dilated graph decouples for arbitrary unit-disk
sequences.**  Port of `NormalNumbers.ElliottTwistedGraph.exists_logProb_bounded_pairTwisted_decoupling`
to the `a`-dilated edge family, with no finite-alphabet restriction on `f₁, f₂` and uniformly over
all unimodular-or-smaller twists, all eligible prime sets and an arbitrary CRT residue shift.

The conclusion is exactly the hypothesis `hdec` of
`NormalNumbers.ElliottDilatedMean.norm_logProb_dilatedMean_sub_correlation_le`. -/
theorem exists_logProb_bounded_dilated_decoupling
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {a : ℕ} (ha : 0 < a) (c₁ h : ℕ)
    (Δ : (m : ℕ) → ZMod (primeGraphModulus (a * m))) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ a ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (_hL : 0 < L) (_hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ f₁ f₂ : ℕ → ℂ, (∀ n : ℕ, 0 < n → ‖f₁ n‖ ≤ 1) → (∀ n : ℕ, 0 < n → ‖f₂ n‖ ≤ 1) →
      ∃ j < J, ∀ (w : ℕ → ℂ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ p ∈ s, δ * (a * entropyScale H₀ j : ℕ) ≤ p) →
        ‖logProbExpectation L U (fun n ↦ genDiscrepancyAt w
            (dilatedEdgeReindexed (affineBlock f₁ a n (a * entropyScale H₀ j))
              (affineBlock f₂ a n (a * entropyScale H₀ j)) a c₁ h) s
            ((n : ZMod (primeGraphModulus (a * entropyScale H₀ j))) -
              Δ (entropyScale H₀ j)))‖ ≤
          ε * (a * entropyScale H₀ j : ℕ) / Real.log ((a * entropyScale H₀ j : ℕ) : ℝ) := by
  classical
  let D := 1 / δ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let ζ := ε / (32 * D)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hbudget : 16 * ζ * D = ε / 2 := by
    dsimp [ζ]
    field_simp
    ring
  obtain ⟨net, hnet, hnetBound, hnetApprox⟩ := exists_finite_unitDisk_approximation hζ
  obtain ⟨z₀, hz₀⟩ := hnet
  let α := (Fin a → ↥net) × (Fin a → ↥net)
  let _ : Nonempty α := ⟨(fun _ ↦ ⟨z₀, hz₀⟩, fun _ ↦ ⟨z₀, hz₀⟩)⟩
  let d₁ : α → Fin a → ℂ := fun x i ↦ (x.1 i : ℂ)
  let d₂ : α → Fin a → ℂ := fun x i ↦ (x.2 i : ℂ)
  have hd₁ : ∀ (x : α) (i : Fin a), ‖d₁ x i‖ ≤ 1 := fun x i ↦ hnetBound _ (x.1 i).2
  have hd₂ : ∀ (x : α) (i : Fin a), ‖d₂ x i‖ ≤ 1 := fun x i ↦ hnetBound _ (x.2 i).2
  let mkE : (m : ℕ) → (Fin m → α) → ℕ → Fin (a * m) → ℂ := fun m b ↦
    dilatedEdgeReindexed (ungroupBlock (fun i ↦ d₁ (b i))) (ungroupBlock (fun i ↦ d₂ (b i)))
      a c₁ h
  have hE : ∀ (m : ℕ) (b : Fin m → α) (p : ℕ) (j : Fin (a * m)), ‖mkE m b p j‖ ≤ (1 : ℝ) ^ 2 :=
    fun m b p j ↦ norm_dilatedEdgeReindexed_le zero_le_one
      (fun jj ↦ norm_ungroupBlock_le (fun i k ↦ hd₁ (b i) k) jj)
      (fun jj ↦ norm_ungroupBlock_le (fun i k ↦ hd₂ (b i) k) jj) a c₁ h p j
  obtain ⟨Hprime, hprime⟩ := eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  obtain ⟨H₀, J, L₀, hmin, hH₀, hH₀a, hJ, hL₀, hselect⟩ :=
    exists_logProb_gen_decoupling ha mkE Δ (by norm_num : (0:ℝ) < 1) hδ
      (show 0 < ε / 2 by positivity) hE (max Hmin Hprime)
  refine ⟨H₀, J, L₀, (le_max_left _ _).trans hmin, hH₀, hH₀a, hJ, hL₀, ?_⟩
  intro L U hL hU hLL f₁ f₂ h₁ h₂
  have happ : ∀ k : ℕ, ∃ x : α, (∀ i, ‖groupSeq a f₁ k i - d₁ x i‖ ≤ ζ) ∧
      (∀ i, ‖groupSeq a f₂ k i - d₂ x i‖ ≤ ζ) := by
    intro k
    have e₁ := fun i : Fin a ↦ hnetApprox (groupSeq a f₁ k i) (norm_groupSeq_le h₁ a k i)
    have e₂ := fun i : Fin a ↦ hnetApprox (groupSeq a f₂ k i) (norm_groupSeq_le h₂ a k i)
    choose g₁ hg₁mem hg₁ using e₁
    choose g₂ hg₂mem hg₂ using e₂
    exact ⟨(fun i ↦ ⟨g₁ i, hg₁mem i⟩, fun i ↦ ⟨g₂ i, hg₂mem i⟩), hg₁, hg₂⟩
  choose A hA₁ hA₂ using happ
  obtain ⟨j, hj, hdec⟩ := hselect L U hL hU hLL A
  refine ⟨j, hj, ?_⟩
  intro w s hw hs
  set m := entropyScale H₀ j with hmdef
  have hmH₀ : H₀ ≤ m := le_entropyScale H₀ j
  set H := a * m with hHdef
  have hmH : m ≤ H := Nat.le_mul_of_pos_left m ha
  have hHlower : H₀ ≤ H := hmH₀.trans hmH
  have hH2 : 2 ≤ H := hH₀.trans hHlower
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hcount := hprime H (((le_max_right _ _).trans hmin).trans hHlower)
  -- the real blocks are the ungrouped blocks of the grouped sequences
  have hreal (n : ℕ) : dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h =
      dilatedEdgeReindexed (ungroupBlock (finiteSequenceBlock (groupSeq a f₁) m n))
        (ungroupBlock (finiteSequenceBlock (groupSeq a f₂) m n)) a c₁ h := by
    rw [ungroupBlock_finiteSequenceBlock_groupSeq, ungroupBlock_finiteSequenceBlock_groupSeq]
  -- pointwise edge closeness, with the dependency's constant
  have hedge (n : ℕ) (p : ℕ) (jj : Fin H) :
      ‖dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h p jj -
        mkE m (finiteSequenceBlock A m n) p jj‖ ≤ 2 * 1 * ζ := by
    rw [hreal n]
    exact norm_dilatedEdgeReindexed_sub_le _ _ _ _ zero_le_one hζ.le
      (fun k ↦ norm_ungroupBlock_le
        (fun i kk ↦ norm_groupSeq_le h₂ a (n + i.1 + 1) kk) k)
      (fun k ↦ norm_ungroupBlock_le
        (fun i kk ↦ hd₁ (A (n + i.1 + 1)) kk) k)
      (fun k ↦ norm_ungroupBlock_sub_le _ _ (fun i kk ↦ hA₁ (n + i.1 + 1) kk) k)
      (fun k ↦ norm_ungroupBlock_sub_le _ _ (fun i kk ↦ hA₂ (n + i.1 + 1) kk) k)
      a c₁ h p jj
  have hdiff := norm_logProbExpectation_le hL (by omega : L ≤ U)
    (fun n ↦ genDiscrepancyAt w
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - Δ m) -
      genDiscrepancyAt w (mkE m (finiteSequenceBlock A m n)) s
        ((n : ZMod (primeGraphModulus H)) - Δ m))
    (2 * (Nat.primeCounting H : ℝ) * (D * (2 * 1 * ζ))) (by
      intro n _
      exact norm_genDiscrepancyAt_sub_le w _ _ s (by positivity) hδ hw
        (fun p jj ↦ hedge n p jj) hs _)
  have heq : logProbExpectation L U
      (fun n ↦ genDiscrepancyAt w
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
          ((n : ZMod (primeGraphModulus H)) - Δ m) -
        genDiscrepancyAt w (mkE m (finiteSequenceBlock A m n)) s
          ((n : ZMod (primeGraphModulus H)) - Δ m)) =
      logProbExpectation L U (fun n ↦ genDiscrepancyAt w
          (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
          ((n : ZMod (primeGraphModulus H)) - Δ m)) -
        logProbExpectation L U (fun n ↦ genDiscrepancyAt w
          (mkE m (finiteSequenceBlock A m n)) s
          ((n : ZMod (primeGraphModulus H)) - Δ m)) := by
    simp only [logProbExpectation, smul_sub, Finset.sum_sub_distrib]
  rw [heq] at hdiff
  have hdiffBudget : 2 * (Nat.primeCounting H : ℝ) * (D * (2 * 1 * ζ)) ≤
      (ε / 2) * ((H : ℝ) / Real.log H) := by
    have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 4 * ζ * D by positivity)
    calc 2 * (Nat.primeCounting H : ℝ) * (D * (2 * 1 * ζ))
        ≤ (16 * ζ * D) * ((H : ℝ) / Real.log H) := by nlinarith
      _ = _ := by rw [hbudget]
  have hdec' := hdec w s hw hs
  have hnorm := norm_add_le
    (logProbExpectation L U (fun n ↦ genDiscrepancyAt w
        (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
        ((n : ZMod (primeGraphModulus H)) - Δ m)) -
      logProbExpectation L U (fun n ↦ genDiscrepancyAt w
        (mkE m (finiteSequenceBlock A m n)) s ((n : ZMod (primeGraphModulus H)) - Δ m)))
    (logProbExpectation L U (fun n ↦ genDiscrepancyAt w
        (mkE m (finiteSequenceBlock A m n)) s ((n : ZMod (primeGraphModulus H)) - Δ m)))
  rw [sub_add_cancel] at hnorm
  have hfinal := hnorm.trans (add_le_add (hdiff.trans hdiffBudget) hdec')
  simp only [mul_div_assoc] at *
  linarith


end

end NormalNumbers.ElliottGenericGraph

#print axioms NormalNumbers.ElliottGenericGraph.exists_logProb_bounded_dilated_decoupling
