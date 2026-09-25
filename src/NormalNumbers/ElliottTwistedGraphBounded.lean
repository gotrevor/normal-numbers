import NormalNumbers.ElliottTwistedGraphDecoupling
import ErdosProblems.Erdos67b.PrimeGraphApproximation

/-!
# Removing the finite-alphabet restriction from the pair-twisted graph

The rung above `NormalNumbers.ElliottTwistedGraphDecoupling`: the port of
`Erdos67b.exists_logProb_bounded_primeGraph_decoupling` to the phase-twisted, two-block graph.

Two observations make the perturbation estimates come out with the dependency's **exact** constants.

* The twist is a per-prime scalar of modulus at most `1`, so it never enters a difference estimate:
  `‖w p · X − w p · Y‖ ≤ ‖X − Y‖`.
* The two-block edge difference splits the same way the conjugate one does,
  `b j c k − b' j c' k = (b j − b' j) c k + b' j (c k − c' k)`, giving the same `2Bζ`.

The finite alphabet for the *pair* is the **product** `net × net` of the dependency's own unit-disk
net `Erdos67b.exists_finite_unitDisk_approximation`, with the two decode maps being the two
projections.  A single sequence in that product alphabet approximates both `F` and `G`
simultaneously, which is precisely the hypothesis shape the previous rung was built to accept.

Contents: `norm_pairShiftEdge_sub_le`, `norm_pairTwistedCoordinate_sub_le`,
`norm_pairTwistedObservable_sub_le`, `norm_pairTwistedSum_sub_le`,
`norm_pairTwistedMeanCRT_sub_le`, `norm_pairTwistedDiscrepancy_sub_le`, and the headline
`exists_logProb_bounded_pairTwisted_decoupling`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b
open Erdos67b.FiniteEntropy

noncomputable section

/-! ## Perturbation estimates, with the dependency's constants -/

theorem norm_pairShiftEdge_sub_le {H : ℕ} (b c b' c' : Fin H → ℂ) (a : ℕ)
    {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ)
    (_hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (hb' : ∀ j, ‖b' j‖ ≤ B) (_hc' : ∀ j, ‖c' j‖ ≤ B)
    (hbclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (hcclose : ∀ j, ‖c j - c' j‖ ≤ ζ) (j : Fin H) :
    ‖pairShiftEdge b c a j - pairShiftEdge b' c' a j‖ ≤ 2 * B * ζ := by
  unfold pairShiftEdge
  split_ifs with hj
  · set k : Fin H := ⟨j.1 + a, hj⟩ with hk
    have hid : b j * c k - b' j * c' k = (b j - b' j) * c k + b' j * (c k - c' k) := by ring
    rw [hid]
    have hleft : ‖(b j - b' j) * c k‖ ≤ ζ * B := by
      rw [norm_mul]
      exact mul_le_mul (hbclose j) (hc k) (norm_nonneg _) hζ
    have hright : ‖b' j * (c k - c' k)‖ ≤ B * ζ := by
      rw [norm_mul]
      exact mul_le_mul (hb' j) (hcclose k) (norm_nonneg _) hB
    exact (norm_add_le _ _).trans (by linarith)
  · simp only [sub_self, norm_zero]
    positivity

theorem norm_pairTwistedCoordinate_sub_le {H : ℕ} (w : ℕ → ℂ) (b c b' c' : Fin H → ℂ)
    (p h : ℕ) [NeZero p] {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hw : ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (hb' : ∀ j, ‖b' j‖ ≤ B) (hc' : ∀ j, ‖c' j‖ ≤ B)
    (hbclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (hcclose : ∀ j, ‖c j - c' j‖ ≤ ζ) (z : ZMod p) :
    ‖pairTwistedCoordinate w b c p h z - pairTwistedCoordinate w b' c' p h z‖ ≤
      (H / p + 1 : ℕ) * (2 * B * ζ) := by
  classical
  let t : Finset (Fin H) := Finset.univ.filter fun j ↦ z + (j.1 + 1 : ℕ) = 0
  have ht : t = Finset.univ.filter (fun j : Fin H ↦ (j.1 : ZMod p) = -z - 1) := by
    ext j
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
    constructor <;> intro hh <;> linear_combination hh
  have hcard : t.card ≤ H / p + 1 := by rw [ht]; exact card_fin_residue_le H p (-z - 1)
  have hsum : pairTwistedCoordinate w b c p h z - pairTwistedCoordinate w b' c' p h z =
      ∑ j ∈ t, (w p * pairShiftEdge b c (p * h) j - w p * pairShiftEdge b' c' (p * h) j) := by
    simp only [pairTwistedCoordinate, t, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hedge (j : Fin H) :
      ‖w p * pairShiftEdge b c (p * h) j - w p * pairShiftEdge b' c' (p * h) j‖ ≤ 2 * B * ζ := by
    rw [← mul_sub, norm_mul]
    calc ‖w p‖ * ‖pairShiftEdge b c (p * h) j - pairShiftEdge b' c' (p * h) j‖
        ≤ 1 * ‖pairShiftEdge b c (p * h) j - pairShiftEdge b' c' (p * h) j‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ 2 * B * ζ :=
          norm_pairShiftEdge_sub_le b c b' c' _ hB hζ hb hc hb' hc' hbclose hcclose j
  rw [hsum]
  calc
    ‖∑ j ∈ t, (w p * pairShiftEdge b c (p * h) j - w p * pairShiftEdge b' c' (p * h) j)‖
        ≤ ∑ j ∈ t, ‖w p * pairShiftEdge b c (p * h) j - w p * pairShiftEdge b' c' (p * h) j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ t, 2 * B * ζ := Finset.sum_le_sum (fun j _ ↦ hedge j)
    _ = t.card * (2 * B * ζ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / p + 1 : ℕ) * (2 * B * ζ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

theorem norm_pairTwistedObservable_sub_le {H : ℕ} (w : ℕ → ℂ) (b c b' c' : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (hb' : ∀ j, ‖b' j‖ ≤ B) (hc' : ∀ j, ‖c' j‖ ≤ B)
    (hbclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (hcclose : ∀ j, ‖c j - c' j‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) (p : PrimeGraphIndex H) (z : ZMod p.1) :
    ‖pairTwistedObservable w b c h s p z - pairTwistedObservable w b' c' h s p z‖ ≤
      (1 / δ + 1) * (2 * B * ζ) := by
  unfold pairTwistedObservable
  split_ifs with hp
  · have hpr : (0 : ℝ) < p.1 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p.1))
    have hdiv : (H / p.1 : ℕ) ≤ (H : ℝ) / p.1 := by
      apply (le_div_iff₀ hpr).mpr
      exact_mod_cast Nat.div_mul_le_self H p.1
    have hratio : (H : ℝ) / p.1 ≤ 1 / δ := by
      apply (div_le_div_iff₀ hpr hδ).mpr
      nlinarith [hs p.1 hp]
    have hfloor : (H / p.1 + 1 : ℕ) ≤ 1 / δ + (1 : ℝ) := by push_cast; linarith
    exact (norm_pairTwistedCoordinate_sub_le w b c b' c' p.1 h hB hζ (hw p.1 hp)
      hb hc hb' hc' hbclose hcclose z).trans
      (mul_le_mul_of_nonneg_right hfloor (by positivity))
  · simp only [sub_self, norm_zero]
    positivity

theorem norm_pairTwistedSum_sub_le {H : ℕ} (w : ℕ → ℂ) (b c b' c' : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (hb' : ∀ j, ‖b' j‖ ≤ B) (hc' : ∀ j, ‖c' j‖ ≤ B)
    (hbclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (hcclose : ∀ j, ‖c j - c' j‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) (z : ZMod (primeGraphModulus H)) :
    ‖pairTwistedSum w b c h s z - pairTwistedSum w b' c' h s z‖ ≤
      (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * (2 * B * ζ)) := by
  unfold pairTwistedSum crtComplexSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p, (pairTwistedObservable w b c h s p _ - pairTwistedObservable w b' c' h s p _)‖
        ≤ ∑ p, ‖pairTwistedObservable w b c h s p _ -
            pairTwistedObservable w b' c' h s p _‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, (1 / δ + 1) * (2 * B * ζ) := Finset.sum_le_sum
      (fun p _ ↦ norm_pairTwistedObservable_sub_le w b c b' c' h s hB hζ hδ hw
        hb hc hb' hc' hbclose hcclose hs p _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]

theorem norm_pairTwistedMeanCRT_sub_le {H : ℕ} (w : ℕ → ℂ) (b c b' c' : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (hb' : ∀ j, ‖b' j‖ ≤ B) (hc' : ∀ j, ‖c' j‖ ≤ B)
    (hbclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (hcclose : ∀ j, ‖c j - c' j‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) :
    ‖pairTwistedMeanCRT w b c h s - pairTwistedMeanCRT w b' c' h s‖ ≤
      (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * (2 * B * ζ)) := by
  rw [← crtComplexMean_pairTwistedObservable, ← crtComplexMean_pairTwistedObservable]
  unfold crtComplexMean
  rw [← Finset.sum_sub_distrib]
  have hcoord (p : PrimeGraphIndex H) :
      ‖(p.1 : ℝ)⁻¹ • (∑ x, pairTwistedObservable w b c h s p x) -
        (p.1 : ℝ)⁻¹ • (∑ x, pairTwistedObservable w b' c' h s p x)‖ ≤
          (1 / δ + 1) * (2 * B * ζ) := by
    rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hsum : ‖∑ x, (pairTwistedObservable w b c h s p x -
        pairTwistedObservable w b' c' h s p x)‖ ≤
        (p.1 : ℝ) * ((1 / δ + 1) * (2 * B * ζ)) := by
      apply (norm_sum_le _ _).trans
      have hh := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦
        norm_pairTwistedObservable_sub_le w b c b' c' h s hB hζ hδ hw
          hb hc hb' hc' hbclose hcclose hs p x)
      simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] using hh
    have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.1)
    have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using hh
  apply (norm_sum_le _ _).trans
  have hh := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hcoord p)
  simpa only [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul] using hh

theorem norm_pairTwistedDiscrepancy_sub_le (w : ℕ → ℂ) (F G F' G' : ℕ → ℂ) (H h : ℕ)
    (s : Finset ℕ) {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hF : ∀ n, ‖F n‖ ≤ B) (hG : ∀ n, ‖G n‖ ≤ B)
    (hF' : ∀ n, ‖F' n‖ ≤ B) (hG' : ∀ n, ‖G' n‖ ≤ B)
    (hFclose : ∀ n, ‖F n - F' n‖ ≤ ζ) (hGclose : ∀ n, ‖G n - G' n‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) (n : ℕ) :
    ‖pairTwistedDiscrepancy w F G H h s n - pairTwistedDiscrepancy w F' G' H h s n‖ ≤
      4 * (Nat.primeCounting H : ℝ) * B * ζ * (1 / δ + 1) := by
  have hsum := norm_pairTwistedSum_sub_le w (finiteSequenceBlock F H n)
    (finiteSequenceBlock G H n) (finiteSequenceBlock F' H n) (finiteSequenceBlock G' H n)
    h s hB hζ hδ hw (fun j ↦ hF _) (fun j ↦ hG _) (fun j ↦ hF' _) (fun j ↦ hG' _)
    (fun j ↦ hFclose _) (fun j ↦ hGclose _) hs (n : ZMod (primeGraphModulus H))
  have hmean := norm_pairTwistedMeanCRT_sub_le w (finiteSequenceBlock F H n)
    (finiteSequenceBlock G H n) (finiteSequenceBlock F' H n) (finiteSequenceBlock G' H n)
    h s hB hζ hδ hw (fun j ↦ hF _) (fun j ↦ hG _) (fun j ↦ hF' _) (fun j ↦ hG' _)
    (fun j ↦ hFclose _) (fun j ↦ hGclose _) hs
  have heq : pairTwistedDiscrepancy w F G H h s n - pairTwistedDiscrepancy w F' G' H h s n =
      (pairTwistedSum w (finiteSequenceBlock F H n) (finiteSequenceBlock G H n) h s n -
        pairTwistedSum w (finiteSequenceBlock F' H n) (finiteSequenceBlock G' H n) h s n) -
        (pairTwistedMeanCRT w (finiteSequenceBlock F H n) (finiteSequenceBlock G H n) h s -
          pairTwistedMeanCRT w (finiteSequenceBlock F' H n) (finiteSequenceBlock G' H n) h s) := by
    unfold pairTwistedDiscrepancy
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by nlinarith)

/-! ## Decoupling for arbitrary unit-disk sequences -/

/-- **Port of `Erdos67b.exists_logProb_bounded_primeGraph_decoupling`.**  Pair-twisted graph
decoupling for every pair of sequences in the complex unit disk, with no finite-alphabet and no
multiplicativity restriction, and uniformly over all unimodular-or-smaller twists. -/
theorem exists_logProb_bounded_pairTwisted_decoupling
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (_hL : 0 < L) (_hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F G : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∃ j < J, ∀ (w : ℕ → ℂ) (h : ℕ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U
          (pairTwistedDiscrepancy w F G (entropyScale H₀ j) h s)‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
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
  obtain ⟨a₀, ha₀⟩ := hnet
  let α := (↥net) × (↥net)
  let _ : Nonempty α := ⟨(⟨a₀, ha₀⟩, ⟨a₀, ha₀⟩)⟩
  let d₁ : α → ℂ := fun a ↦ a.1.1
  let d₂ : α → ℂ := fun a ↦ a.2.1
  have hd₁ : ∀ a : α, ‖d₁ a‖ ≤ 1 := fun a ↦ hnetBound a.1.1 a.1.2
  have hd₂ : ∀ a : α, ‖d₂ a‖ ≤ 1 := fun a ↦ hnetBound a.2.1 a.2.2
  obtain ⟨Hprime, hprime⟩ := eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  obtain ⟨H₀, J, L₀, hmin, hH₀, hJ, hL₀, hselect⟩ :=
    exists_logProb_pairTwisted_decoupling d₁ d₂ (by norm_num : (0 : ℝ) < 1) hδ
      (show 0 < ε / 2 by positivity) hd₁ hd₂ (max Hmin Hprime)
  refine ⟨H₀, J, L₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F G hF hG
  have happ (n : ℕ) : ∃ a : α, ‖F n - d₁ a‖ ≤ ζ ∧ ‖G n - d₂ a‖ ≤ ζ := by
    obtain ⟨x, hx, hxclose⟩ := hnetApprox (F n) (hF n)
    obtain ⟨y, hy, hyclose⟩ := hnetApprox (G n) (hG n)
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxclose, hyclose⟩
  choose A hAF hAG using happ
  obtain ⟨j, hj, hdec⟩ := hselect L U hL hU hLL A
  refine ⟨j, hj, ?_⟩
  intro w h s hw hs
  set H := entropyScale H₀ j with hHdef
  have hHlower : H₀ ≤ H := le_entropyScale H₀ j
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hcount := hprime H (((le_max_right _ _).trans hmin).trans hHlower)
  have hFa : ∀ n, ‖(d₁ ∘ A) n‖ ≤ 1 := fun n ↦ hd₁ (A n)
  have hGa : ∀ n, ‖(d₂ ∘ A) n‖ ≤ 1 := fun n ↦ hd₂ (A n)
  have hdiff := norm_logProbExpectation_le hL (by omega : L ≤ U)
    (fun n ↦ pairTwistedDiscrepancy w F G H h s n -
      pairTwistedDiscrepancy w (d₁ ∘ A) (d₂ ∘ A) H h s n)
    (4 * (Nat.primeCounting H : ℝ) * ζ * D) (by
      intro n _
      have hh := norm_pairTwistedDiscrepancy_sub_le w F G (d₁ ∘ A) (d₂ ∘ A) H h s
        zero_le_one hζ.le hδ hw hF hG hFa hGa hAF hAG hs n
      simpa only [mul_one, D] using hh)
  have heq : logProbExpectation L U
      (fun n ↦ pairTwistedDiscrepancy w F G H h s n -
        pairTwistedDiscrepancy w (d₁ ∘ A) (d₂ ∘ A) H h s n) =
      logProbExpectation L U (pairTwistedDiscrepancy w F G H h s) -
        logProbExpectation L U (pairTwistedDiscrepancy w (d₁ ∘ A) (d₂ ∘ A) H h s) := by
    simp only [logProbExpectation, smul_sub, Finset.sum_sub_distrib]
  rw [heq] at hdiff
  have hdiffBudget : 4 * (Nat.primeCounting H : ℝ) * ζ * D ≤ (ε / 2) * ((H : ℝ) / Real.log H) := by
    have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 4 * ζ * D by positivity)
    calc
      4 * (Nat.primeCounting H : ℝ) * ζ * D ≤ (16 * ζ * D) * ((H : ℝ) / Real.log H) := by nlinarith
      _ = _ := by rw [hbudget]
  have hdec' := hdec w h s hw hs
  have hnorm := norm_add_le
    (logProbExpectation L U (pairTwistedDiscrepancy w F G H h s) -
      logProbExpectation L U (pairTwistedDiscrepancy w (d₁ ∘ A) (d₂ ∘ A) H h s))
    (logProbExpectation L U (pairTwistedDiscrepancy w (d₁ ∘ A) (d₂ ∘ A) H h s))
  rw [sub_add_cancel] at hnorm
  have hfinal := hnorm.trans (add_le_add (hdiff.trans hdiffBudget) hdec')
  simp only [mul_div_assoc] at *
  linarith

end

end NormalNumbers.ElliottTwistedGraph
