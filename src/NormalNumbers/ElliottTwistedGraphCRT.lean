import NormalNumbers.ElliottTwistedGraph
import ErdosProblems.Erdos67b.PrimeGraphConcentration

/-!
# The pair-twisted prime graph on the CRT side

`NormalNumbers.ElliottTwistedGraph` builds the **upper-bound** (Fourier) half of the two-function,
phase-twisted prime graph.  This file builds the **lower-bound** half's foundation: the
Chinese-remainder coordinate layer that the entropy/decoupling argument runs on.

The point that makes the whole port cheap is structural and worth stating once:

> The dependency's concentration engine `Erdos67b.crt_complex_tail_card_mul_exp_le` is stated for an
> **arbitrary** family of coordinate observables `f i : ZMod (a i) → ℂ` subject only to a per-index
> norm radius.  Both of our generalisations — a second block `c` in place of `conj b`, and a
> per-prime unimodular weight `w p` — change the observable but not its radius.  Hence the graph's
> Hoeffding tail bound survives **with the dependency's own constants**, exactly as the additive
> energy bound did on the Fourier side.

Contents (all proved, no `sorry`):

* `pairTwistedCoordinate` / `pairTwistedObservable` / `pairTwistedSum` / `pairTwistedMeanCRT` —
  the twisted two-block analogues of `Erdos67b.primeGraphCoordinate`, `primeGraphObservable`,
  `primeGraphSum`, `primeGraphMean`.  Each reduces to the dependency's notion at `w = 1`,
  `c = conj ∘ b` (`pairTwistedCoordinate_conj_one`, `pairTwistedSum_conj_one`,
  `pairTwistedMeanCRT_conj_one`) — the faithfulness anchors.
* `pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean` — the bridge to the Fourier-side mean of
  `ElliottTwistedGraph`, so the two halves of the argument speak about the same quantity.
* `norm_pairTwistedCoordinate_le_of_scale`, `norm_pairTwistedSum_le`, `norm_pairTwistedMeanCRT_le` —
  the dependency's `primeGraphRadius B δ` verbatim.
* `pairTwisted_tail_card_mul_exp_le`, `exists_pairTwisted_exponential_tail` — ports of
  `Erdos67b.primeGraph_tail_card_mul_exp_le` and `Erdos67b.exists_primeGraph_exponential_tail`,
  with the same constant `c = ρ² / (64 R²)` and the same threshold scale.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottTwistedGraph

open Erdos67b

noncomputable section

/-! ## The twisted two-block coordinate -/

/-- The contribution of one prime to the pair-twisted graph, as a function of the residue only.
Compare `Erdos67b.primeGraphCoordinate`. -/
def pairTwistedCoordinate {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (p h : ℕ) (z : ZMod p) : ℂ :=
  ∑ j : Fin H, if z + (j.1 + 1 : ℕ) = 0 then w p * pairShiftEdge b c (p * h) j else 0

/-- Faithfulness anchor: the dependency's coordinate is the untwisted conjugate case. -/
theorem pairTwistedCoordinate_conj_one {H : ℕ} (b : Fin H → ℂ) (p h : ℕ) (z : ZMod p) :
    pairTwistedCoordinate (fun _ ↦ 1) b (fun i ↦ conj (b i)) p h z =
      primeGraphCoordinate b p h z := by
  simp only [pairTwistedCoordinate, primeGraphCoordinate, pairShiftEdge_conj, one_mul]

/-- The twist is a scalar per prime, so it factors straight out of the coordinate. -/
theorem pairTwistedCoordinate_eq_smul {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (p h : ℕ) (z : ZMod p) :
    pairTwistedCoordinate w b c p h z =
      w p * pairTwistedCoordinate (fun _ ↦ 1) b c p h z := by
  simp only [pairTwistedCoordinate, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

theorem norm_pairTwistedCoordinate_le {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (p h : ℕ) [NeZero p]
    {B : ℝ} (hB : 0 ≤ B) (hw : ‖w p‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (z : ZMod p) :
    ‖pairTwistedCoordinate w b c p h z‖ ≤ (H / p + 1 : ℕ) * B ^ 2 := by
  classical
  let s : Finset (Fin H) := Finset.univ.filter fun j ↦ z + (j.1 + 1 : ℕ) = 0
  have hs : s = Finset.univ.filter (fun j : Fin H ↦ (j.1 : ZMod p) = -z - 1) := by
    ext j
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination h
  have hcard : s.card ≤ H / p + 1 := by rw [hs]; exact card_fin_residue_le H p (-z - 1)
  have hsum : pairTwistedCoordinate w b c p h z =
      ∑ j ∈ s, w p * pairShiftEdge b c (p * h) j := by
    simp only [pairTwistedCoordinate, s, Finset.sum_filter]
  have hedge (j : Fin H) : ‖w p * pairShiftEdge b c (p * h) j‖ ≤ B ^ 2 := by
    rw [norm_mul]
    calc ‖w p‖ * ‖pairShiftEdge b c (p * h) j‖ ≤ 1 * ‖pairShiftEdge b c (p * h) j‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ B ^ 2 := norm_pairShiftEdge_le hB hb hc _ j
  rw [hsum]
  calc
    ‖∑ j ∈ s, w p * pairShiftEdge b c (p * h) j‖
        ≤ ∑ j ∈ s, ‖w p * pairShiftEdge b c (p * h) j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, B ^ 2 := Finset.sum_le_sum (fun j _ ↦ hedge j)
    _ = s.card * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / p + 1 : ℕ) * B ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg B)

/-- On primes of size at least `δH` the coordinate bound is block-length free: the dependency's
`Erdos67b.norm_primeGraphCoordinate_le_of_scale` with the same radius. -/
theorem norm_pairTwistedCoordinate_le_of_scale {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (p h : ℕ) [NeZero p] {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hp : δ * H ≤ p) (z : ZMod p) :
    ‖pairTwistedCoordinate w b c p h z‖ ≤ primeGraphRadius B δ := by
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hdiv : (H / p : ℕ) ≤ (H : ℝ) / p := by
    apply (le_div_iff₀ hpr).mpr
    exact_mod_cast Nat.div_mul_le_self H p
  have hratio : (H : ℝ) / p ≤ 1 / δ := by
    apply (div_le_div_iff₀ hpr hδ).mpr
    nlinarith
  have hfloor : (H / p + 1 : ℕ) ≤ 1 / δ + (1 : ℝ) := by push_cast; linarith
  exact (norm_pairTwistedCoordinate_le w b c p h hB hw hb hc z).trans
    (mul_le_mul_of_nonneg_right hfloor (sq_nonneg B))

/-- Each edge is counted for exactly one residue, so the uniform coordinate mean replaces the
divisibility indicator by `1/p`.  Compare `Erdos67b.sum_primeGraphCoordinate`. -/
theorem sum_pairTwistedCoordinate {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (p h : ℕ) [NeZero p] :
    (∑ z : ZMod p, pairTwistedCoordinate w b c p h z) =
      w p * ∑ j : Fin H, pairShiftEdge b c (p * h) j := by
  classical
  simp only [pairTwistedCoordinate, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcond (z : ZMod p) : z + (j.1 + 1 : ℕ) = 0 ↔ z = -((j.1 + 1 : ℕ) : ZMod p) :=
    eq_neg_iff_add_eq_zero.symm
  simp_rw [hcond]
  simp

/-! ## Observable, CRT sum, and mean -/

/-- Compare `Erdos67b.primeGraphObservable`. -/
def pairTwistedObservable {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (p : PrimeGraphIndex H) (z : ZMod p.1) : ℂ :=
  if p.1 ∈ s then pairTwistedCoordinate w b c p.1 h z else 0

theorem pairTwistedObservable_conj_one {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (p : PrimeGraphIndex H) (z : ZMod p.1) :
    pairTwistedObservable (fun _ ↦ 1) b (fun i ↦ conj (b i)) h s p z =
      primeGraphObservable b h s p z := by
  simp only [pairTwistedObservable, primeGraphObservable, pairTwistedCoordinate_conj_one]

theorem norm_pairTwistedObservable_le {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hs : ∀ p ∈ s, δ * H ≤ p)
    (p : PrimeGraphIndex H) (z : ZMod p.1) :
    ‖pairTwistedObservable w b c h s p z‖ ≤ primeGraphRadius B δ := by
  unfold pairTwistedObservable
  split_ifs with hp
  · exact norm_pairTwistedCoordinate_le_of_scale w b c p.1 h hB hδ (hw p.1 hp) hb hc
      (hs p.1 hp) z
  · simpa only [norm_zero] using primeGraphRadius_nonneg hδ

/-- Compare `Erdos67b.primeGraphSum`. -/
def pairTwistedSum {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (z : ZMod (primeGraphModulus H)) : ℂ :=
  crtComplexSum (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H)
    Finset.univ (pairTwistedObservable w b c h s) z

theorem pairTwistedSum_conj_one {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (z : ZMod (primeGraphModulus H)) :
    pairTwistedSum (fun _ ↦ 1) b (fun i ↦ conj (b i)) h s z = primeGraphSum b h s z := by
  simp only [pairTwistedSum, primeGraphSum, crtComplexSum, pairTwistedObservable_conj_one]

/-- The CRT-indexed pair-twisted mean.  Compare `Erdos67b.primeGraphMean`. -/
def pairTwistedMeanCRT {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) : ℂ :=
  ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
    (p.1 : ℝ)⁻¹ • (w p.1 * ∑ j : Fin H, pairShiftEdge b c (p.1 * h) j) else 0

theorem pairTwistedMeanCRT_conj_one {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) :
    pairTwistedMeanCRT (fun _ ↦ 1) b (fun i ↦ conj (b i)) h s = primeGraphMean b h s := by
  simp only [pairTwistedMeanCRT, primeGraphMean, pairShiftEdge_conj, one_mul]

theorem crtComplexMean_pairTwistedObservable {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) :
    crtComplexMean (fun p : PrimeGraphIndex H ↦ p.1) Finset.univ
      (pairTwistedObservable w b c h s) = pairTwistedMeanCRT w b c h s := by
  unfold crtComplexMean pairTwistedMeanCRT
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : p.1 ∈ s
  · simp only [pairTwistedObservable, hp, if_true, sum_pairTwistedCoordinate]
  · simp only [pairTwistedObservable, hp, if_false, Finset.sum_const_zero, smul_zero]

/-- **The bridge between the two halves of the argument.**  When the active primes lie in the
ambient CRT index set, the lower-bound side's mean is literally the Fourier side's
`pairTwistedPrimeGraphMean`.  Compare `Erdos67b.primeGraphMean_eq_sum`. -/
theorem pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H) :
    pairTwistedMeanCRT w b c h s = pairTwistedPrimeGraphMean w b c h s := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE H, if p ∈ s then
        (p : ℝ)⁻¹ • (w p * ∑ j : Fin H, pairShiftEdge b c (p * h) j) else 0 :=
      Finset.sum_coe_sort (Nat.primesLE H) _
    _ = ∑ p ∈ s, (p : ℝ)⁻¹ • (w p * ∑ j : Fin H, pairShiftEdge b c (p * h) j) := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hs hp, hp⟩⟩
    _ = _ := by
      simp only [pairTwistedPrimeGraphMean, Complex.real_smul, Complex.ofReal_inv,
        Complex.ofReal_natCast]
      exact Finset.sum_congr rfl fun p _ ↦ by ring

/-! ## Norm bounds, with the dependency's radius -/

theorem norm_pairTwistedSum_le {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hs : ∀ p ∈ s, δ * H ≤ p)
    (z : ZMod (primeGraphModulus H)) :
    ‖pairTwistedSum w b c h s z‖ ≤ (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  unfold pairTwistedSum crtComplexSum
  calc
    ‖∑ p, pairTwistedObservable w b c h s p _‖
        ≤ ∑ p, ‖pairTwistedObservable w b c h s p _‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, primeGraphRadius B δ :=
      Finset.sum_le_sum fun p _ ↦ norm_pairTwistedObservable_le w b c h s hB hδ hw hb hc hs p _
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]

theorem norm_pairTwistedMeanCRT_le {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hs : ∀ p ∈ s, δ * H ≤ p) :
    ‖pairTwistedMeanCRT w b c h s‖ ≤ (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  rw [← crtComplexMean_pairTwistedObservable]
  unfold crtComplexMean
  have hcoord (p : PrimeGraphIndex H) :
      ‖(p.1 : ℝ)⁻¹ • ∑ x, pairTwistedObservable w b c h s p x‖ ≤ primeGraphRadius B δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsum : ‖∑ x, pairTwistedObservable w b c h s p x‖ ≤
        (p.1 : ℝ) * primeGraphRadius B δ := by
      calc
        ‖∑ x, pairTwistedObservable w b c h s p x‖
            ≤ ∑ x, ‖pairTwistedObservable w b c h s p x‖ := norm_sum_le _ _
        _ ≤ ∑ _x : ZMod p.1, primeGraphRadius B δ := Finset.sum_le_sum
          (fun x _ ↦ norm_pairTwistedObservable_le w b c h s hB hδ hw hb hc hs p x)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹)
    have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.1)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using hmul
  exact (norm_sum_le _ _).trans (by
    have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hcoord p)
    simpa only [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul] using hsum)

/-! ## The Hoeffding tail, with the dependency's constants -/

/-- Port of `Erdos67b.primeGraph_tail_card_mul_exp_le`.  The twist and the second block are
invisible to the concentration engine: only the radius `primeGraphRadius B δ` enters. -/
theorem pairTwisted_tail_card_mul_exp_le {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ)
    (h : ℕ) (s : Finset ℕ) {B δ t r : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hw : ∀ p ∈ s, ‖w p‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ j, ‖c j‖ ≤ B)
    (hs : ∀ p ∈ s, δ * H ≤ p) (ht : 0 ≤ t)
    (hr : r + Real.log 4 ≤ t ^ 2 /
      (8 * (Nat.primeCounting H : ℝ) * (primeGraphRadius B δ) ^ 2)) :
    ((Finset.univ.filter fun z : ZMod (primeGraphModulus H) ↦
      t ≤ ‖pairTwistedSum w b c h s z - pairTwistedMeanCRT w b c h s‖).card : ℝ) *
        Real.exp r ≤ primeGraphModulus H := by
  classical
  let _ : NeZero (∏ p : PrimeGraphIndex H, p.1) :=
    ⟨show primeGraphModulus H ≠ 0 from NeZero.ne _⟩
  let R : ℝ≥0 := ⟨primeGraphRadius B δ, primeGraphRadius_nonneg hδ⟩
  have hbound : ∀ p : PrimeGraphIndex H, ∀ _ : p ∈ Finset.univ, ∀ z,
      ‖pairTwistedObservable w b c h s p z‖ ≤ (R : ℝ) := fun p _ z ↦
    norm_pairTwistedObservable_le w b c h s hB hδ hw hb hc hs p z
  have hsum : ((∑ _p : PrimeGraphIndex H, R ^ 2 : ℝ≥0) : ℝ) =
      (Nat.primeCounting H : ℝ) * primeGraphRadius B δ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]
    simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
    rfl
  have htail := crt_complex_tail_card_mul_exp_le
    (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H) Finset.univ
    (pairTwistedObservable w b c h s) (fun _ ↦ R) hbound ht
    (by rw [hsum]; simpa only [mul_assoc] using hr)
  rw [crtComplexMean_pairTwistedObservable] at htail
  exact htail

/-- Port of `Erdos67b.exists_primeGraph_exponential_tail`: uniform concentration for the
pair-twisted graph, with **the dependency's own constant** `c = ρ²/(64 R²)` and threshold scale. -/
theorem exists_pairTwisted_exponential_tail {B δ ρ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H : ℕ, H₁ ≤ H →
      ∀ (w : ℕ → ℂ) (b c' : Fin H → ℂ) (h : ℕ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ j, ‖b j‖ ≤ B) → (∀ j, ‖c' j‖ ≤ B) →
        (∀ p ∈ s, δ * H ≤ p) →
        ((Finset.univ.filter fun z : ZMod (primeGraphModulus H) ↦
          ρ * H / Real.log H ≤
            ‖pairTwistedSum w b c' h s z - pairTwistedMeanCRT w b c' h s‖).card : ℝ) *
          Real.exp (c * H / Real.log H) ≤ primeGraphModulus H := by
  let R := primeGraphRadius B δ
  have hR : 0 < R := primeGraphRadius_pos hB hδ
  let c : ℝ := ρ ^ 2 / (64 * R ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlarge := eventually_log_four_le_mul_nat_div_log hc
  have hevent : ∀ᶠ H : ℕ in atTop, 2 ≤ H ∧
      (Nat.primeCounting H : ℝ) ≤ 4 * ((H : ℝ) / Real.log H) ∧
      Real.log 4 ≤ c * ((H : ℝ) / Real.log H) := by
    filter_upwards [eventually_ge_atTop 2, eventually_primeCounting_le_four_mul_div_log, hlarge]
      with H hH hp hl
    exact ⟨hH, hp, hl⟩
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.mp hevent
  refine ⟨c, hc, max 2 H₁, le_max_left _ _, ?_⟩
  intro H hH w b c' h s hw hb hc' hs
  obtain ⟨hHtwo, hcount, hlarge'⟩ := hH₁ H ((le_max_right _ _).trans hH)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hT : 0 < (H : ℝ) / Real.log H := div_pos (by positivity) hlog
  have hN : (0 : ℝ) < Nat.primeCounting H := by
    exact_mod_cast (card_primeGraphIndex H ▸ primeGraphIndex_card_pos hHtwo)
  apply pairTwisted_tail_card_mul_exp_le w b c' h s hB.le hδ hw hb hc' hs (by positivity)
  have hbudget := primeGraph_tail_scalar_budget hN hT hR hρ hcount hlarge'
  simpa only [c, R, mul_div_assoc] using hbudget

end

end NormalNumbers.ElliottTwistedGraph
