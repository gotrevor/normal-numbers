import NormalNumbers.ElliottTwistedGraphCRT

/-!
# The prime-graph CRT layer over an *arbitrary* edge family

`NormalNumbers.ElliottTwistedGraphCRT` carries the CRT / concentration layer for the edge
`pairShiftEdge b c (p*h) j`.  Reading that file shows the edge enters in exactly two places:

* the coordinate norm bound needs `‖w p · edge‖ ≤ B²`;
* the mean needs the total `∑_j edge`.

Nothing else about the edge is used — not the shift, not the two blocks, not the block structure.
So the entire layer generalises, at no cost, to an arbitrary family

```
E : ℕ → Fin H → ℂ,      ‖E p j‖ ≤ B²
```

(`E p j` = the edge the prime `p` contributes at block position `j`).  This file is that
generalisation.  Its purpose is the `a`-dilated graph of the Elliott crux, whose edge
`dilatedPairShiftEdge` has a *dilated* block index and therefore is not of the proved shape.

**The prime-dependent residue shift is free.**  The dilated bookkeeping needs the residue condition
`z + (j+1) − d_p = 0` rather than `z + (j+1) = 0`, where `d_p = ⌊p c₁ / a⌋`.  That is the standard
condition evaluated at `z − d_p`, and `z ↦ z − d_p` is a bijection of `ZMod p`; so the shift never
has to enter the layer at all — it is applied to the residue variable by the *caller*.  This is why
genericity in the edge is the only generalisation needed.

The pure-shift case is recovered by `genCoordinate_pairShiftEdge` and friends, which identify the
generic objects with the proved `pairTwisted*` ones definitionally.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate NNReal
open Finset Filter

namespace NormalNumbers.ElliottGenericGraph

open Erdos67b
open NormalNumbers.ElliottTwistedGraph

noncomputable section

/-! ## Coordinate, observable, CRT sum, mean -/

/-- The contribution of one prime to the graph, as a function of the residue only, for an arbitrary
edge family.  Compare `NormalNumbers.ElliottTwistedGraph.pairTwistedCoordinate`. -/
def genCoordinate {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (p : ℕ) (z : ZMod p) : ℂ :=
  ∑ j : Fin H, if z + (j.1 + 1 : ℕ) = 0 then w p * E p j else 0

/-- Anchor: the proved coordinate is the pure-shift instance. -/
theorem genCoordinate_pairShiftEdge {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (p h : ℕ)
    (z : ZMod p) :
    genCoordinate w (fun p j ↦ pairShiftEdge b c (p * h) j) p z =
      pairTwistedCoordinate w b c p h z := rfl

theorem norm_genCoordinate_le {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (p : ℕ) [NeZero p]
    {B : ℝ} (hw : ‖w p‖ ≤ 1) (hE : ∀ j, ‖E p j‖ ≤ B ^ 2) (z : ZMod p) :
    ‖genCoordinate w E p z‖ ≤ (H / p + 1 : ℕ) * B ^ 2 := by
  classical
  let s : Finset (Fin H) := Finset.univ.filter fun j ↦ z + (j.1 + 1 : ℕ) = 0
  have hs : s = Finset.univ.filter (fun j : Fin H ↦ (j.1 : ZMod p) = -z - 1) := by
    ext j
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination h
  have hcard : s.card ≤ H / p + 1 := by rw [hs]; exact card_fin_residue_le H p (-z - 1)
  have hsum : genCoordinate w E p z = ∑ j ∈ s, w p * E p j := by
    simp only [genCoordinate, s, Finset.sum_filter]
  have hedge (j : Fin H) : ‖w p * E p j‖ ≤ B ^ 2 := by
    rw [norm_mul]
    calc ‖w p‖ * ‖E p j‖ ≤ 1 * ‖E p j‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ B ^ 2 := hE j
  rw [hsum]
  calc
    ‖∑ j ∈ s, w p * E p j‖ ≤ ∑ j ∈ s, ‖w p * E p j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, B ^ 2 := Finset.sum_le_sum (fun j _ ↦ hedge j)
    _ = s.card * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / p + 1 : ℕ) * B ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg B)

theorem norm_genCoordinate_le_of_scale {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (p : ℕ) [NeZero p]
    {B δ : ℝ} (_hB : 0 ≤ B) (hδ : 0 < δ) (hw : ‖w p‖ ≤ 1) (hE : ∀ j, ‖E p j‖ ≤ B ^ 2)
    (hp : δ * H ≤ p) (z : ZMod p) :
    ‖genCoordinate w E p z‖ ≤ primeGraphRadius B δ := by
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hdiv : (H / p : ℕ) ≤ (H : ℝ) / p := by
    apply (le_div_iff₀ hpr).mpr
    exact_mod_cast Nat.div_mul_le_self H p
  have hratio : (H : ℝ) / p ≤ 1 / δ := by
    apply (div_le_div_iff₀ hpr hδ).mpr
    nlinarith
  have hfloor : (H / p + 1 : ℕ) ≤ 1 / δ + (1 : ℝ) := by push_cast; linarith
  exact (norm_genCoordinate_le w E p hw hE z).trans
    (mul_le_mul_of_nonneg_right hfloor (sq_nonneg B))

/-- Each edge is counted for exactly one residue. -/
theorem sum_genCoordinate {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (p : ℕ) [NeZero p] :
    (∑ z : ZMod p, genCoordinate w E p z) = w p * ∑ j : Fin H, E p j := by
  classical
  simp only [genCoordinate, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcond (z : ZMod p) : z + (j.1 + 1 : ℕ) = 0 ↔ z = -((j.1 + 1 : ℕ) : ZMod p) :=
    eq_neg_iff_add_eq_zero.symm
  simp_rw [hcond]
  simp

/-- The observable of the CRT layer. -/
def genObservable {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    (p : PrimeGraphIndex H) (z : ZMod p.1) : ℂ :=
  if p.1 ∈ s then genCoordinate w E p.1 z else 0

theorem norm_genObservable_le {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hE : ∀ p, ∀ j, ‖E p j‖ ≤ B ^ 2) (hs : ∀ p ∈ s, δ * H ≤ p)
    (p : PrimeGraphIndex H) (z : ZMod p.1) :
    ‖genObservable w E s p z‖ ≤ primeGraphRadius B δ := by
  unfold genObservable
  split_ifs with hp
  · exact norm_genCoordinate_le_of_scale w E p.1 hB hδ (hw p.1 hp) (hE p.1) (hs p.1 hp) z
  · simpa only [norm_zero] using primeGraphRadius_nonneg hδ

/-- The CRT sum of the generic graph. -/
def genSum {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    (z : ZMod (primeGraphModulus H)) : ℂ :=
  crtComplexSum (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H)
    Finset.univ (genObservable w E s) z

/-- The CRT-indexed mean of the generic graph. -/
def genMeanCRT {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ) : ℂ :=
  ∑ p : PrimeGraphIndex H, if p.1 ∈ s then
    (p.1 : ℝ)⁻¹ • (w p.1 * ∑ j : Fin H, E p.1 j) else 0

/-- Anchor: the proved CRT sum is the pure-shift instance. -/
theorem genSum_pairShiftEdge {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (z : ZMod (primeGraphModulus H)) :
    genSum w (fun p j ↦ pairShiftEdge b c (p * h) j) s z = pairTwistedSum w b c h s z := rfl

/-- Anchor: the proved CRT mean is the pure-shift instance. -/
theorem genMeanCRT_pairShiftEdge {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) :
    genMeanCRT w (fun p j ↦ pairShiftEdge b c (p * h) j) s = pairTwistedMeanCRT w b c h s := rfl

theorem crtComplexMean_genObservable {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ) :
    crtComplexMean (fun p : PrimeGraphIndex H ↦ p.1) Finset.univ (genObservable w E s) =
      genMeanCRT w E s := by
  unfold crtComplexMean genMeanCRT
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : p.1 ∈ s
  · simp only [genObservable, hp, if_true, sum_genCoordinate]
  · simp only [genObservable, hp, if_false, Finset.sum_const_zero, smul_zero]

/-! ## Norm bounds -/

theorem norm_genSum_le {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hE : ∀ p, ∀ j, ‖E p j‖ ≤ B ^ 2) (hs : ∀ p ∈ s, δ * H ≤ p)
    (z : ZMod (primeGraphModulus H)) :
    ‖genSum w E s z‖ ≤ (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  unfold genSum crtComplexSum
  calc
    ‖∑ p, genObservable w E s p _‖ ≤ ∑ p, ‖genObservable w E s p _‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, primeGraphRadius B δ :=
      Finset.sum_le_sum fun p _ ↦ norm_genObservable_le w E s hB hδ hw hE hs p _
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]

theorem norm_genMeanCRT_le {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hE : ∀ p, ∀ j, ‖E p j‖ ≤ B ^ 2) (hs : ∀ p ∈ s, δ * H ≤ p) :
    ‖genMeanCRT w E s‖ ≤ (Nat.primeCounting H : ℝ) * primeGraphRadius B δ := by
  rw [← crtComplexMean_genObservable]
  unfold crtComplexMean
  have hcoord (p : PrimeGraphIndex H) :
      ‖(p.1 : ℝ)⁻¹ • ∑ x, genObservable w E s p x‖ ≤ primeGraphRadius B δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsum : ‖∑ x, genObservable w E s p x‖ ≤ (p.1 : ℝ) * primeGraphRadius B δ := by
      calc
        ‖∑ x, genObservable w E s p x‖ ≤ ∑ x, ‖genObservable w E s p x‖ := norm_sum_le _ _
        _ ≤ ∑ _x : ZMod p.1, primeGraphRadius B δ := Finset.sum_le_sum
          (fun x _ ↦ norm_genObservable_le w E s hB hδ hw hE hs p x)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹)
    have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.1)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using hmul
  exact (norm_sum_le _ _).trans (by
    have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hcoord p)
    simpa only [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul] using hsum)

/-! ## The Hoeffding tail -/

/-- Port of `NormalNumbers.ElliottTwistedGraph.pairTwisted_tail_card_mul_exp_le` to a generic edge
family: only the radius enters the concentration engine. -/
theorem gen_tail_card_mul_exp_le {H : ℕ} (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ)
    {B δ t r : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hw : ∀ p ∈ s, ‖w p‖ ≤ 1)
    (hE : ∀ p, ∀ j, ‖E p j‖ ≤ B ^ 2) (hs : ∀ p ∈ s, δ * H ≤ p) (ht : 0 ≤ t)
    (hr : r + Real.log 4 ≤ t ^ 2 /
      (8 * (Nat.primeCounting H : ℝ) * (primeGraphRadius B δ) ^ 2)) :
    ((Finset.univ.filter fun z : ZMod (primeGraphModulus H) ↦
      t ≤ ‖genSum w E s z - genMeanCRT w E s‖).card : ℝ) *
        Real.exp r ≤ primeGraphModulus H := by
  classical
  let _ : NeZero (∏ p : PrimeGraphIndex H, p.1) :=
    ⟨show primeGraphModulus H ≠ 0 from NeZero.ne _⟩
  let R : ℝ≥0 := ⟨primeGraphRadius B δ, primeGraphRadius_nonneg hδ⟩
  have hbound : ∀ p : PrimeGraphIndex H, ∀ _ : p ∈ Finset.univ, ∀ z,
      ‖genObservable w E s p z‖ ≤ (R : ℝ) := fun p _ z ↦
    norm_genObservable_le w E s hB hδ hw hE hs p z
  have hsum : ((∑ _p : PrimeGraphIndex H, R ^ 2 : ℝ≥0) : ℝ) =
      (Nat.primeCounting H : ℝ) * primeGraphRadius B δ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]
    simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
    rfl
  have htail := crt_complex_tail_card_mul_exp_le
    (fun p : PrimeGraphIndex H ↦ p.1) (primeGraphModuli_pairwise H) Finset.univ
    (genObservable w E s) (fun _ ↦ R) hbound ht
    (by rw [hsum]; simpa only [mul_assoc] using hr)
  rw [crtComplexMean_genObservable] at htail
  exact htail

/-- Uniform concentration for the generic graph, with the dependency's own constant
`c = ρ²/(64 R²)`.  Port of
`NormalNumbers.ElliottTwistedGraph.exists_pairTwisted_exponential_tail`. -/
theorem exists_gen_exponential_tail {B δ ρ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H : ℕ, H₁ ≤ H →
      ∀ (w : ℕ → ℂ) (E : ℕ → Fin H → ℂ) (s : Finset ℕ),
        (∀ p ∈ s, ‖w p‖ ≤ 1) → (∀ p, ∀ j, ‖E p j‖ ≤ B ^ 2) → (∀ p ∈ s, δ * H ≤ p) →
        ((Finset.univ.filter fun z : ZMod (primeGraphModulus H) ↦
          ρ * H / Real.log H ≤ ‖genSum w E s z - genMeanCRT w E s‖).card : ℝ) *
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
  intro H hH w E s hw hE hs
  obtain ⟨hHtwo, hcount, hlarge'⟩ := hH₁ H ((le_max_right _ _).trans hH)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hT : 0 < (H : ℝ) / Real.log H := div_pos (by positivity) hlog
  have hN : (0 : ℝ) < Nat.primeCounting H := by
    exact_mod_cast (card_primeGraphIndex H ▸ primeGraphIndex_card_pos hHtwo)
  apply gen_tail_card_mul_exp_le w E s hB.le hδ hw hE hs (by positivity)
  have hbudget := primeGraph_tail_scalar_budget hN hT hR hρ hcount hlarge'
  simpa only [c, R, mul_div_assoc] using hbudget

end

end NormalNumbers.ElliottGenericGraph

#print axioms NormalNumbers.ElliottGenericGraph.exists_gen_exponential_tail
#print axioms NormalNumbers.ElliottGenericGraph.genSum_pairShiftEdge
